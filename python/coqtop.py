# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Rocq interface with functions to send commands and parse responses."""

import datetime
import io
import logging
import os
import signal
import subprocess
import threading
import time
from concurrent import futures
from contextlib import contextmanager
from queue import Empty, Queue
from tempfile import NamedTemporaryFile
from typing import (
    IO,
    TYPE_CHECKING,
    Any,
    Callable,
    Generator,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Tuple,
    Union,
)

from xmlInterface import (
    STDERR_ERR,
    TIMEOUT_ERR,
    Err,
    FindCoqtopError,
    GoalMode,
    Goals,
    Ok,
    Result,
    XMLInterface,
    XMLInterfaceBase,
    partition_warnings,
    prettyxml,
)

if TYPE_CHECKING:
    from typing_extensions import TypedDict

    BytesQueue = Queue[bytes]
    CoqtopProcess = subprocess.Popen[bytes]
    DuneProcess = subprocess.Popen[bytes]
    VersionInfo = TypedDict(
        "VersionInfo",
        {
            "version": Tuple[int, int, int],
            "str_version": str,
            "latest": Optional[str],
        },
    )
else:
    BytesQueue = Queue
    CoqtopProcess = subprocess.Popen
    DuneProcess = subprocess.Popen
    VersionInfo = Mapping[str, Any]


def join_not_empty(msgs: Iterable[str], joiner: str = "\n\n") -> str:
    """Concatenate non-empty messages."""
    return joiner.join(msg for msg in msgs if msg != "")


class CoqtopError(Exception):
    """An exception for when Rocq stops unexpectedly."""


class DuneError(Exception):
    """An exception for when dune could not run."""


class Coqtop:
    """Provide an interface to the background Rocq process."""

    def __init__(
        self,
        add_info_callback: Optional[Callable[[str], None]] = None,
    ) -> None:
        """Initialize Rocq state.

        coqtop - The Rocq process
        states - A stack of previous state_ids (grows to the right)
        state_id - The current (tip) state_id
        root_state - The starting state_id
        out_q - A thread-safe queue of data read from Rocq
        err_q - A thread-safe queue of error messages read from Rocq
        xml - The XML interface for the given version
        """
        self.coqtop: Optional[CoqtopProcess] = None
        self.xml: Optional[XMLInterfaceBase] = None
        self.states: List[int] = []
        self.state_id = -1
        self.root_state = -1
        self.out_q: BytesQueue = Queue()
        self.err_q: BytesQueue = Queue()
        self.stopping = False
        self.add_info_callback: Optional[Callable[[str], None]] = add_info_callback
        self.dune: Optional[DuneProcess] = None

        # Debugging
        self.log: Optional[IO[str]] = None
        self.handler: logging.Handler = logging.NullHandler()
        self.logger = logging.getLogger(str(id(self)))
        self.logger.addHandler(self.handler)
        self.logger.setLevel(logging.INFO)

    def is_in_valid_dune_project(self, filename: str) -> bool:
        """Query dune to assert that the given file is in a correctly configured dune project."""
        if self.xml is not None and self.xml.valid_module(filename):
            # dune needs relative paths to work properly
            filepath = os.path.dirname(filename)

            # check if the file is located in a dune project
            self.logger.debug(("query dune in ", filepath))
            dune_check = ("dune", "describe", "workspace")
            try:
                subprocess.run(
                    dune_check,
                    capture_output=True,
                    cwd=filepath,
                    check=True,
                )
            except subprocess.CalledProcessError as e:
                self.logger.debug("file is not in correctly configured dune project")
                raise DuneError(e.stderr.decode("utf-8")) from e
            self.logger.debug("found dune project")
            return True
        return False

    def can_run_dune_toplevel(self, toplevel: str, filename: str) -> bool:
        """Check whether we can run the given dune toplevel (coq or rocq) on the given filename.
        Assumes that it has already been determined that this is a valid dune project.
        """
        basename = os.path.basename(filename)
        filepath = os.path.dirname(filename)
        # run echo as the toplevel. We just care about checking whether `dune toplevel top` runs without errors.
        dune_check = (
            "dune",
            toplevel,
            "top",
            "--no-build",
            "--toplevel",
            "echo",
            basename,
        )
        try:
            subprocess.run(
                dune_check,
                capture_output=True,
                cwd=filepath,
                check=True,
            )
        except subprocess.CalledProcessError:
            return False
        return True

    def get_dune_toplevel(self, filename: str) -> str:
        """Determine the correct dune toplevel (coq or rocq) for the dune project the given filename is located in,
        which depends on whether the dune project is configured for the `coq` language or the `rocq` language.
        Assumes that the file is part of a correctly configured dune project."""
        if self.can_run_dune_toplevel("rocq", filename):
            return "rocq"
        return "coq"

    def get_dune_args(self, filename: str, dune_compile_deps: bool) -> List[str]:
        """Get the arguments to pass to the Rocq process from dune.
        Assumes that the file is part of a correctly configured dune project."""
        # dune needs relative paths to work properly
        basename = os.path.basename(filename)
        filepath = os.path.dirname(filename)

        dune_toplevel = self.get_dune_toplevel(filename)
        dune_launch = (
            "dune",
            dune_toplevel,
            "top",
            basename,
            "--toplevel",
            "echo",
            "--display=short",
            "--no-build" if not dune_compile_deps else "",
        )
        self.logger.debug(dune_launch)

        with subprocess.Popen(
            dune_launch,
            cwd=filepath,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        ) as dune_proc:
            # read stderr output continuously using a separate thread
            err_queue: BytesQueue = Queue()
            self.dune = dune_proc
            threading.Thread(
                target=self.capture_dune_out,
                args=(err_queue, dune_proc.stderr),
                daemon=True,
            ).start()

            # wait for dune to terminate
            dune_proc.wait()
            self.dune = None

            if dune_proc.returncode != 0:
                self.logger.debug("dune error")
                # get the error output
                err_msg = b""
                while not err_queue.empty():
                    err_msg += err_queue.get_nowait()
                decoded_err_msg = err_msg.decode("utf-8")
                raise DuneError(decoded_err_msg)

            # read the dune result from stdout
            self.logger.debug("dune result")
            assert dune_proc.stdout is not None
            out = io.TextIOWrapper(dune_proc.stdout, encoding="utf-8")
            args = out.read()
            self.logger.debug(args)
            return args.split()

    def capture_dune_out(self, buffer: BytesQueue, stream: IO[bytes]) -> None:
        """Continually read data from 'stream' into 'buffer' and add it to the info panel."""
        data = b""
        while not self.stopping:
            try:
                r = stream.read(0x10000)
                buffer.put(r)
                data += r
            except (AttributeError, OSError, ValueError):
                # dune stopped
                return
            try:
                decoded = data.decode("utf-8").strip()
                data = b""
                if self.add_info_callback is not None:
                    self.add_info_callback(decoded)
            except (UnicodeDecodeError, AttributeError):
                # not complete yet
                pass

    def find_coq(
        self,
        coq_path: Optional[str],
        coq_prog: Optional[str],
    ) -> Union[VersionInfo, str]:
        """Find the Rocq executable."""
        assert self.coqtop is None
        assert self.xml is None

        try:
            self.logger.debug("locating rocq")
            self.xml, latest = XMLInterface(coq_path, coq_prog)

            return {
                "version": self.xml.version,
                "str_version": self.xml.str_version,
                "latest": latest,
            }
        except (OSError, FindCoqtopError) as e:
            # Failed to find Rocq
            self.xml = None
            return str(e)

    # Rocq Interface #
    def start(
        self,
        filename: str,
        coqproject_args: List[str],
        use_dune: bool,
        dune_compile_deps: bool,
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[Optional[str], str]:
        """Launch the Rocq process."""
        assert self.coqtop is None
        assert self.xml is not None

        try:
            self.logger.debug("start")

            args = coqproject_args
            if use_dune and self.is_in_valid_dune_project(filename):
                # Add user-provided args last so they take precedence.
                args = self.get_dune_args(filename, dune_compile_deps) + args

            launch = self.xml.launch(filename, args)
            self.logger.debug(launch)
            self.coqtop = subprocess.Popen(  # pylint: disable=consider-using-with
                launch,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                bufsize=0,
            )

            # Ensure that Rocq spawned correctly
            try:
                self.coqtop.wait(timeout=0.1)
                assert self.coqtop.stderr is not None
                return self.coqtop.stderr.read().decode("utf8"), ""
            except subprocess.TimeoutExpired:
                pass

            # Spawn threads to monitor Rocq's stdout and stderr
            for buf, stream in (
                (self.out_q, self.coqtop.stdout),
                (self.err_q, self.coqtop.stderr),
            ):
                threading.Thread(
                    target=self.capture_out,
                    args=(buf, stream),
                    daemon=True,
                ).start()
            threading.Thread(target=self.capture_dead, daemon=True).start()

            # Initialize Rocq
            response, err = self.call(
                self.xml.init(),
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )

            if isinstance(response, Err):
                return response.msg, err

            self.root_state = response.val
            self.state_id = response.val

            return (None, err)
        except (OSError, DuneError, FindCoqtopError) as e:
            # Failed to launch Rocq
            self.coqtop = None
            return str(e), ""

    def stop(self) -> None:
        """End the Rocq process."""
        if self.dune is not None:
            self.interrupt()

        if self.coqtop is not None:
            self.logger.debug("stop")
            self.stopping = True

            try:
                # Try to terminate Rocq cleanly
                # TODO: use Quit call
                self.coqtop.terminate()
                self.coqtop.communicate()
            except (OSError, ValueError, AttributeError):
                try:
                    # Force Rocq to stop
                    self.coqtop.kill()
                except (OSError, AttributeError):
                    pass

            self.coqtop = None

        # Close debugging log
        try:
            self.handler.flush()
            self.handler.close()
        except ValueError:
            pass
        if self.log is not None and not self.log.closed:
            self.log.close()

    def advance(
        self,
        cmd: str,
        in_script: bool,
        encoding: str = "utf-8",
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Advance Rocq by sending 'cmd'."""
        assert self.xml is not None
        self.logger.debug("advance: %s", cmd)
        response, err1 = self.call(
            self.xml.add(cmd, self.state_id, encoding=encoding),
            timeout=timeout,
            stderr_is_warning=stderr_is_warning,
        )

        if isinstance(response, Err):
            return False, response.msg, response.loc, err1

        # In addition to sending 'cmd', also check status in order to force it
        # to be evaluated
        status, err2 = self.call(
            self.xml.status(encoding=encoding),
            timeout=timeout,
            stderr_is_warning=stderr_is_warning,
        )

        # Combine messages
        msgs = join_not_empty((response.msg, response.val["res_msg"], status.msg))
        err = err1 + err2

        if isinstance(status, Err):
            # Reset state id to before the error
            self.call(
                self.xml.edit_at(self.state_id, 1),
                stderr_is_warning=stderr_is_warning,
            )
            return False, msgs, status.loc, err

        # Only add the state id to the rewind list if the command is actually
        # in the file so Rocq and Coqtail stay in sync.
        if in_script:
            self.states.append(self.state_id)
        self.state_id = response.val["state_id"]

        return True, msgs, None, err

    def rewind(
        self,
        steps: int = 1,
        stderr_is_warning: bool = False,
    ) -> Tuple[bool, str, Optional[int], str]:
        """Go back 'steps' states."""
        assert self.xml is not None
        self.logger.debug("rewind: %d", steps)
        if steps > len(self.states):
            self.state_id = self.root_state
            self.states = []
            steps = len(self.states)
        else:
            # In 8.4 query and option commands will be recorded with
            # state_id = -1. Need to count them and reduce number of steps to
            # rewind so Rocq doesn't go too far back
            fake_steps = sum(s == -1 for s in self.states[-steps:])
            if self.states[-steps] != -1:
                self.state_id = self.states[-steps]
            else:
                self.state_id = 0
            self.states = self.states[:-steps]
            steps -= fake_steps

        response, err = self.call(
            self.xml.edit_at(self.state_id, steps),
            stderr_is_warning=stderr_is_warning,
        )
        return (
            isinstance(response, Ok),
            response.msg,
            response.val if isinstance(response, Ok) else None,
            err,
        )

    def query(
        self,
        cmd: str,
        in_script: bool,
        encoding: str = "utf-8",
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Query Rocq with 'cmd'."""
        assert self.xml is not None
        self.logger.debug("query: %s", cmd)
        response, err = self.call(
            self.xml.query(cmd, self.state_id, encoding=encoding),
            timeout=timeout,
            stderr_is_warning=stderr_is_warning,
        )

        if isinstance(response, Ok) and in_script:
            # If the query was called from within the script we need to record
            # the state id so rewinding will work properly. Since 8.4 uses
            # number of steps rather than state ids, record '-1' to indicate
            # that no rewind should actually be done
            if self.xml.version >= (8, 5, 0):
                self.states.append(self.state_id)
            else:
                self.states.append(-1)

        return (
            isinstance(response, Ok),
            response.msg,
            None if isinstance(response, Ok) else response.loc,
            err,
        )

    def goals(
        self,
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[bool, str, Optional[Goals], str]:
        """Get the current set of hypotheses and goals."""
        assert self.xml is not None
        self.logger.debug("goals")

        # Use Subgoals if available, otherwise fall back to Goal
        if hasattr(self.xml, "subgoal"):
            return self.subgoals(timeout=timeout, stderr_is_warning=stderr_is_warning)

        response, err = self.call(
            self.xml.goal(),
            timeout=timeout,
            stderr_is_warning=stderr_is_warning,
        )

        return (
            isinstance(response, Ok),
            response.msg,
            response.val if isinstance(response, Ok) else None,
            err,
        )

    def subgoals(
        self,
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[bool, str, Optional[Goals], str]:
        """Get the current set of hypotheses and goals."""
        assert self.xml is not None

        # Get the current proof state, but only include focused
        # goals in the goal list.
        response_main, err_main = self.call(
            self.xml.subgoal(  # type: ignore
                GoalMode.FULL,
                fg=True,
                bg=False,
                shelved=False,
                given_up=False,
            ),
            timeout=timeout,
            stderr_is_warning=stderr_is_warning,
        )

        if isinstance(response_main, Err):
            return (False, response_main.msg, None, err_main)

        # If success but we didn't get a CoqGoals, then there's
        # no proof in progress. We can return early.
        if response_main.val is None:
            # If the request was success but it returned None, then
            # we're not in a proof. No need to run the second query.
            return (True, response_main.msg, None, err_main)

        # NOTE: Subgoals ignores `gf_flag = "short"` if proof diffs are
        # enabled.
        # See: https://github.com/coq/coq/issues/16564
        with self.suppress_diffs(stderr_is_warning=stderr_is_warning):
            # Get the short version of other goals (no hypotheses)
            response_extra, err_extra = self.call(
                self.xml.subgoal(  # type: ignore
                    GoalMode.SHORT,
                    fg=False,
                    bg=True,
                    shelved=True,
                    given_up=True,
                ),
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )

        # Combine messages
        msgs = join_not_empty(response_main.msg, response_extra.msg)
        errs = err_main + err_extra

        if isinstance(response_extra, Err):
            return (False, msgs, None, errs)

        assert response_extra.val is not None, "proof state changed unexpectedly?"

        # Merge goals
        goals = Goals(
            response_main.val.fg,
            response_extra.val.bg,
            response_extra.val.shelved,
            response_extra.val.given_up,
        )

        return (True, msgs, goals, errs)

    def do_option(
        self,
        cmd: str,
        in_script: bool,
        encoding: str = "utf-8",
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Set or get an option's value."""
        assert self.xml is not None
        self.logger.debug("do_option: %s", cmd)
        vals, opt = self.xml.parse_option(cmd)

        # See: https://github.com/coq/coq/blob/6c18649e6c77fdae0dd92934929640dc1243541a/ide/coqide/idetop.ml#L57
        scoldable = {
            "Printing Implicit",
            "Printing Coercions",
            "Printing Matching",
            "Printing Synth",
            "Printing Notations",
            "Printing Parentheses",
            "Printing All",
            "Printing Records",
            "Printing Existential Instances",
            "Printing Universes",
            "Printing Unfocused",
            "Printing Goal Names",
            "Diffs",
        }

        # Since Rocq split parsing and execution of vernacular commands,
        # certain options, such as `Default Proof Mode` can't be set with
        # SetOptions. So to make things easier, just use `Add` instead of
        # `SetOptions` for all but a few options that Rocq will otherwise scold
        # you about not setting from the IDE menu.
        # See: https://github.com/coq/coq/blob/40373610d6024510125405f53293809bc850b3af/library/goptions.ml#L437
        if vals is not None and opt not in scoldable:
            return self.advance(
                cmd,
                in_script,
                encoding=encoding,
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )

        option_ok = True
        if vals is None:
            response, err = self.call(
                self.xml.get_options(encoding=encoding),
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )

            if isinstance(response, Ok):
                try:
                    ret = next(
                        (
                            f"{desc}: {val}"
                            for name, desc, val in response.val
                            if name == opt
                        )
                    )
                except StopIteration:
                    ret = "Invalid option name"
                    option_ok = False
        else:
            errs = []
            for val in vals:
                response, err = self.call(
                    self.xml.set_options(opt, val, encoding=encoding),
                    timeout=timeout,
                    stderr_is_warning=stderr_is_warning,
                )
                ret = response.msg
                # `set_options()` returns nothing on success
                option_ok = option_ok and ret == ""
                errs.append(err)
                if isinstance(response, Ok):
                    break
            err = "".join(errs)

        if in_script and isinstance(response, Ok) and option_ok:
            # Hack to associate setting an option with a new state id by
            # executing a noop so it works correctly with rewinding
            success, _, _, _ = self.advance(
                self.xml.noop,
                in_script,
                encoding=encoding,
                stderr_is_warning=stderr_is_warning,
            )
            assert success
        elif in_script and not option_ok:
            # Fall back to using `advance()` in case the best-effort attempt at
            # using `SetOptions` only failed because the option's value doesn't
            # follow the usual pattern (e.g., `Firstorder Solver`).
            # NOTE: This shouldn't be possible anymore since only options that
            # are known to work with `SetOptions` can reach here, but I'm
            # leaving it just in case.
            self.logger.warning("Failed to handle %s with Get/SetOptions", cmd)
            return self.advance(
                cmd,
                in_script,
                encoding=encoding,
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )

        return (
            isinstance(response, Ok),
            ret if isinstance(response, Ok) else response.msg,
            None if isinstance(response, Ok) else response.loc,
            err,
        )

    def dispatch(
        self,
        cmd: str,
        cmd_no_comment: Optional[str] = None,
        in_script: bool = True,
        encoding: str = "utf-8",
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Decide whether 'cmd' is setting/getting an option, a query, or a
        regular command.
        """
        # pylint: disable=no-else-return
        assert self.xml is not None
        if cmd_no_comment is None:
            cmd_no_comment = cmd

        if self.xml.is_option(cmd_no_comment):
            return self.do_option(
                cmd_no_comment,
                in_script,
                encoding=encoding,
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )
        elif self.xml.is_query(cmd_no_comment):
            return self.query(
                cmd,
                in_script,
                encoding=encoding,
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )
        elif in_script:
            return self.advance(
                cmd,
                in_script,
                encoding=encoding,
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )
        else:
            return True, "Command only allowed in script.", None, ""

    @contextmanager
    def suppress_diffs(
        self,
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Generator[None, None, None]:
        """Temporarily disable proof diffs."""
        # Check if diffs are enabled
        expect_prefix = "Diffs: Some(val="
        ok, response, _, err = self.do_option(
            "Test Diffs",
            in_script=False,
            timeout=timeout,
            stderr_is_warning=stderr_is_warning,
        )
        if ok and response.startswith(expect_prefix):
            # TODO: Make a cleaner way of reading an option
            diffs = response[len(expect_prefix) : -1].strip("'")
        else:
            # Failures are just logged because there's not much else that can
            # be done from here.
            self.logger.warning("Failed to read Diffs option: %s", err)
            diffs = "off"

        # Disable if necessary
        if diffs != "off":
            ok, _, _, err = self.do_option(
                'Set Diffs "off"',
                in_script=False,
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )
            if not ok:
                self.logger.warning("Failed to disable Diffs option: %s", err)

        yield None

        # Re-enable if necessary
        if diffs != "off":
            ok, _, _, err = self.do_option(
                f'Set Diffs "{diffs}"',
                in_script=False,
                timeout=timeout,
                stderr_is_warning=stderr_is_warning,
            )
            if not ok:
                self.logger.warning("Failed to re-enable Diffs option: %s", err)

    # Interacting with Rocq #
    def call(
        self,
        cmdtype_msg: Tuple[str, Optional[bytes]],
        timeout: Optional[int] = None,
        stderr_is_warning: bool = False,
    ) -> Tuple[Result, str]:
        """Send 'msg' to the Rocq process and wait for the response."""
        assert self.xml is not None
        # Check if Rocq has stopped
        if not self.running():
            raise CoqtopError("Rocq is not running.")

        # Throw away any unread messages
        self.empty_out()

        # 'msg' can be None if a command does not exist for a particular
        # version and is being faked.
        # NOTE: It is important that the '_standardize' function being called
        # does not depend on the value it is passed since it is None
        cmd, msg = cmdtype_msg
        if msg is None:
            return self.xml.standardize(cmd, Ok(None)), self.collect_err()

        # Don't bother doing prettyxml if debugging isn't on
        if self.logger.isEnabledFor(logging.DEBUG):
            self.logger.debug(prettyxml(msg))
        self.send_cmd(msg)

        with futures.ThreadPoolExecutor(1) as pool:
            try:
                timeout = None if timeout == 0 else timeout
                response, err = pool.submit(
                    lambda: self.get_answer(stderr_is_warning)
                ).result(timeout)
            except futures.TimeoutError:
                self.interrupt()
                response, err = TIMEOUT_ERR, ""

        return self.xml.standardize(cmd, response), err

    def get_answer(self, stderr_is_warning: bool = False) -> Tuple[Result, str]:
        """Read from 'out_q' and wait until a full response is received."""
        assert self.xml is not None
        data = []
        poll_sec = 1

        while True:
            # Abort if an error is printed to stderr, but ignore warnings.
            # NOTE: If `warnings_wf` is False because this version of Rocq does
            # not follow the pattern expected by `partition_warnings` then
            # pretend everything is a warning and hope for the best.
            # The `stderr_is_warning` option also causes any any message
            # on stderr to be treated as a warning.
            err = self.collect_err()
            if (
                not stderr_is_warning
                and self.xml.warnings_wf
                and partition_warnings(err)[1] != ""
            ):
                return STDERR_ERR, err

            try:
                data.append(self.out_q.get(timeout=poll_sec))
            except Empty:
                continue
            xml = b"".join(data)
            if not self.xml.worth_parsing(xml):
                continue
            response = self.xml.raw_response(xml)

            if response is None:
                continue

            # Don't bother doing prettyxml if debugging isn't on
            if self.logger.isEnabledFor(logging.DEBUG):
                self.logger.debug(prettyxml(b"<response>" + xml + b"</response>"))
            return response, err

    @staticmethod
    def drain_queue(q: BytesQueue) -> Iterator[bytes]:
        """Yield data from 'q' until it is empty."""
        while not q.empty():
            try:
                yield q.get_nowait()
            except Empty:
                return

    def empty_out(self) -> None:
        """Pop data until 'out_q' is empty."""
        for _ in Coqtop.drain_queue(self.out_q):
            pass

    def collect_err(self) -> str:
        """Pop and concatenate everything in 'err_q'."""
        err = b"".join(Coqtop.drain_queue(self.err_q)).decode("utf-8")
        if err != "":
            self.logger.debug(err)
        return err

    def capture_out(self, buffer: BytesQueue, stream: IO[bytes]) -> None:
        """Continually read data from 'stream' into 'buffer'."""
        while not self.stopping:
            try:
                buffer.put(stream.read(0x10000))
            except (AttributeError, OSError, ValueError):
                # Rocq died
                return

    def capture_dead(self) -> None:
        """Continually check if Rocq has died."""
        while self.running():
            time.sleep(1)
        self.stop()

    def send_cmd(self, cmd: bytes) -> None:
        """Write to Rocq's stdin."""
        if self.coqtop is None:
            raise CoqtopError("coqtop must not be None in send_cmd()")
        if self.coqtop.stdin is None:
            raise CoqtopError("coqtop stdin must not be None in send_cmd()")

        self.coqtop.stdin.write(cmd)
        self.coqtop.stdin.flush()

    def interrupt(self) -> None:
        """Send a SIGINT signal to Rocq or a SIGTERM signal to dune."""
        if self.dune is not None:
            # if dune is running, stop it
            self.dune.send_signal(signal.SIGTERM)
            self.dune.wait()
            self.dune = None
        elif self.coqtop is not None:
            self.coqtop.send_signal(signal.SIGINT)

    # Current State #
    def running(self) -> bool:
        """Check if Rocq has already been started."""
        return self.coqtop is not None and self.coqtop.poll() is None

    # Debugging #
    def toggle_debug(self) -> Optional[str]:
        """Enable or disable logging of debug messages."""
        self.logger.removeHandler(self.handler)
        self.handler.flush()
        self.handler.close()

        if self.log is None:
            # Create unique log file
            fmt = logging.Formatter("%(asctime)s: %(message)s")
            self.log = NamedTemporaryFile(  # pylint: disable=consider-using-with
                mode="w",
                encoding="utf-8",
                prefix=f"coqtop_{datetime.datetime.now().strftime('%y%m%d_%H%M%S')}_",
                delete=False,
            )
            self.handler = logging.StreamHandler(self.log)
            self.handler.setFormatter(fmt)
            self.logger.addHandler(self.handler)
            self.logger.setLevel(logging.DEBUG)
        else:
            # Clean up old logging
            self.log.close()

            # Set to null logging
            self.log = None
            self.handler = logging.NullHandler()
            self.logger.addHandler(self.handler)
            self.logger.setLevel(logging.CRITICAL)
        return self.log.name if self.log is not None else None
