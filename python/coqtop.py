# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Coqtop interface with functions to send commands and parse responses."""

import datetime
import logging
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
    TIMEOUT_ERR,
    UNEXPECTED_ERR,
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
    VersionInfo = Mapping[str, Any]


def join_not_empty(msgs: Iterable[str], joiner: str = "\n\n") -> str:
    """Concatenate non-empty messages."""
    return joiner.join(msg for msg in msgs if msg != "")


class CoqtopError(Exception):
    """An exception for when Coqtop stops unexpectedly."""


class Coqtop:
    """Provide an interface to the background Coqtop process."""

    def __init__(self) -> None:
        """Initialize Coqtop state.

        coqtop - The Coqtop process
        states - A stack of previous state_ids (grows to the right)
        state_id - The current (tip) state_id
        root_state - The starting state_id
        out_q - A thread-safe queue of data read from Coqtop
        err_q - A thread-safe queue of error messages read from Coqtop
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

        # Debugging
        self.log: Optional[IO[str]] = None
        self.handler: logging.Handler = logging.NullHandler()
        self.logger = logging.getLogger(str(id(self)))
        self.logger.addHandler(self.handler)
        self.logger.setLevel(logging.INFO)

    # Coqtop Interface #
    def start(
        self,
        coq_path: Optional[str],
        coq_prog: Optional[str],
        filename: str,
        args: Iterable[str],
        timeout: Optional[int] = None,
    ) -> Tuple[Union[VersionInfo, str], str]:
        """Launch the Coqtop process."""
        assert self.coqtop is None

        try:
            self.logger.debug("start")
            self.xml, latest = XMLInterface(coq_path, coq_prog)
            launch = self.xml.launch(filename, args)
            self.logger.debug(launch)
            self.coqtop = subprocess.Popen(  # pylint: disable=consider-using-with
                launch,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                bufsize=0,
            )

            # Ensure that Coqtop spawned correctly
            try:
                self.coqtop.wait(timeout=0.1)
                assert self.coqtop.stderr is not None
                return self.coqtop.stderr.read().decode("utf8"), ""
            except subprocess.TimeoutExpired:
                pass

            # Spawn threads to monitor Coqtop's stdout and stderr
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

            # Initialize Coqtop
            response, err = self.call(self.xml.init(), timeout=timeout)

            if isinstance(response, Err):
                return response.msg, err

            self.root_state = response.val
            self.state_id = response.val

            return (
                {
                    "version": self.xml.version,
                    "str_version": self.xml.str_version,
                    "latest": latest,
                },
                err,
            )
        except (OSError, FindCoqtopError) as e:
            # Failed to launch or find Coqtop
            self.coqtop = None
            return str(e), ""

    def stop(self) -> None:
        """End the Coqtop process."""
        if self.coqtop is not None:
            self.logger.debug("stop")
            self.stopping = True

            try:
                # Try to terminate Coqtop cleanly
                # TODO: use Quit call
                self.coqtop.terminate()
                self.coqtop.communicate()
            except (OSError, ValueError, AttributeError):
                try:
                    # Force Coqtop to stop
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
        encoding: str = "utf-8",
        timeout: Optional[int] = None,
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Advance Coqtop by sending 'cmd'."""
        assert self.xml is not None
        self.logger.debug("advance: %s", cmd)
        response, err1 = self.call(
            self.xml.add(cmd, self.state_id, encoding=encoding),
            timeout=timeout,
        )

        if isinstance(response, Err):
            return False, response.msg, response.loc, err1

        # In addition to sending 'cmd', also check status in order to force it
        # to be evaluated
        status, err2 = self.call(self.xml.status(encoding=encoding), timeout=timeout)

        # Combine messages
        msgs = join_not_empty((response.msg, response.val["res_msg"], status.msg))
        err = err1 + err2

        if isinstance(status, Err):
            # Reset state id to before the error
            self.call(self.xml.edit_at(self.state_id, 1))
            return False, msgs, status.loc, err

        self.states.append(self.state_id)
        self.state_id = response.val["state_id"]

        return True, msgs, None, err

    def rewind(self, steps: int = 1) -> Tuple[bool, str, Optional[int], str]:
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
            # rewind so Coqtop doesn't go too far back
            fake_steps = sum(s == -1 for s in self.states[-steps:])
            if self.states[-steps] != -1:
                self.state_id = self.states[-steps]
            else:
                self.state_id = 0
            self.states = self.states[:-steps]
            steps -= fake_steps

        response, err = self.call(self.xml.edit_at(self.state_id, steps))
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
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Query Coqtop with 'cmd'."""
        assert self.xml is not None
        self.logger.debug("query: %s", cmd)
        response, err = self.call(
            self.xml.query(cmd, self.state_id, encoding=encoding),
            timeout=timeout,
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
    ) -> Tuple[bool, str, Optional[Goals], str]:
        """Get the current set of hypotheses and goals."""
        assert self.xml is not None
        self.logger.debug("goals")

        # Use Subgoals if available, otherwise fall back to Goal
        if hasattr(self.xml, "subgoal"):
            return self.subgoals(timeout=timeout)

        response, err = self.call(self.xml.goal(), timeout=timeout)

        return (
            isinstance(response, Ok),
            response.msg,
            response.val if isinstance(response, Ok) else None,
            err,
        )

    def subgoals(
        self,
        timeout: Optional[int] = None,
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
        with self.suppress_diffs():
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
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Set or get an option's value."""
        assert self.xml is not None
        self.logger.debug("do_option: %s", cmd)
        vals, opt = self.xml.parse_option(cmd)
        option_ok = True

        if vals is None:
            response, err = self.call(
                self.xml.get_options(encoding=encoding),
                timeout=timeout,
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
            success, _, _, _ = self.advance(self.xml.noop, encoding)
            assert success
        elif in_script and not option_ok:
            # Fall back to using `advance()` in case the best-effort attempt at
            # using `SetOptions` only failed because the option's value doesn't
            # follow the usual pattern (e.g., `Firstorder Solver`)
            self.logger.warning("Failed to handle %s with Get/SetOptions", cmd)
            return self.advance(cmd, encoding, timeout)

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
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Decide whether 'cmd' is setting/getting an option, a query, or a
        regular command.
        """
        # pylint: disable=no-else-return
        assert self.xml is not None
        if cmd_no_comment is None:
            cmd_no_comment = cmd

        if self.xml.is_option(cmd_no_comment):
            return self.do_option(cmd_no_comment, in_script, encoding, timeout)
        elif self.xml.is_query(cmd_no_comment):
            return self.query(cmd, in_script, encoding, timeout)
        elif in_script:
            return self.advance(cmd, encoding, timeout)
        else:
            return True, "Command only allowed in script.", None, ""

    @contextmanager
    def suppress_diffs(
        self,
        timeout: Optional[int] = None,
    ) -> Generator[None, None, None]:
        """Temporarily disable proof diffs."""
        # Check if diffs are enabled
        expect_prefix = "Diffs: Some(val="
        ok, response, _, err = self.do_option(
            "Test Diffs",
            in_script=False,
            timeout=timeout,
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
            )
            if not ok:
                self.logger.warning("Failed to re-enable Diffs option: %s", err)

    # Interacting with Coqtop #
    def call(
        self,
        cmdtype_msg: Tuple[str, Optional[bytes]],
        timeout: Optional[int] = None,
    ) -> Tuple[Result, str]:
        """Send 'msg' to the Coqtop process and wait for the response."""
        assert self.xml is not None
        # Check if Coqtop has stopped
        if not self.running():
            raise CoqtopError("Coqtop is not running.")

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
                timeout = timeout if timeout != 0 else None
                response, err = pool.submit(self.get_answer).result(timeout)
            except futures.TimeoutError:
                self.interrupt()
                response, err = TIMEOUT_ERR, ""

        return self.xml.standardize(cmd, response), err

    def get_answer(self) -> Tuple[Result, str]:
        """Read from 'out_q' and wait until a full response is received."""
        assert self.xml is not None
        data = []
        poll_sec = 1

        while True:
            # Abort if an error is printed to stderr, but ignore warnings.
            # NOTE: If `warnings_wf` is False because this version of Coq does
            # not follow the pattern expected by `partition_warnings` then
            # pretend everything is a warning and hope for the best.
            err = self.collect_err()
            if self.xml.warnings_wf and partition_warnings(err)[1] != "":
                return UNEXPECTED_ERR, err

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
                # Coqtop died
                return

    def capture_dead(self) -> None:
        """Continually check if Coqtop has died."""
        while self.running():
            time.sleep(1)
        self.stop()

    def send_cmd(self, cmd: bytes) -> None:
        """Write to Coqtop's stdin."""
        if self.coqtop is None:
            raise CoqtopError("coqtop must not be None in send_cmd()")
        if self.coqtop.stdin is None:
            raise CoqtopError("coqtop stdin must not be None in send_cmd()")

        self.coqtop.stdin.write(cmd)
        self.coqtop.stdin.flush()

    def interrupt(self) -> None:
        """Send a SIGINT signal to Coqtop."""
        if self.coqtop is None:
            raise CoqtopError("Coqtop is not running.")
        self.coqtop.send_signal(signal.SIGINT)

    # Current State #
    def running(self) -> bool:
        """Check if Coqtop has already been started."""
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
