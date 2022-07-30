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
from queue import Empty, Queue
from tempfile import NamedTemporaryFile
from typing import (
    IO,
    TYPE_CHECKING,
    Any,
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
        msgs = "\n\n".join(
            msg
            for msg in (response.msg, response.val["res_msg"], status.msg)
            if msg != ""
        )
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
        response, err = self.call(self.xml.goal(), timeout=timeout)

        return (
            isinstance(response, Ok),
            response.msg,
            response.val if isinstance(response, Ok) else None,
            err,
        )

    def do_option(
        self,
        cmd: str,
        in_script: bool,
        encoding: str = "utf-8",
        timeout: Optional[int] = None,
    ) -> Tuple[bool, str, Optional[Tuple[int, int]], str]:
        """Set or get an option."""
        assert self.xml is not None
        self.logger.debug("do_option: %s", cmd)
        vals, opt = self.xml.parse_option(cmd)

        if vals is None:
            response, err = self.call(
                self.xml.get_options(encoding=encoding),
                timeout=timeout,
            )

            if isinstance(response, Ok):
                optval = [
                    (val, desc) for name, desc, val in response.val if name == opt
                ]

                if optval != []:
                    ret = f"{optval[0][1]}: {optval[0][0]}"
                else:
                    ret = "Invalid option name"
        else:
            errs = []
            for val in vals:
                response, err = self.call(
                    self.xml.set_options(opt, val, encoding=encoding),
                    timeout=timeout,
                )
                ret = response.msg
                errs.append(err)
                if isinstance(response, Ok):
                    break
            err = "".join(errs)

        if isinstance(response, Ok) and in_script:
            # Hack to associate setting an option with a new state id by
            # executing a noop so it works correctly with rewinding
            if in_script:
                success, _, _, _ = self.advance(self.xml.noop, encoding)
                assert success

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
