# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Coqtop interface with functions to send commands and parse responses."""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import datetime
import logging
import os
import signal
import subprocess
import threading
import time
from tempfile import NamedTemporaryFile

from six import ensure_text
from six.moves.queue import Empty, Queue

from xmlInterface import Err, Ok, STOPPED_ERR, TIMEOUT_ERR, XMLInterface, prettyxml

# For Mypy
try:
    from typing import Any, Callable, Generator, IO, List, Optional, Text, Tuple, Union
except ImportError:
    pass

DEFAULT_REF = Err("Default Ref value. Should never be seen.")


class Ref(object):
    """A mutable value to be passed between threads."""

    __slots__ = ("val",)

    def __init__(self, val=DEFAULT_REF):
        # type: (Union[Ok, Err]) -> None
        self.val = val


class CoqtopError(Exception):
    """An exception for when Coqtop stops unexpectedly."""


class Coqtop(object):
    """Provide an interface to the background Coqtop process."""

    def __init__(self, version, done_callback):
        # type: (Text, Callable[[], None]) -> None
        """Initialize Coqtop state.

        coqtop - The Coqtop process
        done_callback - A function to call when finished waiting for Coqtop
        states - A stack of previous state_ids (grows to the right)
        state_id - The current state_id
        root_state - The starting state_id
        out_q - A thread-safe queue of data read from Coqtop
        xml - The XML interface for the given version
        """
        self.coqtop = None  # type: Optional[subprocess.Popen[bytes]]
        self.done_callback = done_callback
        self.states = []  # type: List[int]
        self.state_id = -1
        self.root_state = -1
        self.out_q = Queue()  # type: Queue[bytes]
        self.xml = XMLInterface(version)
        self.stopping = False

        # Debugging
        self.log = None  # type: Optional[IO[Text]]
        self.handler = logging.NullHandler()  # type: logging.Handler
        self.logger = logging.getLogger(str(id(self)))
        self.logger.addHandler(self.handler)
        self.logger.setLevel(logging.INFO)

    # Coqtop Interface #
    # These are expressed as generators that spawn a thread to interact with
    # Coqtop, yield and wait to be told whether the user interrupted with
    # CTRL-C, then yield the final result. This is done because Vim cannot
    # capture signals while running Python plugins, so we have to busy wait in
    # Vim instead.

    # Ideally the type would be Generator[None, bool, bool] and the final
    # 'yield's would be 'return's, but Python 2 doesn't support returning
    # values from generators.
    def start(self, coq_path, *args, **kwargs):
        # type: (str, *str, **int) -> Generator[Optional[bool], bool, None]
        """Launch the Coqtop process."""
        assert self.coqtop is None

        self.logger.debug("start")
        timeout = kwargs.get("timeout", None)

        for launch in self.xml.launch(coq_path):
            try:
                self.coqtop = subprocess.Popen(
                    launch + args,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    bufsize=0,
                )

                # Spawn threads to monitor Coqtop's stdout and stderr
                for f in (self.capture_out, self.capture_err, self.capture_dead):
                    read_thread = threading.Thread(target=f)
                    read_thread.daemon = True
                    read_thread.start()

                # Initialize Coqtop
                call = self.call(self.xml.init(), timeout=timeout)
                next(call)
                stopped = yield  # type: ignore[misc] # (see comment above start())
                response = call.send(stopped)

                if isinstance(response, Err):
                    yield False
                    return

                self.root_state = response.val
                self.state_id = response.val

                yield True
                return
            except OSError:
                continue

        # Failed to launch Coqtop
        self.coqtop = None
        self.done_callback()
        yield  # type: ignore[misc] # (see comment above start())
        yield False

    def stop(self):
        # type: () -> None
        """End the Coqtop process."""
        if self.coqtop is not None:
            self.logger.debug("stop")
            self.stopping = True

            # Close debugging log
            self.handler.flush()
            self.handler.close()
            if self.log is not None:
                self.log.close()

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

    def advance(
        self,
        cmd,  # type: Text
        encoding="utf-8",  # type: str
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Generator[Tuple[bool, Text, Optional[Tuple[int, int]]], bool, None]
        """Advance Coqtop by sending 'cmd'."""
        self.logger.debug("advance: %s", cmd)
        call = self.call(
            self.xml.add(cmd, self.state_id, encoding=encoding), timeout=timeout
        )
        next(call)
        stopped = yield  # type: ignore[misc] # (see comment above start())
        response = call.send(stopped)

        if isinstance(response, Err):
            yield False, response.msg, response.loc
            return

        # In addition to sending 'cmd', also check status in order to force it
        # to be evaluated
        call = self.call(self.xml.status(encoding=encoding), timeout=timeout)
        next(call)
        stopped = yield  # type: ignore[misc] # (see comment above start())
        status = call.send(stopped)

        # Combine messages
        msgs = "\n\n".join(
            msg
            for msg in (response.msg, response.val["res_msg"], status.msg)
            if msg != ""
        )

        if isinstance(status, Err):
            # Reset state id to before the error
            call = self.call(self.xml.edit_at(self.state_id, 1))
            next(call)
            yield  # type: ignore[misc] # (see comment above start())
            call.send(False)
            yield False, msgs, status.loc
            return

        self.states.append(self.state_id)
        self.state_id = response.val["state_id"]

        yield True, msgs, None

    def rewind(self, steps=1):
        # type: (int) -> Generator[Tuple[bool, int], bool, None]
        """Go back 'steps' states."""
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

        call = self.call(self.xml.edit_at(self.state_id, steps))
        next(call)
        stopped = yield  # type: ignore[misc] # (see comment above start())
        response = call.send(stopped)

        if isinstance(response, Ok):
            yield True, response.val
        else:
            yield False, 0

    def query(
        self,
        cmd,  # type: Text
        in_script,  # type: bool
        encoding="utf-8",  # type: str
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Generator[Tuple[bool, Text, Optional[Tuple[int, int]]], bool, None]
        """Query Coqtop with 'cmd'."""
        self.logger.debug("query: %s", cmd)
        call = self.call(
            self.xml.query(cmd, self.state_id, encoding=encoding), timeout=timeout
        )
        next(call)
        stopped = yield  # type: ignore[misc] # (see comment above start())
        response = call.send(stopped)

        if isinstance(response, Ok):
            # If the query was called from within the script we need to record
            # the state id so rewinding will work properly. Since 8.4 uses
            # number of steps rather than state ids, record '-1' to indicate
            # that no rewind should actually be done
            if in_script:
                if self.xml.versions >= (8, 5, 0):
                    self.states.append(self.state_id)
                else:
                    self.states.append(-1)
            yield True, response.msg, None
        else:
            yield False, response.msg, response.loc

    def goals(self, timeout=None):
        # type: (Optional[int]) -> Generator[Tuple[bool, Text, Optional[Tuple[List[Any], List[Any], List[Any], List[Any]]]], bool, None]
        """Get the current set of hypotheses and goals."""
        self.logger.debug("goals")
        call = self.call(self.xml.goal(), timeout=timeout)
        next(call)
        stopped = yield  # type: ignore[misc] # (see comment above start())
        response = call.send(stopped)

        if isinstance(response, Ok):
            yield True, response.msg, response.val
        else:
            yield False, "", None

    def do_option(
        self,
        cmd,  # type: Text
        in_script,  # type: bool
        encoding="utf-8",  # type: str
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Generator[Tuple[bool, Text, Optional[Tuple[int, int]]], bool, None]
        """Set or get an option."""
        self.logger.debug("do_option: %s", cmd)
        vals, opt = self.xml.parse_option(cmd)

        if vals is None:
            call = self.call(self.xml.get_options(encoding=encoding), timeout=timeout)
            next(call)
            stopped = yield  # type: ignore[misc] # (see comment above start())
            response = call.send(stopped)

            if isinstance(response, Ok):
                optval = [
                    (val, desc) for name, desc, val in response.val if name == opt
                ]

                if optval != []:
                    ret = "{}: {}".format(optval[0][1], optval[0][0])  # type: Text
                else:
                    ret = "Invalid option name"
        else:
            for val in vals:
                call = self.call(
                    self.xml.set_options(opt, val, encoding=encoding), timeout=timeout
                )
                next(call)
                stopped = yield  # type: ignore[misc] # (see comment above start())
                response = call.send(stopped)
                ret = response.msg
                if isinstance(response, Ok):
                    break

        if isinstance(response, Ok):
            # Hack to associate setting an option with a new state id by
            # executing a noop so it works correctly with rewinding
            if in_script:
                noop_call = self.advance(self.xml.noop, encoding)
                next(noop_call)
                while True:
                    yield  # type: ignore[misc] # (see comment above start())
                    noop_ret = noop_call.send(False)
                    if noop_ret is not None:
                        success, _, _ = noop_ret
                        assert success
                        break
            yield True, ret, None
        else:
            yield False, response.msg, response.loc

    def dispatch(
        self,
        cmd,  # type: Text
        in_script=True,  # type: bool
        encoding="utf-8",  # type: str
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Generator[Tuple[bool, Text, Optional[Tuple[int, int]]], bool, None]
        """Decide whether 'cmd' is setting/getting an option, a query, or a
        regular command.
        """
        # Make sure 'cmd' is a string format that supports unicode
        cmd = ensure_text(cmd, encoding)  # type: ignore[no-untyped-call]

        if self.xml.is_option(cmd):
            call = self.do_option(cmd, in_script, encoding, timeout)
        elif self.xml.is_query(cmd):
            call = self.query(cmd, in_script, encoding, timeout)
        elif in_script:
            call = self.advance(cmd, encoding, timeout)
        else:
            self.done_callback()
            yield  # type: ignore[misc] # (see comment above start())
            yield True, "Command only allowed in script.", None
            return

        next(call)
        while True:
            stopped = yield  # type: ignore[misc] # (see comment above start())
            ret = call.send(stopped)
            if ret is not None:
                yield ret
                break

    # Interacting with Coqtop #
    def call(
        self,
        cmdtype_msg,  # type: Tuple[Text, Optional[bytes]]
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Generator[Union[Ok, Err], bool, None]
        """Send 'msg' to the Coqtop process and wait for the response."""
        # Check if Coqtop has stopped
        if not self.running():
            raise CoqtopError("Coqtop is not running.")

        # Throw away any unread messages
        self.empty_out()

        cmd, msg = cmdtype_msg

        # 'msg' can be None if a command does not exist for a particular
        # version and is being faked.
        # N.B. It is important that the '_standardize' function being called
        # does not depend on the value it is passed since it is None
        if msg is None:
            self.done_callback()
            yield  # type: ignore[misc] # (see comment above start())
            yield self.xml.standardize(cmd, Ok(None))
            return

        # Don't bother doing prettyxml if debugging isn't on
        if self.logger.isEnabledFor(logging.DEBUG):
            self.logger.debug(prettyxml(msg))
        self.send_cmd(msg)

        if timeout == 0:
            timeout = None

        # The got_response event tells the timeout_thread that get_answer()
        # returned normally, while timed_out will be set by timeout_thread if
        # time runs out without receiving a response
        got_response = threading.Event()
        timed_out = threading.Event()
        timeout_thread = threading.Thread(
            target=self.timeout_thread, args=(timeout, got_response, timed_out)
        )
        timeout_thread.daemon = True

        # Start a thread to get Coqtop's response
        res_ref = Ref()
        answer_thread = threading.Thread(target=self.get_answer, args=(res_ref,))
        answer_thread.daemon = True

        # Start threads and yield back to caller to wait for Coqtop to finish
        timeout_thread.start()
        answer_thread.start()
        stopped = yield  # type: ignore[misc] # (see comment above start())

        # Notify timeout_thread that a response is received and wait for
        # threads to finish
        got_response.set()
        timeout_thread.join()
        answer_thread.join()

        response = res_ref.val

        # Check for user interrupt or timeout
        if isinstance(response, Err):
            if stopped:
                response = STOPPED_ERR
            elif timed_out.is_set():
                response = TIMEOUT_ERR

        yield self.xml.standardize(cmd, response)

    def timeout_thread(self, timeout, got_response, timed_out):
        # type: (int, threading.Event, threading.Event) -> None
        """Wait on the 'got_response' Event for timeout seconds and set
        'timed_out' and interrupt the Coqtop process if it is not set in
        time.
        """
        if self.coqtop is None:
            raise CoqtopError("coqtop must not be None in timeout_thread()")

        if not got_response.wait(timeout):
            self.interrupt()
            timed_out.set()

    def get_answer(self, res_ref):
        # type: (Ref) -> None
        """Read from 'out_q' and wait until a full response is received."""
        data = []

        while True:
            data.append(self.out_q.get())
            xml = b"".join(data)
            if not self.xml.worth_parsing(xml):
                continue
            response = self.xml.raw_response(xml)

            if response is None:
                continue

            # Don't bother doing prettyxml if debugging isn't on
            if self.logger.isEnabledFor(logging.DEBUG):
                self.logger.debug(prettyxml(b"<response>" + xml + b"</response>"))
            res_ref.val = response
            # Notify the caller that Coqtop is done
            self.done_callback()
            break

    def empty_out(self):
        # type: () -> None
        """Pop data until 'out_q' is empty."""
        while not self.out_q.empty():
            try:
                self.out_q.get_nowait()
            except Empty:
                return

    def capture_out(self):
        # type: () -> None
        """Continually read data from Coqtop's stdout into 'out_q'."""
        if self.coqtop is None:
            raise CoqtopError("coqtop must not be None in capture_out()")
        if self.coqtop.stdout is None:
            raise CoqtopError("coqtop stdout must not be None in capture_out()")
        fd = self.coqtop.stdout.fileno()

        while not self.stopping:
            try:
                self.out_q.put(os.read(fd, 0x10000))
            except (AttributeError, OSError, ValueError):
                # Coqtop died
                return

    def capture_err(self):
        # type: () -> None
        """Continually read data from Coqtop's stderr and print it."""
        if self.coqtop is None:
            raise CoqtopError("coqtop must not be None in capture_err()")
        if self.coqtop.stderr is None:
            raise CoqtopError("coqtop stderr must not be None in capture_err()")
        fd = self.coqtop.stderr.fileno()

        while not self.stopping:
            try:
                print(os.read(fd, 0x10000).decode())
            except (AttributeError, OSError, ValueError):
                # Coqtop died
                return

    def capture_dead(self):
        # type: () -> None
        """Continually check if Coqtop has died."""
        while self.running():
            time.sleep(1)
        self.stop()

    def send_cmd(self, cmd):
        # type: (bytes) -> None
        """Write to Coqtop's stdin."""
        if self.coqtop is None:
            raise CoqtopError("coqtop must not be None in send_cmd()")
        if self.coqtop.stdin is None:
            raise CoqtopError("coqtop stdin must not be None in send_cmd()")

        self.coqtop.stdin.write(cmd)
        self.coqtop.stdin.flush()

    def interrupt(self):
        # type: () -> None
        """Send a SIGINT signal to Coqtop."""
        if self.coqtop is None:
            raise CoqtopError("Coqtop is not running.")
        self.coqtop.send_signal(signal.SIGINT)

    # Current State #
    def running(self):
        # type: () -> bool
        """Check if Coqtop has already been started."""
        return self.coqtop is not None and self.coqtop.poll() is None

    # Debugging #
    def toggle_debug(self):
        # type: () -> Optional[str]
        """Enable or disable logging of debug messages."""
        self.logger.removeHandler(self.handler)
        self.handler.flush()
        self.handler.close()

        if self.log is None:
            # Create unique log file
            pre = "coqtop_{}_".format(datetime.datetime.now().strftime("%y%m%d_%H%M%S"))
            fmt = logging.Formatter("%(asctime)s: %(message)s")
            # Python 2 says _TemporaryFileWrapper is incompatible with IO[Text]
            self.log = NamedTemporaryFile(mode="w", prefix=pre, delete=False)  # type: ignore[assignment]
            self.handler = logging.StreamHandler(self.log)
            self.handler.setFormatter(fmt)
            self.logger.addHandler(self.handler)
            self.logger.setLevel(logging.DEBUG)
            return self.log.name  # type: ignore[no-any-return, attr-defined] # (see above)
        else:
            # Clean up old logging
            self.log.close()

            # Set to null logging
            self.log = None
            self.handler = logging.NullHandler()
            self.logger.addHandler(self.handler)
            self.logger.setLevel(logging.CRITICAL)
            return None
