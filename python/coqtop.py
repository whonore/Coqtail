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
    from typing import Any, IO, List, Optional, Text, Tuple, Union
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

    def __init__(self, version):
        # type: (Text) -> None
        """Initialize Coqtop state.

        coqtop - The Coqtop process
        states - A stack of previous state_ids (grows to the right)
        state_id - The current state_id
        root_state - The starting state_id
        out_q - A thread-safe queue of data read from Coqtop
        xml - The XML interface for the given version
        """
        self.coqtop = None  # type: Optional[subprocess.Popen[bytes]]
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
    def start(self, coq_path, *args, **kwargs):
        # type: (str, *str, **int) -> bool
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
                response = self.call(self.xml.init(), timeout=timeout)

                if isinstance(response, Err):
                    return False

                self.root_state = response.val
                self.state_id = response.val

                return True
            except OSError:
                continue

        # Failed to launch Coqtop
        self.coqtop = None
        return False

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
        # type: (...) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Advance Coqtop by sending 'cmd'."""
        self.logger.debug("advance: %s", cmd)
        response = self.call(
            self.xml.add(cmd, self.state_id, encoding=encoding), timeout=timeout
        )

        if isinstance(response, Err):
            return False, response.msg, response.loc

        # In addition to sending 'cmd', also check status in order to force it
        # to be evaluated
        status = self.call(self.xml.status(encoding=encoding), timeout=timeout)

        # Combine messages
        msgs = "\n\n".join(
            msg
            for msg in (response.msg, response.val["res_msg"], status.msg)
            if msg != ""
        )

        if isinstance(status, Err):
            # Reset state id to before the error
            self.call(self.xml.edit_at(self.state_id, 1))
            return False, msgs, status.loc

        self.states.append(self.state_id)
        self.state_id = response.val["state_id"]

        return True, msgs, None

    def rewind(self, steps=1):
        # type: (int) -> Tuple[bool, int]
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

        response = self.call(self.xml.edit_at(self.state_id, steps))

        if isinstance(response, Ok):
            return True, response.val
        else:
            return False, 0

    def query(
        self,
        cmd,  # type: Text
        in_script,  # type: bool
        encoding="utf-8",  # type: str
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Query Coqtop with 'cmd'."""
        self.logger.debug("query: %s", cmd)
        response = self.call(
            self.xml.query(cmd, self.state_id, encoding=encoding), timeout=timeout
        )

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
            return True, response.msg, None
        else:
            return False, response.msg, response.loc

    def goals(self, timeout=None):
        # type: (Optional[int]) -> Tuple[bool, Text, Optional[Tuple[List[Any], List[Any], List[Any], List[Any]]]]
        """Get the current set of hypotheses and goals."""
        self.logger.debug("goals")
        response = self.call(self.xml.goal(), timeout=timeout)

        if isinstance(response, Ok):
            return True, response.msg, response.val
        else:
            return False, "", None

    def do_option(
        self,
        cmd,  # type: Text
        in_script,  # type: bool
        encoding="utf-8",  # type: str
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Set or get an option."""
        self.logger.debug("do_option: %s", cmd)
        vals, opt = self.xml.parse_option(cmd)

        if vals is None:
            response = self.call(
                self.xml.get_options(encoding=encoding), timeout=timeout
            )

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
                response = self.call(
                    self.xml.set_options(opt, val, encoding=encoding), timeout=timeout
                )
                ret = response.msg
                if isinstance(response, Ok):
                    break

        if isinstance(response, Ok):
            # Hack to associate setting an option with a new state id by
            # executing a noop so it works correctly with rewinding
            if in_script:
                success, _, _ = self.advance(self.xml.noop, encoding)
                assert success
            return True, ret, None
        else:
            return False, response.msg, response.loc

    def dispatch(
        self,
        cmd,  # type: Text
        in_script=True,  # type: bool
        encoding="utf-8",  # type: str
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Decide whether 'cmd' is setting/getting an option, a query, or a
        regular command.
        """
        # Make sure 'cmd' is a string format that supports unicode
        cmd = ensure_text(cmd, encoding)  # type: ignore[no-untyped-call]

        if self.xml.is_option(cmd):
            return self.do_option(cmd, in_script, encoding, timeout)
        elif self.xml.is_query(cmd):
            return self.query(cmd, in_script, encoding, timeout)
        elif in_script:
            return self.advance(cmd, encoding, timeout)
        else:
            return True, "Command only allowed in script.", None

    # Interacting with Coqtop #
    def call(
        self,
        cmdtype_msg,  # type: Tuple[Text, Optional[bytes]]
        timeout=None,  # type: Optional[int]
    ):
        # type: (...) -> Union[Ok, Err]
        """Send 'msg' to the Coqtop process and wait for the response."""
        # Check if Coqtop has stopped
        if not self.running():
            raise CoqtopError("Coqtop is not running.")

        # Throw away any unread messages
        self.empty_out()

        # 'msg' can be None if a command does not exist for a particular
        # version and is being faked.
        # N.B. It is important that the '_standardize' function being called
        # does not depend on the value it is passed since it is None
        cmd, msg = cmdtype_msg
        if msg is None:
            return self.xml.standardize(cmd, Ok(None))

        # Don't bother doing prettyxml if debugging isn't on
        if self.logger.isEnabledFor(logging.DEBUG):
            self.logger.debug(prettyxml(msg))
        self.send_cmd(msg)

        if timeout == 0:
            timeout = None

        # TODO: simplify this
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

        # Start threads and wait for Coqtop to finish
        timeout_thread.start()
        answer_thread.start()
        stopped = False

        # Notify timeout_thread that a response is received and wait for
        # threads to finish
        got_response.set()
        timeout_thread.join()
        answer_thread.join()

        # Check for user interrupt or timeout
        response = res_ref.val
        if isinstance(response, Err):
            if stopped:
                response = STOPPED_ERR
            elif timed_out.is_set():
                response = TIMEOUT_ERR

        return self.xml.standardize(cmd, response)

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
