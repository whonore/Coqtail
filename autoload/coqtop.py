# -*- coding: utf8 -*-
"""
File: coqtop.py
Author: Wolf Honore (inspired by/partially adapted from Coquille)

Coquille Credit:
Copyright (c) 2013, Thomas Refis

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.

Description: Provides an interface to Coqtop with functions to send commands
and parse responses.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import os
import subprocess
import signal
import sys
import threading

if sys.version_info[0] >= 3:
    import queue
else:
    import Queue as queue

from xmlInterface import XmlInterface, Ok, Err, TIMEOUT_ERR

# For Mypy
try:
    from typing import (Any, Callable, Dict, Iterable, List, Optional, Text,
                        Tuple, Type, Union)
except ImportError:
    pass


class CoqtopError(Exception):
    """An exception for when Coqtop stops unexpectedly."""
    pass


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
        self.coqtop = None  # type: Optional[subprocess.Popen]
        self.states = []  # type: List[int]
        self.state_id = -1
        self.root_state = -1
        self.out_q = queue.Queue()  # type: queue.Queue[bytes]
        self.xml = XmlInterface(version)
        self.stopping = False

    # Coqtop Interface #
    def start(self, *args, **kwargs):
        # type: (*str, **int) -> bool
        """Launch the Coqtop process."""
        assert self.coqtop is None

        timeout = kwargs.get('timeout', None)

        options = ['coqtop'] + self.xml.launch_args
        try:
            self.coqtop = subprocess.Popen(
                options + list(args),
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                bufsize=0)

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
            return False

    def stop(self):
        # type: () -> None
        """End the Coqtop process."""
        if self.coqtop is not None:
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

    def advance(self, cmd, encoding='utf-8', timeout=None):
        # type: (Text, str, Optional[int]) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Advance Coqtop by sending 'cmd'."""
        response = self.call(self.xml.add(cmd,
                                          self.state_id,
                                          encoding=encoding),
                             timeout=timeout)

        if isinstance(response, Err):
            return False, response.msg, response.loc

        # In addition to sending 'cmd', also check status in order to force it
        # to be evaluated
        status = self.call(self.xml.status(encoding=encoding), timeout=timeout)

        # Combine messages
        msgs = '\n\n'.join(msg
                           for msg in (response.msg,
                                       response.val['res_msg'],
                                       status.msg)
                           if msg != '')

        if isinstance(status, Err):
            # Reset state id to before the error
            self.call(self.xml.edit_at(self.state_id, 1))
            return False, msgs, status.loc

        self.states.append(self.state_id)
        self.state_id = response.val['state_id']

        return True, msgs, None

    def rewind(self, step=1):
        # type: (int) -> Tuple[bool, int]
        """Go back 'step' states."""
        if step > len(self.states):
            self.state_id = self.root_state
            self.states = []
            step = len(self.states)
        else:
            self.state_id = self.states[-step]
            self.states = self.states[:-step]

        response = self.call(self.xml.edit_at(self.state_id, step))
        if isinstance(response, Ok):
            return True, response.val
        else:
            return False, 0

    def query(self, cmd, in_script, encoding='utf-8', timeout=None):
        # type: (Text, bool, str, Optional[int]) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Query Coqtop with 'cmd'."""
        response = self.call(self.xml.query(cmd,
                                            self.state_id,
                                            encoding=encoding),
                             timeout=timeout)

        if isinstance(response, Ok):
            # If the query was called from within the script we need to record
            # the state id so rewinding will work properly. Since 8.4 uses
            # number of steps rather than state ids, don't record the state id
            if in_script and self.xml.versions >= (8, 5, 0):
                self.states.append(self.state_id)
            return True, response.msg, None
        else:
            return False, response.msg, response.loc

    def goals(self, timeout=None):
        # type: (Optional[int]) -> Tuple[bool, Text, Any]
        """Get the current set of hypotheses and goals."""
        response = self.call(self.xml.goal(), timeout=timeout)

        if isinstance(response, Ok):
            return True, response.msg, response.val
        else:
            return False, '', []

    def mk_cases(self, ty, encoding='utf-8', timeout=None):
        # type: (Text, str, Optional[int]) -> Tuple[bool, Text]
        """Return cases for each constructor of 'ty'."""
        response = self.call(self.xml.mk_cases(ty, encoding=encoding),
                             timeout=timeout)

        if isinstance(response, Ok):
            return True, response.val
        else:
            return False, response.msg

    def do_option(self, cmd, in_script, encoding='utf-8', timeout=None):
        # type: (Text, bool, str, Optional[int]) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Set or get an option."""
        if cmd.startswith('Test'):
            response = self.call(self.xml.get_options(encoding=encoding),
                                 timeout=timeout)

            if isinstance(response, Ok):
                optval = [(val, desc) for name, desc, val in response.val
                          if name in cmd]

                if optval != []:
                    ret = "{}: {}".format(optval[0][1], optval[0][0])  # type: Text
                else:
                    ret = 'Invalid option name'
        else:
            response = self.call(self.xml.set_options(cmd, encoding=encoding),
                                 timeout=timeout)
            ret = response.msg

        if isinstance(response, Ok):
            # See comment in query()
            if in_script and self.xml.versions >= (8, 5, 0):
                self.states.append(self.state_id)
            return True, ret, None
        else:
            return False, response.msg, response.loc

    def dispatch(self, cmd, in_script=True, encoding='utf-8', timeout=None):
        # type: (Text, bool, str, Optional[int]) -> Tuple[bool, Text, Optional[Tuple[int, int]]]
        """Decide whether 'cmd' is setting/getting an option, a query, or a
        regular command."""
        # Python 2 will throw an error if unicode is in 'cmd' unless we decode
        # it, but in Python 3 'cmd' is 'str' not 'bytes' and doesn't need to be
        # decoded
        if isinstance(cmd, bytes):
            cmd = cmd.decode(encoding)
        cmd = cmd.strip()

        if self.xml.is_option(cmd):
            return self.do_option(cmd, in_script, encoding, timeout)
        elif self.xml.is_query(cmd):
            return self.query(cmd, in_script, encoding, timeout)
        else:
            return self.advance(cmd, encoding, timeout)

    # Interacting with Coqtop #
    def call(self, cmdtype_msg, timeout=None):
        # type: (Tuple[Text, Optional[Text]], Optional[int]) -> Union[Ok, Err]
        """Send 'msg' to the Coqtop process and wait for the response."""
        # Check if Coqtop has stopped
        if not self.running():
            raise CoqtopError('Coqtop is not running.')

        # Throw away any unread messages
        self.empty_out()

        cmd, msg = cmdtype_msg

        # 'msg' can be None if a command does not exist for a particular
        # version and is being faked.
        # N.B. It is important that the '_standardize' function being called
        # does not depend on the value it is passed since it is None
        if msg is None:
            return self.xml.standardize(cmd, Ok(None))

        self.send_cmd(msg)

        if timeout == 0:
            timeout = None

        # The got_response event tells the timeout_thread that get_answer()
        # returned normally, while timed_out will be set by timeout_thread if
        # time runs out without receiving a response
        got_response = threading.Event()
        timed_out = threading.Event()
        timeout_thread = threading.Thread(target=self.timeout_thread,
                                          args=(timeout,
                                                got_response,
                                                timed_out))
        timeout_thread.daemon = True

        # Start timeout timer
        timeout_thread.start()

        # Wait for a response
        response = self.get_answer()

        got_response.set()
        if timed_out.is_set():
            response = TIMEOUT_ERR

        return self.xml.standardize(cmd, response)

    def timeout_thread(self, timeout, got_response, timed_out):
        # type: (int, threading.Event, threading.Event) -> None
        """Wait on the 'got_response' Event for timeout seconds and set
        'timed_out' and interrupt the Coqtop process if it is not set in
        time.
        """
        if self.coqtop is None:
            raise CoqtopError('coqtop must not be None in timeout_thread()')

        if not got_response.wait(timeout):
            self.coqtop.send_signal(signal.SIGINT)
            timed_out.set()

    def get_answer(self):
        # type: () -> Union[Ok, Err]
        """Read from 'out_q' and wait until a full response is received."""
        data = []

        while True:
            data.append(self.out_q.get())
            response = self.xml.raw_response(b''.join(data))

            if response is None:
                continue

            return response

    def empty_out(self):
        # type: () -> None
        """Pop data until 'out_q' is empty."""
        while not self.out_q.empty():
            try:
                self.out_q.get_nowait()
            except queue.Empty:
                return

    def capture_out(self):
        # type: () -> None
        """Continually read data from Coqtop's stdout into 'out_q'."""
        if self.coqtop is None:
            raise CoqtopError('coqtop must not be None in capture_out()')
        if self.coqtop.stdout is None:
            raise CoqtopError('coqtop stdout must not be None in capture_out()')

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
            raise CoqtopError('coqtop must not be None in capture_err()')
        if self.coqtop.stderr is None:
            raise CoqtopError('coqtop stdout must not be None in capture_err()')
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
            pass
        self.stop()

    def send_cmd(self, cmd):
        # type: (Text) -> None
        """Write to Coqtop's stdin."""
        if self.coqtop is None:
            raise CoqtopError('coqtop must not be None in send_cmd()')
        if self.coqtop.stdin is None:
            raise CoqtopError('coqtop stdin must not be None in send_cmd()')

        self.coqtop.stdin.write(cmd)
        self.coqtop.stdin.flush()

    # Current State #
    def running(self):
        # type: () -> bool
        """Check if Coqtop has already been started."""
        return self.coqtop is not None and self.coqtop.poll() is None
