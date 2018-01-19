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
try:
    import Queue as queue
except ImportError:
    import queue

from xmlInterface import XmlInterface, TIMEOUT_ERR


class CoqtopError(Exception):
    """An exception for when Coqtop stops unexpectedly."""
    pass


class Coqtop(object):
    """Provide an interface to the background Coqtop process."""

    def __init__(self, version):
        """Initialize Coqtop state.

        coqtop - The Coqtop process
        states - A stack of previous state_ids (grows to the right)
        state_id - The current state_id
        root_state - The starting state_id
        out_q - A thread-safe queue of data read from Coqtop
        xml - The XML interface for the given version
        """
        self.coqtop = None
        self.states = []
        self.state_id = None
        self.root_state = None
        self.out_q = queue.Queue()
        self.xml = XmlInterface(version)

    # Coqtop Interface #
    def start(self, *args, **kwargs):
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
            if not response.is_ok():
                return False

            self.root_state = response.val
            self.state_id = response.val

            return True
        except OSError:
            return False

    def stop(self):
        """End the Coqtop process."""
        if self.coqtop is not None:
            try:
                # Try to terminate Coqtop cleanly
                # TODO: use Quit call
                self.coqtop.terminate()
                self.coqtop.communicate()
            except (OSError, ValueError):
                try:
                    # Force Coqtop to stop
                    self.coqtop.kill()
                except OSError:
                    pass

            self.coqtop = None

    def advance(self, cmd, encoding='utf-8', timeout=None):
        """Advance Coqtop by sending 'cmd'."""
        response = self.call(self.xml.add(cmd,
                                          self.state_id,
                                          encoding=encoding),
                             timeout=timeout)

        if not response.is_ok():
            return False, response.msg, response.loc

        # In addition to sending 'cmd', also check status in order to force it
        # to be evaluated
        status = self.call(self.xml.status(encoding=encoding), timeout=timeout)

        # Combine messages
        msgs = '\n\n'.join(msg
                           for msg in (response.msg,
                                       response.res_msg,
                                       status.msg)
                           if msg != '')

        if not status.is_ok():
            # Reset state id to before the error
            self.call(self.xml.edit_at(self.state_id, 1))
            return False, msgs, status.loc

        self.states.append(self.state_id)
        self.state_id = response.state_id

        return True, msgs, None

    def rewind(self, step=1):
        """Go back 'step' states."""
        if step > len(self.states):
            self.state_id = self.root_state
            self.states = []
        else:
            self.state_id = self.states[-step]
            self.states = self.states[:-step]

        response = self.call(self.xml.edit_at(self.state_id, step))
        return response.is_ok(), response.extra_steps

    def query(self, cmd, encoding='utf-8', timeout=None):
        """Query Coqtop with 'cmd'."""
        response = self.call(self.xml.query(cmd,
                                            self.state_id,
                                            encoding=encoding),
                             timeout=timeout)

        if response.is_ok():
            return True, response.msg, None
        else:
            return False, response.msg, response.loc

    def goals(self, timeout=None):
        """Get the current set of hypotheses and goals."""
        response = self.call(self.xml.goal(), timeout=timeout)

        return response.is_ok(), response.msg, response.val

    def mk_cases(self, ty, encoding='utf-8', timeout=None):
        """Return cases for each constructor of 'ty'."""
        response = self.call(self.xml.mk_cases(ty, encoding=encoding),
                             timeout=timeout)

        if response.is_ok():
            return True, response.val
        else:
            return False, response.msg

    def do_option(self, cmd, encoding='utf-8', timeout=None):
        """Set or get an option."""
        if cmd.startswith('Test'):
            response = self.call(self.xml.get_options(encoding=encoding),
                                 timeout=timeout)

            if response.is_ok():
                optval = [(val, desc) for name, desc, val in response.val
                          if name in cmd]

                if optval != []:
                    ret = "{}: {}".format(optval[0][1], optval[0][0])
                else:
                    ret = 'Invalid option name'
        else:
            response = self.call(self.xml.set_options(cmd, encoding=encoding),
                                 timeout=timeout)
            ret = response.msg

        if response.is_ok():
            return True, ret, None
        else:
            return False, response.msg, response.loc

    def dispatch(self, cmd, encoding='utf-8', timeout=None):
        """Decide whether 'cmd' is setting/getting an option, a query, or a
        regular command."""
        # Python 2 will throw an error if unicode is in 'cmd' unless we decode
        # it, but in Python 3 'cmd' is 'str' not 'bytes' and doesn't need to be
        # decoded
        if isinstance(cmd, bytes):
            cmd = cmd.decode(encoding)
        cmd = cmd.strip()

        if self.xml.is_option(cmd):
            return self.do_option(cmd, encoding, timeout=timeout)
        elif self.xml.is_query(cmd):
            return self.query(cmd, encoding, timeout)
        else:
            return self.advance(cmd, encoding, timeout)

    # Interacting with Coqtop #
    def call(self, cmdtype_msg, timeout=None):
        """Send 'msg' to the Coqtop process and wait for the response."""
        # Check if Coqtop has stopped
        if not self.running():
            raise CoqtopError('Coqtop is not running.')

        # Throw away any unread messages
        self.empty_out()

        cmd, msg = cmdtype_msg

        # 'msg' can be None if a command does not exist for a particular
        # version and is being faked
        if msg is None:
            return self.xml.standardize(cmd, None)

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
        """Wait on the 'got_response' Event for timeout seconds and set
        'timed_out' and interrupt the Coqtop process if it is not set in
        time.
        """
        if not got_response.wait(timeout):
            self.coqtop.send_signal(signal.SIGINT)
            timed_out.set()

    def get_answer(self):
        """Read from 'out_q' and wait until a full response is received."""
        data = []

        while True:
            data.append(self.out_q.get())
            response = self.xml.raw_response(b''.join(data))

            if response is None:
                continue

            return response

    def empty_out(self):
        """Pop data until 'out_q' is empty."""
        while not self.out_q.empty():
            try:
                self.out_q.get_nowait()
            except queue.Empty:
                break

    # TODO: figure out why python 2 needs os.read vs stdout.read but 3 doesn't
    def capture_out(self):
        """Continually read data from Coqtop's stdout into 'out_q'."""
        fd = self.coqtop.stdout.fileno()

        while True:
            try:
                self.out_q.put(os.read(fd, 0x10000))
                # self.out_q.put(self.coqtop.stdout.read(0x10000))
            except (AttributeError, OSError, ValueError):
                # Coqtop died
                return

    # TODO: figure out why printing to stderr causes hide_colors() to fail on
    # quit
    def capture_err(self):
        """Continually read data from Coqtop's stderr and print it."""
        fd = self.coqtop.stderr.fileno()

        while True:
            try:
                print(os.read(fd, 0x10000).decode())
                # print(os.read(fd, 0x10000).decode(), file=sys.stderr)
            except (AttributeError, OSError, ValueError):
                # Coqtop died
                return

    def capture_dead(self):
        """Continually check if Coqtop has died."""
        while self.running():
            pass
        self.stop()

    def send_cmd(self, cmd):
        """Write to Coqtop's stdin."""
        self.coqtop.stdin.write(cmd)
        self.coqtop.stdin.flush()

    # Current State #
    def running(self):
        """Check if Coqtop has already been started."""
        return self.coqtop is not None and self.coqtop.poll() is None
