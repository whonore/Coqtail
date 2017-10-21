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


class Coqtop(object):
    """ FIXME: add description
    """

    def __init__(self, version):
        """ FIXME: add description
        """
        self.coqtop = None
        self.states = []
        self.state_id = None
        self.root_state = None
        self.out_q = queue.Queue()
        self.xml = XmlInterface(version)

    # Coqtop Interface #
    def start(self, *args, **kwargs):
        """ FIXME: add description
        """
        if self.running():
            self.stop()

        timeout = kwargs.get('timeout', None)

        options = ['coqtop',
                   '-ideslave',
                   '-main-channel', 'stdfds',
                   '-async-proofs', 'on']
        try:
            self.coqtop = subprocess.Popen(
                options + list(args),
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                bufsize=0)

            # Spawn threads to monitor Coqtop's stdout and stderr
            for f in (self.capture_out, self.capture_err):
                read_thread = threading.Thread(target=f)
                read_thread.daemon = True
                read_thread.start()

            # Initialize Coqtop
            result = self.call(self.xml.init(), timeout=timeout)
            if not result.is_ok():
                return False

            self.root_state = result.val
            self.state_id = result.val

            return True
        except OSError:
            return False

    def stop(self):
        """ FIXME: add description
        """
        if self.running():
            try:
                self.coqtop.terminate()
                self.coqtop.communicate()
            except OSError:
                pass
            self.coqtop = None

    def advance(self, cmd, encoding='utf-8', timeout=None):
        """ FIXME: add description
        """
        # Python 2 will throw an error if unicode is in 'cmd' unless we decode
        # it, but in Python 3 'cmd' is 'str' not 'bytes' and doesn't need to be
        # decoded
        if isinstance(cmd, bytes):
            cmd = cmd.decode(encoding)

        result = self.call(self.xml.add(cmd,
                                        self.cur_state(),
                                        encoding=encoding),
                           timeout=timeout)
        goals = self.goals(timeout=timeout)

        if result.is_ok():
            msgs = [result.val[1][1]]
        else:
            msgs = []
        msgs += [str(res) for res in (result, goals)]
        result.msg = goals.msg = '\n\n'.join(msg for msg in msgs if msg != '')

        if not result.is_ok():
            return result

        if not goals.is_ok():
            # Reset position to get goals back
            self.call(self.xml.edit_at(self.state_id))
            return goals

        self.states.append(self.state_id)
        self.state_id = result.val[0]

        # Coqtop refuses to show queries in a script so catch the error and
        # resend as a query
        if 'Query commands should not' in str(result):
            return self.query(cmd, encoding=encoding, timeout=timeout)

        return result

    def rewind(self, step=1):
        """ FIXME: add description
        """
        if step > len(self.states):
            self.state_id = self.root_state
        else:
            self.state_id = self.states[-step]
            self.states = self.states[0:-step]

        return self.call(self.xml.edit_at(self.state_id))

    def query(self, cmd, encoding='utf-8', timeout=None):
        """ FIXME: add description
        """
        # See 'advance' for an explanation of this
        if isinstance(cmd, bytes):
            cmd = cmd.decode(encoding)

        return self.call(self.xml.query(cmd,
                                        self.cur_state(),
                                        encoding=encoding),
                         timeout=timeout)

    def goals(self, timeout=None):
        """ FIXME: add description
        response = self.call(self.xml.goal(), timeout=timeout)

        if response.is_ok():
            if response.val.val is None:
                response.val = None
            else:
                response.val = response.val.val.fg

        return response

    # Interacting with Coqtop #
        """ FIXME: add description
    def call(self, msg, timeout=None):
        self.empty_out()

        self.send_cmd(msg)

        if timeout == 0:
            timeout = None

        # The got_response event tells the timeout_thread that get_answer()
        # returned normally, while timed_out will be set by timeout_thread if
        # time runs out without receiving a response.
        got_response = threading.Event()
        timed_out = threading.Event()
        timeout_thread = threading.Thread(target=self.timeout_thread,
                                          args=(timeout,
                                                got_response,
                                                timed_out))
        timeout_thread.daemon = True

        timeout_thread.start()
        response = self.get_answer()

        got_response.set()
        if timed_out.is_set():
            response = TIMEOUT_ERR

        return response

    def timeout_thread(self, timeout, got_response, timed_out):
        """ FIXME: add description
        """
        if not got_response.wait(timeout):
            self.coqtop.send_signal(signal.SIGINT)
            timed_out.set()

    def get_answer(self):
        """ FIXME: add description
        """
        data = []

        while True:
            data.append(self.out_q.get())
            response = self.xml.raw_response(b''.join(data))

            if response is None:
                continue

            return response

    def empty_out(self):
        """ FIXME: add description """
        while not self.out_q.empty():
            try:
                self.out_q.get_nowait()
            except queue.Empty:
                break

    # TODO: figure out why python 2 needs os.read vs stdout.read but 3 doesnt'
    def capture_out(self):
        """ FIXME: add description """
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
        """ FIXME: add description """
        fd = self.coqtop.stderr.fileno()

        while True:
            try:
                print(os.read(fd, 0x10000).decode())
                # print(os.read(fd, 0x10000).decode(), file=sys.stderr)
            except (AttributeError, OSError, ValueError):
                # Coqtop died
                return

    def send_cmd(self, cmd):
        """ FIXME: add description
        """
        self.coqtop.stdin.write(cmd)
        self.coqtop.stdin.flush()

    # Current State #
    def running(self):
        """ FIXME: add description
        """
        return self.coqtop is not None

    def cur_state(self):
        """ FIXME: add description
        """
        if self.states == []:
            return self.root_state
        return self.state_id
