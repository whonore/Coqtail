# -*- coding: utf8 -*-
'''
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

FIXME: add description
'''

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import vim

import os
import subprocess
import signal
import sys
import threading
import xml.etree.ElementTree as ET
from collections import namedtuple
try:
    import Queue as queue
except ImportError:
    import queue

    # If in python 3 make unicode an alias for str
    unicode = str

# Parsing Coqtop #
# Much of the parsing of Coqtop responses is copied from Coquille
Ok = namedtuple('Ok', ['val', 'msg'])
Err = namedtuple('Err', ['err', 'loc', 'timeout'])

Inl = namedtuple('Inl', ['val'])
Inr = namedtuple('Inr', ['val'])

StateId = namedtuple('StateId', ['id'])
Option = namedtuple('Option', ['val'])

OptionState = namedtuple('OptionState', ['sync', 'depr', 'name', 'value'])
OptionValue = namedtuple('OptionValue', ['val'])

Status = namedtuple('Status', ['path', 'proofname', 'allproofs', 'proofnum'])

Goals = namedtuple('Goals', ['fg', 'bg', 'shelved', 'given_up'])
Goal = namedtuple('Goal', ['id', 'hyp', 'ccl'])
Evar = namedtuple('Evar', ['info'])

TIMEOUT_ERR = Err('Coq timed out. You can change the timeout with '
                  '<leader>ct and try again.',
                  None, True)


def get_message(ok_err):
    ''' FIXME: add description
    '''
    if isinstance(ok_err, Ok) and ok_err.msg is not None:
        return ok_err.msg
    elif isinstance(ok_err, Err) and ok_err.err is not None:
        return ok_err.err
    else:
        return ''


def parse_response(xml):
    ''' FIXME: add description
    '''
    assert xml.tag == 'value'

    if xml.get('val') == 'good':
        return Ok(parse_value(xml[0]), None)
    elif xml.get('val') == 'fail':
        msg, loc = parse_error(xml)
        return Err(msg, loc, False)
    else:
        assert False, 'expected "good" or "fail" in <value>'


def parse_value(xml):
    ''' FIXME: add description
    '''
    if xml.tag == 'unit':
        return ()
    elif xml.tag == 'bool':
        if xml.get('val') == 'true':
            return True
        elif xml.get('val') == 'false':
            return False
        else:
            assert False, 'expected "true" or "false" in <bool>'
    elif xml.tag == 'string':
        return xml.text or ''
    elif xml.tag == 'int':
        return int(xml.text)
    elif xml.tag == 'state_id':
        return StateId(int(xml.get('val')))
    elif xml.tag == 'list':
        return [parse_value(c) for c in xml]
    elif xml.tag == 'option':
        if xml.get('val') == 'none':
            return Option(None)
        elif xml.get('val') == 'some':
            return Option(parse_value(xml[0]))
        else:
            assert False, 'expected "none" or "some" in <option>'
    elif xml.tag == 'pair':
        return tuple(parse_value(c) for c in xml)
    elif xml.tag == 'union':
        if xml.get('val') == 'in_l':
            return Inl(parse_value(xml[0]))
        elif xml.get('val') == 'in_r':
            return Inr(parse_value(xml[0]))
        else:
            assert False, 'expected "in_l" or "in_r" in <union>'
    elif xml.tag == 'option_state':
        sync, depr, name, value = map(parse_value, xml)
        return OptionState(sync, depr, name, value)
    elif xml.tag == 'option_value':
        return OptionValue(parse_value(xml[0]))
    elif xml.tag == 'status':
        path, proofname, allproofs, proofnum = map(parse_value, xml)
        return Status(path, proofname, allproofs, proofnum)
    elif xml.tag == 'goals':
        return Goals(*map(parse_value, xml))
    elif xml.tag == 'goal':
        return Goal(*map(parse_value, xml))
    elif xml.tag == 'evar':
        return Evar(*map(parse_value, xml))
    elif xml.tag == 'xml' or xml.tag == 'richpp':
        return ''.join(xml.itertext())


def parse_error(xml):
    ''' FIXME: add description
    '''
    loc_s = int(xml.get('loc_s', -1))
    loc_e = int(xml.get('loc_e', -1))

    return ''.join(xml.itertext()), (loc_s, loc_e)


def build(tag, val=None, children=()):
    ''' FIXME: add description
    '''
    attribs = {'val': val} if val is not None else {}

    xml = ET.Element(tag, attribs)
    xml.extend(children)

    return xml


def encode_call(name, arg):
    ''' FIXME: add description
    '''
    return build('call', name, [encode_value(arg)])


def encode_value(v):
    ''' FIXME: add description
    '''
    if v == ():
        return build('unit')
    elif isinstance(v, bool):
        xml = build('bool', str(v).lower())
        xml.text = str(v)
        return xml
    elif isinstance(v, (str, unicode)):
        xml = build('string')
        xml.text = v
        return xml
    elif isinstance(v, int):
        xml = build('int')
        xml.text = str(v)
        return xml
    elif isinstance(v, StateId):
        return build('state_id', str(v.id))
    elif isinstance(v, list):
        return build('list', None, [encode_value(c) for c in v])
    elif isinstance(v, Option):
        xml = build('option')
        if v.val is not None:
            xml.set('val', 'some')
            xml.append(encode_value(v.val))
        else:
            xml.set('val', 'none')
        return xml
    elif isinstance(v, Inl):
        return build('union', 'in_l', [encode_value(v.val)])
    elif isinstance(v, Inr):
        return build('union', 'in_r', [encode_value(v.val)])
    # N.B. 'tuple' check must be at the end because it overlaps with () and
    # namedtuples.
    elif isinstance(v, tuple):
        return build('pair', None, [encode_value(c) for c in v])
    else:
        assert False, "unrecognized type in encode_value: {}".format(type(v))


def escape(cmd):
    ''' FIXME: add description
    '''
    return cmd.replace(b'&nbsp;', b' ') \
              .replace(b'&apos;', b'\'') \
              .replace(b'&#40;', b'(') \
              .replace(b'&#41;', b')')


class Coqtop(object):
    ''' FIXME: add description
    '''

    def __init__(self):
        ''' FIXME: add description
        '''
        self.coqtop = None
        self.states = []
        self.state_id = None
        self.root_state = None
        self.out_q = queue.Queue()

    # Coqtop Interface #
    def start(self, *args):
        ''' FIXME: add description
        '''
        if self.running():
            self.stop()

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
            result = self.call('Init', Option(None), use_timeout=True)
            if not isinstance(result, Ok):
                return False

            self.root_state = result.val
            self.state_id = result.val

            return True
        except OSError:
            return False

    def stop(self):
        ''' FIXME: add description
        '''
        if self.running():
            try:
                self.coqtop.terminate()
                self.coqtop.communicate()
            except OSError:
                pass
            self.coqtop = None

    def advance(self, cmd, encoding='utf-8'):
        ''' FIXME: add description
        '''
        # Python 2 will throw an error if unicode is in 'cmd' unless we decode it,
        # but in Python 3 'cmd' is 'str' not 'bytes' and doesn't need to be decoded
        if isinstance(cmd, bytes):
            cmd = cmd.decode(encoding)

        result = self.call('Add',
                           ((cmd, -1),
                            (self.cur_state(), True)),
                           encoding, use_timeout=True)
        goals = self.goals()

        if result is None:
            return (result, '')

        msgs = [get_message(res) for res in (result, goals) if res is not None]

        if result is None or isinstance(result, Err):
            return (result, msgs)

        if isinstance(goals, Err):
            # Reset position to get goals back
            self.call('Edit_at', self.state_id)
            return (goals, msgs)

        self.states.append(self.state_id)
        self.state_id = result.val[0]

        # Coqtop refuses to show queries in a script so catch the error and
        # resend as a query
        try:
            if 'Query commands should not' in result.msg:
                result = self.query(cmd, encoding)
                return (result, [] if result.msg is None else [result.msg])
        except (AttributeError, TypeError):
            pass

        return (result, msgs)

    def rewind(self, step=1):
        ''' FIXME: add description
        '''
        if step > len(self.states):
            self.state_id = self.root_state
        else:
            self.state_id = self.states[-step]
            self.states = self.states[0:-step]

        return self.call('Edit_at', self.state_id)

    def query(self, cmd, encoding='utf-8'):
        ''' FIXME: add description
        '''
        # See 'advance' for an explanation of this
        if isinstance(cmd, bytes):
            cmd = cmd.decode(encoding)

        return self.call('Query',
                         (cmd, self.cur_state()),
                         encoding, use_timeout=True)

    def goals(self):
        ''' FIXME: add description
        '''
        return self.call('Goal', (), use_timeout=True)

    # Interacting with Coqtop #
    def call(self, name, arg, encoding='utf-8', use_timeout=False):
        ''' FIXME: add description
        '''
        self.empty_out()

        xml = encode_call(name, arg)
        msg = ET.tostring(xml, encoding)
        self.send_cmd(msg)

        if use_timeout:
            timeout = int(vim.eval('b:coq_timeout'))
            if timeout == 0:
                timeout = None
        else:
            timeout = None

        # The got_response event tells the timeout_thread that get_answer()
        # returned normally, while timed_out will be set by timeout_thread if
        # time runs out without receiving a response.
        got_response = threading.Event()
        timed_out = threading.Event()
        timeout_thread = threading.Thread(target=self.timeout_thread,
                                          args=(timeout, got_response, timed_out))
        timeout_thread.daemon = True

        timeout_thread.start()
        response = self.get_answer()

        got_response.set()
        if timed_out.is_set():
            response = TIMEOUT_ERR

        return response

    def timeout_thread(self, timeout, got_response, timed_out):
        ''' FIXME: add description
        '''
        if not got_response.wait(timeout):
            self.coqtop.send_signal(signal.SIGINT)
            timed_out.set()

    def get_answer(self):
        ''' FIXME: add description
        '''
        data = []

        while True:
            try:
                data.append(self.out_q.get())
                elt = ET.fromstring(b'<coqtoproot>' + escape(b''.join(data)) + b'</coqtoproot>')

                keep_waiting = True
                msg_node = []

                # Wait for a 'value' node and store any 'message' nodes
                for child in elt:
                    if child.tag == 'value':
                        keep_waiting = False
                        val_node = child
                    if child.tag == 'message':
                        msg_node.append(parse_value(child.find('richpp')))

                if keep_waiting:
                    continue
                else:
                    val = parse_response(val_node)
                    if msg_node != []:
                        if isinstance(val, Ok):
                            return Ok(val.val, '\n\n'.join(msg_node))
                    return val
            except ET.ParseError:
                continue
            except queue.Empty:
                return None

    def empty_out(self):
        ''' FIXME: add description '''
        while not self.out_q.empty():
            try:
                self.out_q.get_nowait()
            except queue.Empty:
                break

    # TODO: figure out why python 2 needs os.read vs stdout.read but 3 doesnt'
    def capture_out(self):
        ''' FIXME: add description '''
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
        ''' FIXME: add description '''
        fd = self.coqtop.stderr.fileno()

        while True:
            try:
                print(os.read(fd, 0x10000).decode())
                # print(os.read(fd, 0x10000).decode(), file=sys.stderr)
            except (AttributeError, OSError, ValueError):
                # Coqtop died
                return

    def send_cmd(self, cmd):
        ''' FIXME: add description
        '''
        self.coqtop.stdin.write(cmd)
        self.coqtop.stdin.flush()

    # Current State #
    def running(self):
        ''' FIXME: add description
        '''
        return self.coqtop is not None

    def cur_state(self):
        ''' FIXME: add description
        '''
        if self.states == []:
            return self.root_state
        return self.state_id
