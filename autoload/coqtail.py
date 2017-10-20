# -*- coding: utf8 -*-
'''
File: coqtail.py
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

Description: Provides classes and functions for managing goals and info panels
and coqtop interfaces.
'''

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import vim

import os
import re
import sys
from collections import deque
from collections import defaultdict as ddict

import coqtop as CT
import vimbufsync

vimbufsync.check_version('0.1.0', who='coqtail')


# Error Messages #
def fail(err):
    '''Print an error and stop Coqtail.'''
    print(err, file=sys.stderr)
    vim.command('call coqtail#Stop()')


def unexpected(response, where):
    '''Print a debugging error about an unexpected response.'''
    print("Coqtail receieved unexpected response {} in {}".format(response, where),
          file=sys.stderr)


class Coqtail(object):
    '''Manage coqtop interfaces and goal and info buffers for each Coq file.'''

    def __init__(self):
        '''Initialize variables.'''
        self.coqtop = None
        self._reset()

    def _reset(self):
        '''Reset variables to initial state.'''
        self.saved_sync = None
        self.endpoints = []
        self.send_queue = deque([])
        self.error_at = None
        self.info_msg = ''
        self.goal_msg = 'No goals.'

        self.reset_color()

    def sync(self):
        '''Check if buffer has been updated and rewind coqtop if so.'''
        curr_sync = vimbufsync.sync()

        if self.saved_sync is None or curr_sync.buf() != self.saved_sync.buf():
            self._reset()
        else:
            (line, col) = self.saved_sync.pos()
            self.rewind_to(line - 1, col)

        self.saved_sync = curr_sync

    def check_coq(self):
        '''Check if coqtop is running.'''
        if not self.coqtop.running():
            print('Coq is not running.', file=sys.stderr)
            return False

        return True

    # Coqtop Interface #
    def start(self, *args):
        '''Start a new coqtop instance.'''
        self.coqtop = CT.Coqtop()
        if not self.coqtop.start(*args, timeout=get_timeout()):
            print('Failed to launch Coq', file=sys.stderr)
            raise vim.error('coq_start_fail')

    def stop(self):
        '''Stop coqtop and reset variables.'''
        self.coqtop.stop()
        self._reset()

    def next(self):
        '''Advance Coq by one step.'''
        if not self.check_coq():
            return

        self.sync()

        # Get the location of the last '.'
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]
        else:
            (line, col) = (0, 0)

        to_send = _get_message_range((line, col))
        if to_send is None:
            return

        self.send_queue.append(to_send)
        self.send_until_fail()

    def rewind(self, steps=1):
        '''Rewind Coq by 'steps' steps.'''
        if not self.check_coq():
            return

        if steps < 1 or self.endpoints == []:
            return

        response = self.coqtop.rewind(steps)
        if response is None:
            fail('Coq seems to have stopped running.')
            return

        if isinstance(response, CT.Ok):
            self.endpoints = self.endpoints[:-steps]
        else:
            unexpected(response, 'rewind()')

        self.refresh()

    def to_cursor(self):
        '''Advance Coq to the cursor position.'''
        if not self.check_coq():
            return

        self.sync()

        (cline, ccol) = vim.current.window.cursor
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]
        else:
            (line, col) = (0, 0)

        # Check if should rewind or advance.
        if cline < line or (cline == line and ccol < col):
            self.rewind_to(cline - 1, ccol)
        else:
            to_send = _get_message_range((line, col))
            while to_send is not None and to_send['stop'] <= (cline - 1, ccol):
                (eline, ecol) = to_send['stop']
                self.send_queue.append(to_send)
                to_send = _get_message_range((eline, ecol + 1))

            self.send_until_fail()

    def to_top(self):
        '''Rewind to the beginning of the file.'''
        self.rewind_to(0, 1)

    def query(self, *args):
        '''Forward Coq query to coqtop interface.'''
        if not self.check_coq():
            return

        self.clear_info()

        encoding = vim.eval('&encoding') or 'utf-8'
        message = ' '.join(args)

        response = self.coqtop.query(message, encoding)
        if response is None:
            fail('Coq seems to have stopped running.')
            return

        if isinstance(response, CT.Ok):
            if response.msg is not None:
                self.info_msg = response.msg
        elif isinstance(response, CT.Err):
            self.info_msg = response.err
        else:
            unexpected(response, 'query()')

        self.show_info()

    def jump_to_end(self):
        '''Move the cursor to the end of the Coq checked section.'''
        # Get the location of the last '.'
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]
        else:
            (line, col) = (0, 1)

        vim.current.window.cursor = (line + 1, col)

    def find_def(self, target):
        '''Locate where the current word is defined and jump to it.'''
        if not self.check_coq():
            return

        # 'Locate target' returns the kind of object (Constant, Inductive, etc)
        # and the logical path to where it is defined
        encoding = vim.eval('&encoding') or 'utf-8'
        message = "Locate {}.".format(target)

        response = self.coqtop.query(message, encoding)
        if response is None:
            fail('Coq seems to have stopped running.')
            return

        if isinstance(response, CT.Ok):
            if response.msg is not None:
                locs = self.parse_locate(response.msg)

                # Ask user to choose which definition to find.
                if len(locs) == 1:
                    ltype, lfile, lname = locs[0]
                else:
                    choices = ["{}: {} in {}".format(n + 1,
                                                     ltype,
                                                     lfile if lfile != 'Coq' else 'Coq StdLib')
                               for n, (ltype, lfile, _) in enumerate(locs)
                               if ltype is not None]
                    choices.insert(0, 'Choose one of these definitions:')

                    idx = int(vim.eval('inputlist(' + str(choices) + ')'))
                    if 1 <= idx <= len(locs):
                        ltype, lfile, lname = locs[idx - 1]
                    else:
                        print('Invalid choice.', file=sys.stderr)
                        return

                if lfile == 'Coq':
                    print("{} is part of the Coq StdLib".format(target))
                elif ltype == 'Err':
                    print("Failed to locate {}:\n{}".format(target, lfile),
                          file=sys.stderr)
                else:
                    if lfile != 'Top':
                        vim.command('hide argedit ' + lfile)

                    if lname is not None:
                        searches = get_searches(ltype, lname)

                        for search in searches:
                            try:
                                vim.command(r"0/\v{}".format(search))
                                break
                            except vim.error:
                                pass
        elif isinstance(response, CT.Err):
            print(response.err)
        else:
            unexpected(response, 'find_def()')

    # Helpers #
    def send_until_fail(self):
        '''Send all chunks in 'send_queue' until an error is encountered.'''
        msgs = []
        encoding = vim.eval('&fileencoding') or 'utf-8'

        while self.send_queue:
            self.reset_color()
            vim.command('redraw')

            to_send = self.send_queue.popleft()
            message = _between(to_send['start'], to_send['stop'])

            (response, res_msgs) = self.coqtop.advance(message,
                                                       encoding,
                                                       timeout=get_timeout())
            if response is None:
                fail('Coq seems to have stopped running.')
                return

            if isinstance(response, CT.Ok):
                (line, col) = to_send['stop']
                self.endpoints.append((line, col + 1))

                if len(response.val) > 1 and isinstance(response.val[1], tuple):
                    msgs.append(response.val[1][1])
                msgs += res_msgs
            else:
                self.send_queue.clear()

                if isinstance(response, CT.Err):
                    msgs += res_msgs

                    # Highlight error location
                    if response.loc is not None:
                        loc_s, loc_e = response.loc
                        if loc_s == loc_e == -1:
                            self.error_at = (to_send['start'], to_send['stop'])
                            (sline, scol) = to_send['start']
                            (eline, ecol) = to_send['stop']
                        else:
                            (line, col) = to_send['start']
                            (sline, scol) = _pos_from_offset(col, message, loc_s)
                            (eline, ecol) = _pos_from_offset(col, message, loc_e)
                            self.error_at = ((line + sline, scol), (line + eline, ecol))
                else:
                    unexpected(response, 'send_until_fail()')

        self.clear_info()
        self.info_msg = '\n\n'.join(msg for msg in msgs if msg != '')

        self.refresh()

    def rewind_to(self, line, col):
        '''Rewind to a specific location.'''
        if not self.check_coq():
            return

        # Count the number of endpoints after the specified location.
        steps_too_far = sum(pos > (line, col) for pos in self.endpoints)
        self.rewind(steps_too_far)

    def parse_locate(self, msg):
        '''Parse the response from 'Locate target' and return the physical path
        to the file where it is defined, plus the type of object and name.
        '''
        # Build a map from logical to physical paths using LoadPath
        encoding = vim.eval('&encoding') or 'utf-8'
        message = 'Print LoadPath.'

        response = self.coqtop.query(message, encoding, timeout=get_timeout())
        if response is None:
            fail('Coq seems to have stopped running.')
            return

        if isinstance(response, CT.Ok):
            paths = response.msg.split()[2:]
            logic = paths[::2]
            physic = paths[1::2]

            path_map = {log: phy for log, phy in zip(logic, physic)}
        else:
            return [('Err', 'Failed to query LoadPath.', None)]

        # Return the location and type of the target
        locs = []
        for loc in msg.split('\n'):
            # Skip extra information included in Locate response
            if loc.strip().startswith('('):
                continue

            loc = loc.split()
            ltype = loc[0]

            # Target not found
            if ltype == 'No':
                break

            where = loc[1].split('.')
            if where[0] == 'Coq':
                locs.append((ltype, 'Coq', None))
            elif where[0] == 'Top' or ltype == 'Variable':
                lfile = vim.eval('expand("%:p")')
                locs.append((ltype, 'Top', where[-1]))
            else:
                for end in range(-1, -len(where), -1):
                    logpath = '.'.join(where[:end])
                    if logpath in path_map:
                        libpath = path_map[logpath]
                        lfile = os.path.abspath(os.path.join(libpath, where[end])) + '.v'
                        lname = where[-1]
                        locs.append((ltype, lfile, lname))
                        break
                else:
                    # Could be a module name inside a module definition
                    lfile = vim.eval('expand("%:p")')
                    locs.append((ltype, 'Top', where[-1]))

        if locs == []:
            return [('Err', msg, None)]
        return locs

    # Goals and Infos #
    def refresh(self):
        '''Refresh the goals and info panels.'''
        self.show_goal()
        self.show_info()
        self.reset_color()

    def show_goal(self):
        '''Display the current goals.'''
        response = self.coqtop.goals(timeout=get_timeout())
        if response is None:
            fail('Coq seems to have stopped running.')
            return

        if isinstance(response, CT.Err):
            unexpected(response, 'show_goal()')
            return

        if response.msg is not None:
            self.info_msg = response.msg

        if response.val.val is None:
            self.goal_msg = 'No goals.'
        else:
            goals = response.val.val.fg
            ngoals = len(goals)
            plural = '' if ngoals == 1 else 's'
            msg = ["{} subgoal{}\n".format(ngoals, plural)]

            for idx, goal in enumerate(goals):
                if idx == 0:
                    # Print the environment only for the current goal
                    for hyp in goal.hyp:
                        msg.append(hyp)

                msg.append('\n' + '=' * 25 + " ({} / {})\n".format(idx + 1, ngoals))
                msg.append(goal.ccl)

            self.goal_msg = '\n'.join(msg)

        self.restore_goal()

    def restore_goal(self):
        '''Restore the last-displayed goals.'''
        bufn = int(vim.eval('b:goal_buf'))
        goal_buf = vim.buffers[bufn]
        del goal_buf[:]

        goal_buf.append(self.goal_msg.split('\n'))

    def show_info(self):
        '''Display the info_msg buffer in the info panel.'''
        bufn = int(vim.eval('b:info_buf'))
        info_buf = vim.buffers[bufn]
        del info_buf[:]

        lines = [line for line in self.info_msg.split('\n')]
        info_buf.append(lines)

    def clear_info(self):
        '''Clear the info panel.'''
        self.info_msg = ''
        self.show_info()

    def hide_color(self):
        '''Clear highlighting.'''
        # Clear checked highlighting
        if int(vim.eval('b:checked')) != -1:
            vim.command('call matchdelete(b:checked)')
            vim.command('let b:checked = -1')

        if int(vim.eval('b:sent')) != -1:
            vim.command('call matchdelete(b:sent)')
            vim.command('let b:sent = -1')

        if int(vim.eval('b:errors')) != -1:
            vim.command('call matchdelete(b:errors)')
            vim.command('let b:errors = -1')

    def reset_color(self):
        '''Recolor sections.'''
        self.hide_color()

        # Recolor
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]

            start = {'line': 0, 'col': 0}
            stop = {'line': line + 1, 'col': col}
            zone = _make_matcher(start, stop)
            vim.command("let b:checked = matchadd('CheckedByCoq', '{}')".format(zone))

        if self.send_queue:
            if self.endpoints != []:
                (sline, scol) = self.endpoints[-1]
            else:
                (sline, scol) = (0, -1)

            to_send = self.send_queue[0]
            (eline, ecol) = to_send['stop']

            start = {'line': sline, 'col': scol + 1}
            stop = {'line': eline + 1, 'col': ecol}
            zone = _make_matcher(start, stop)
            vim.command("let b:sent = matchadd('SentToCoq', '{}')".format(zone))

        if self.error_at is not None:
            ((sline, scol), (eline, ecol)) = self.error_at

            start = {'line': sline + 1, 'col': scol}
            stop = {'line': eline + 1, 'col': ecol}
            zone = _make_matcher(start, stop)
            vim.command("let b:errors = matchadd('CoqError', '{}')".format(zone))

            self.error_at = None

    def splash(self, version):
        '''Display the logo in the info panel.'''
        # This is called before the panels are displayed so the window size is
        # actually half
        w = vim.current.window.width // 2
        h = vim.current.window.height // 2

        msg = [u'~~~~~~~~~~~~~~~~~~~~~~~',
               u'λ                     /',
               u' λ      Coqtail      / ',
               u'  λ   Wolf Honoré   /  ',
               u'   λ               /   ',
               u"    λ{}/    ".format(('Coq ' + version).center(13)),
               u'     λ           /     ',
               u'      λ         /      ',
               u'       λ       /       ',
               u'        λ     /        ',
               u'         λ   /         ',
               u'          λ /          ',
               u'           ‖           ',
               u'           ‖           ',
               u'           ‖           ',
               u'          / λ          ',
               u'         /___λ         ']
        msg_maxw = max(len(line) for line in msg)
        msg = [line.center(w - msg_maxw // 2) for line in msg]

        top_pad = [''] * ((h // 2) - (len(msg) // 2 + 1))

        self.info_msg = '\n'.join(top_pad + msg)


# Vim Helpers #
def get_timeout():
    '''Get the current timeout value.'''
    return int(vim.eval('b:coq_timeout'))


# Searching for Coq Definitions #
# TODO: could search more intelligently by searching only within relevant
# section/module, or sometimes by looking at the type (for constructors for
# example, or record projections)
def get_searches(ltype, lname):
    '''Construct a search expression given an object type and name.'''
    auto_names = [('Constructor', 'Inductive', 'Build_(.*)', 1),
                  ('Constant', 'Inductive', '(.*)_(ind|rect?)', 1)]
    searches = []
    type_to_vernac = {
        'Inductive': ['Inductive', 'Class', 'Record'],
        'Constant': ['Definition', 'Fixpoint', 'Function', 'Instance', 'Fact',
                     'Remark', 'Lemma', 'Corollary', 'Theorem', 'Axiom',
                     'Conjecture'],
        'Notation': ['Notation'],
        'Variable': ['Variables?', 'Context'],
        'Ltac': ['Ltac'],
        'Module': ['Module']
    }

    # Look for some implicitly generated names
    search_name = [lname]
    search_type = [ltype]
    for from_type, to_type, pat, grp in auto_names:
        if ltype == from_type and re.match(pat, lname) is not None:
            search_name.append(re.match(pat, lname).groups(grp)[0])
            search_type.append(to_type)
    search_name = '|'.join(search_name)

    # What Vernacular command to look for
    search_vernac = '|'.join(vernac
                             for typ in search_type
                             for vernac in type_to_vernac.get(typ, ''))

    searches.append(r"<({})>\s*<({})>".format(search_vernac, search_name))
    searches.append(r"<({})>".format(search_name))

    return searches


# Finding Start and End of Coq Chunks #
# From here on is largely copied from Coquille
def _pos_from_offset(col, msg, offset):
    '''Calculate the line and column of a given offset.'''
    msg = msg[:offset]
    lines = msg.split('\n')

    line = len(lines) - 1
    col = len(lines[-1]) + (col if line == 0 else 0)

    return (line, col)


def _between(start, end):
    '''Return the text between a given start and end point.'''
    (sline, scol) = start
    (eline, ecol) = end

    buf = vim.current.buffer

    lines = []
    for idx, line in enumerate(buf[sline:eline + 1]):
        lcol = scol if idx == 0 else 0
        rcol = ecol + 1 if idx == eline - sline else len(line)
        lines.append(line[lcol:rcol])

    return '\n'.join(lines)


def _get_message_range(after):
    '''Return the next chunk to send after a given point.'''
    end_pos = _find_next_chunk(*after)

    if end_pos is not None:
        return {'start': after, 'stop': end_pos}
    return None


def _find_next_chunk(sline, scol):
    '''Find the next chunk to send to Coq.'''
    buf = vim.current.buffer
    blen = len(buf)
    bullets = ['{', '}', '-', '+', '*']

    (line, col) = (sline, scol)
    while True:
        # Skip leading whitespace
        for line in range(sline, blen):
            first_line = buf[line][col:].lstrip()
            if first_line.rstrip() != '':
                col += len(buf[line][col:]) - len(first_line)
                break

            col = 0
        else:  # break not reached, nothing left in the buffer but whitespace
            return None

        # Skip leading comments
        if first_line.startswith('(*'):
            com_end = _skip_comment(line, col + 2)
            if not com_end:
                return None

            (sline, col) = com_end
        else:
            break

    # Check if the first character of the chunk is a bullet
    if first_line[0] in bullets:
        return (line, col + 1)

    # Otherwise, find an ending '.'
    return _find_dot_after(line, col)


def _find_dot_after(sline, scol):
    '''Find the next '.' after a given point.'''
    buf = vim.current.buffer
    if sline >= len(buf):
        return None

    line = buf[sline][scol:]
    dot_pos = line.find('.')
    com_pos = line.find('(*')
    str_pos = line.find('"')

    if com_pos == -1 and dot_pos == -1 and str_pos == -1:
        # Nothing on this line
        return _find_dot_after(sline + 1, 0)
    elif dot_pos == -1 or (0 <= com_pos < dot_pos) or (0 <= str_pos < dot_pos):
        if str_pos == -1 or (0 <= com_pos < str_pos):
            # We see a comment opening before the next '.'
            com_end = _skip_comment(sline, scol + com_pos + 2)
            if not com_end:
                return

            return _find_dot_after(*com_end)
        else:
            # We see a string starting before the next '.'
            str_end = _skip_str(sline, scol + str_pos + 1)
            if not str_end:
                return

            return _find_dot_after(*str_end)
    elif line[dot_pos:dot_pos + 2] in ('.', '. '):
        # Don't stop for '.' used in qualified name or for '..'
        return (sline, scol + dot_pos)
    elif line[dot_pos:dot_pos + 3] == '...':
        # But do allow '...'
        return (sline, scol + dot_pos + 2)
    else:
        return _find_dot_after(sline, scol + dot_pos + 1)


def _skip_str(sline, scol):
    '''Skip the next block contained in " ".'''
    return _skip_block(sline, scol, '"')


def _skip_comment(sline, scol):
    '''Skip the next block contained in (* *).'''
    return _skip_block(sline, scol, '*)', '(*', 1)


def _skip_block(sline, scol, estr, sstr=None, nesting=1):
    '''A generic function to skip the next block contained in sstr estr.'''
    if nesting == 0:
        return (sline, scol)

    buf = vim.current.buffer
    if sline >= len(buf):
        return None

    line = buf[sline][scol:]
    blk_end = line.find(estr)
    if sstr is not None:
        blk_start = line.find(sstr)
    else:
        blk_start = -1

    if blk_end != -1 and (blk_end < blk_start or blk_start == -1):
        # Found an end and no new start
        return _skip_block(sline, scol + blk_end + len(estr),
                           estr, sstr, nesting - 1)
    elif blk_start != -1:
        # Found a new start
        return _skip_block(sline, scol + blk_start + len(sstr),
                           estr, sstr, nesting + 1)
    else:
        # Nothing on this line
        return _skip_block(sline + 1, 0, estr, sstr, nesting)


# Region Highlighting #
def _make_matcher(start, stop):
    '''A wrapper function to call the appropriate _matcher function.'''
    if start['line'] == stop['line']:
        return _easy_matcher(start, stop)
    return _hard_matcher(start, stop)


def _easy_matcher(start, stop):
    '''Create a single-line Vim match expression.'''
    startl = ''
    startc = ''

    if start['line'] > 0:
        startl = r"\%>{0}l".format(start['line'] - 1)
    if start['col'] > 0:
        startc = r"\%>{0}c".format(start['col'])

    start_match = "{0}{1}".format(startl, startc)
    if stop['col'] is not None:
        end_match = r"\%<{0}l\%<{1}c".format(stop['line'] + 1, stop['col'] + 1)
    else:
        end_match = r"\%<{0}l".format(stop['line'] + 1)

    return ''.join((start_match, end_match))


def _hard_matcher(start, stop):
    '''Create a multi-line Vim match expression.'''
    first_start = {'line': start['line'], 'col': start['col']}
    first_stop = {'line': start['line'], 'col': None}
    first_line = _easy_matcher(first_start, first_stop)

    mid_start = {'line': start['line'] + 1, 'col': 0}
    mid_stop = {'line': stop['line'] - 1, 'col': None}
    middle = _easy_matcher(mid_start, mid_stop)

    last_start = {'line': stop['line'], 'col': 0}
    last_stop = {'line': stop['line'], 'col': stop['col']}
    last_line = _easy_matcher(last_start, last_stop)

    return r"{0}\|{1}\|{2}".format(first_line, middle, last_line)


# Method Dispatch #
# A mapping from buffer numbers to Coqtail classes
bufmap = ddict(Coqtail)


# Calls the corresponding method on the current buffer.
def sync(*args):
    bufmap[vim.current.buffer].sync(*args)


def start(*args):
    bufmap[vim.current.buffer].start(*args)


def stop(*args):
    bufmap[vim.current.buffer].stop(*args)


def next(*args):
    bufmap[vim.current.buffer].next(*args)


def rewind(*args):
    bufmap[vim.current.buffer].rewind(*args)


def to_cursor(*args):
    bufmap[vim.current.buffer].to_cursor(*args)


def to_top(*args):
    bufmap[vim.current.buffer].to_top(*args)


def query(*args):
    bufmap[vim.current.buffer].query(*args)


def jump_to_end(*args):
    bufmap[vim.current.buffer].jump_to_end(*args)


def find_def(*args):
    bufmap[vim.current.buffer].find_def(*args)


def hide_color(*args):
    bufmap[vim.current.buffer].hide_color(*args)


def reset_color(*args):
    bufmap[vim.current.buffer].reset_color(*args)


def restore_goal(*args):
    bufmap[vim.current.buffer].restore_goal(*args)


def show_info(*args):
    bufmap[vim.current.buffer].show_info(*args)


def splash(*args):
    bufmap[vim.current.buffer].splash(*args)
