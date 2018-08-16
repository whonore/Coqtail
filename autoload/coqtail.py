# -*- coding: utf8 -*-
"""
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
and Coqtop interfaces.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import vim

import os
import re
import sys
from collections import deque, defaultdict as ddict

import coqtop as CT
import vimbufsync

# For Mypy
try:
    from typing import (Any, Callable, Deque, Dict, Generator, List, Optional,
                        Mapping, Sequence, Text, Tuple)
except ImportError:
    pass

vimbufsync.check_version('0.1.0', who='coqtail')


# Error Messages #
def fail(err):
    # type: (Exception) -> None
    """Print an error and stop Coqtail."""
    print(err, file=sys.stderr)
    vim.command('call coqtail#Stop()')


def unexpected(response, where):
    # type: (Any, str) -> None
    """Print a debugging error about an unexpected response."""
    print("Coqtail received unexpected response {} in {}"
          .format(response, where),
          file=sys.stderr)


class Coqtail(object):
    """Manage Coqtop interfaces and goal and info buffers for each Coq file."""
    _bufmap = {}  # type: Dict[int, Coqtail]

    def __new__(cls):
        # type: () -> Coqtail
        """Create one Coqtail instance per Vim buffer."""
        num = vim.current.buffer.number
        # Return same instance if already exists, otherwise create new instance
        return Coqtail._bufmap.get(num, super(Coqtail, cls).__new__(cls))

    def __init__(self):
        # type: () -> None
        """Initialize variables."""
        num = vim.current.buffer.number
        # Only initialize if this is a new instance
        if num not in Coqtail._bufmap:
            Coqtail._bufmap[num] = self
            self.coqtop = None  # type: Optional[CT.Coqtop]
            self._reset()

    def _reset(self):
        # type: () -> None
        """Reset variables to initial state.

        saved_sync - The last vimbufsync BufferRevision object
        endpoints - A stack of the end positions of the lines sent to Coqtop
                    (grows to the right)
        send_queue - A queue of the lines to send to Coqtop
        error_at - The position of the last error
        info_msg - The text to display in the info panel
        goal_msg - The text to display in the goal panel
        """
        self.saved_sync = None
        self.endpoints = []  # type: List[Tuple[int, int]]
        self.send_queue = deque([])  # type: Deque[Mapping[str, Tuple[int, int]]]
        self.error_at = None  # type: Optional[Tuple[Tuple[int, int], Tuple[int, int]]]
        self.info_msg = ''  # type: Text
        self.goal_msg = 'No goals.'  # type: Text

        self.reset_color()

    def sync(self):
        # type: () -> None
        """Check if buffer has been updated and rewind Coqtop if so."""
        curr_sync = vimbufsync.sync()

        if self.saved_sync is None or curr_sync.buf() != self.saved_sync.buf():
            self._reset()
        else:
            (line, col) = self.saved_sync.pos()
            self.rewind_to(line - 1, col)

        self.saved_sync = curr_sync

    # Coqtop Interface #
    def start(self, version, *args):
        # type: (Text, *Text) -> None
        """Start a new Coqtop instance."""
        success = False
        errmsg = ['Failed to launch Coq']

        def set_done():
            # type: () -> None
            """Callback to be triggered when Coqtop is done executing."""
            vim.current.buffer.vars['coqtop_done'] = 1

        try:
            self.coqtop = CT.Coqtop(version, set_done)
            success = self.call_and_wait(self.coqtop.start, *args,
                                         timeout=self.timeout)
        except ValueError as e:
            errmsg.append(str(e))

        if not success:
            print('. '.join(errmsg), file=sys.stderr)

    def stop(self):
        # type: () -> None
        """Stop Coqtop and reset variables."""
        if self.coqtop is not None:
            self.coqtop.stop()
        self._reset()
        self.coqtop = None

    def step(self):
        # type: () -> None
        """Advance Coq by one step."""
        self.sync()

        # Get the location of the last '.'
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]
        else:
            (line, col) = (0, 0)

        to_send = _get_message_range(vim.current.buffer, (line, col))
        if to_send is None:
            return

        self.send_queue.append(to_send)
        self.send_until_fail()

    def rewind(self, steps=1):
        # type: (int) -> None
        """Rewind Coq by 'steps' steps."""
        assert self.coqtop is not None

        if steps < 1 or self.endpoints == []:
            return

        try:
            success, extra_steps = self.call_and_wait(self.coqtop.rewind, steps)
        except CT.CoqtopError as e:
            fail(e)
            return

        if success:
            self.endpoints = self.endpoints[:-(steps + extra_steps)]
        else:
            unexpected(success, 'rewind()')

        self.refresh()

    def to_cursor(self):
        # type: () -> None
        """Advance Coq to the cursor position."""
        self.sync()

        (cline, ccol) = vim.current.window.cursor
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]
        else:
            (line, col) = (0, 0)

        # Check if should rewind or advance
        if cline - 1 < line or (cline - 1 == line and ccol < col):
            self.rewind_to(cline - 1, ccol + 2)
        else:
            to_send = _get_message_range(vim.current.buffer, (line, col))
            while to_send is not None and to_send['stop'] <= (cline - 1, ccol):
                (eline, ecol) = to_send['stop']
                self.send_queue.append(to_send)
                to_send = _get_message_range(vim.current.buffer,
                                             (eline, ecol + 1))

            self.send_until_fail()

    def to_top(self):
        # type: () -> None
        """Rewind to the beginning of the file."""
        self.rewind_to(0, 1)

    def query(self, *args):
        # type: (*Text) -> None
        """Forward Coq query to Coqtop interface."""
        assert self.coqtop is not None

        self.clear_info()

        message = ' '.join(args)

        try:
            _, self.info_msg, _ = self.call_and_wait(self.coqtop.dispatch,
                                                     message,
                                                     in_script=False,
                                                     encoding=self.encoding)
        except CT.CoqtopError as e:
            fail(e)
            return

        self.show_info()

    def jump_to_end(self):
        # type: () -> None
        """Move the cursor to the end of the Coq checked section."""
        # Get the location of the last '.'
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]
        else:
            (line, col) = (0, 1)

        vim.current.window.cursor = (line + 1, col)

    def find_def(self, target):
        # type: (Text) -> None
        """Locate where the current word is defined and jump to it."""
        # Get the fully qualified version of 'target'
        qual_info = self.qual_name(target)

        if qual_info is not None:
            qual_tgt, tgt_type = qual_info
            tgt_file, tgt_name = self.log_to_phy(qual_tgt, tgt_type)

            if tgt_file is None:
                print("Failed to locate {}: {}".format(target, tgt_name),
                      file=sys.stderr)
                return

            if tgt_file == 'Coq':
                print("{} is part of the Coq StdLib".format(tgt_name))
            else:
                # Open 'tgt_file' if it is not the current file
                if tgt_file != vim.eval('expand("%:p")'):
                    vim.command('hide argedit ' + tgt_file)

                # Try progressively broader searches
                for search in get_searches(tgt_type, tgt_name):
                    try:
                        vim.command(r"0/\v{}".format(search))
                        break
                    except vim.error:
                        pass

    def make_match(self, ty):
        # type: (Text) -> None
        """Create a "match" statement template for the given inductive type."""
        assert self.coqtop is not None

        try:
            success, msg = self.call_and_wait(self.coqtop.mk_cases, ty,
                                              encoding=self.encoding)
        except CT.CoqtopError as e:
            fail(e)
            return

        match = ['match _ with']
        if success:
            for con in msg:
                match.append("| {} => _".format(' '.join(con)))
            match.append('end')

            # Decide whether to insert here or on new line
            if vim.current.line.strip() == '':
                mode = 'i'
            else:
                mode = 'o'

            # Insert text and indent
            vim.command("normal {}{}".format(mode, '\n'.join(match)))
            vim.command("normal ={}k".format(len(match) - 1))
        else:
            print("Cannot make cases for {}".format(ty), file=sys.stderr)

    # Helpers #
    def send_until_fail(self):
        # type: () -> None
        """Send all chunks in 'send_queue' until an error is encountered."""
        assert self.coqtop is not None

        msgs = []

        while self.send_queue:
            self.reset_color()
            vim.command('redraw')

            to_send = self.send_queue.popleft()
            message = _between(to_send['start'], to_send['stop'])

            try:
                success, msg, err_loc = self.call_and_wait(self.coqtop.dispatch,
                                                           message,
                                                           encoding=self.encoding,
                                                           timeout=self.timeout)
            except CT.CoqtopError as e:
                fail(e)
                return

            msgs.append(msg)
            if success:
                (line, col) = to_send['stop']
                self.endpoints.append((line, col + 1))
            else:
                self.send_queue.clear()

                # Highlight error location
                loc_s, loc_e = err_loc
                if loc_s == loc_e == -1:
                    self.error_at = (to_send['start'], to_send['stop'])
                    (sline, scol) = to_send['start']
                    (eline, ecol) = to_send['stop']
                else:
                    (line, col) = to_send['start']
                    (sline, scol) = _pos_from_offset(col, message, loc_s)
                    (eline, ecol) = _pos_from_offset(col, message, loc_e)
                    self.error_at = ((line + sline, scol),
                                     (line + eline, ecol))

        self.clear_info()
        self.info_msg = '\n\n'.join(msg for msg in msgs if msg != '')

        self.refresh()

    def rewind_to(self, line, col):
        # type: (int, int) -> None
        """Rewind to a specific location."""
        # Count the number of endpoints after the specified location
        steps_too_far = sum(pos >= (line, col) for pos in self.endpoints)
        self.rewind(steps_too_far)

    def qual_name(self, target):
        # type: (Text) -> Optional[Tuple[Text, Text]]
        """Find the fully qualified name of 'target' using 'Locate'."""
        assert self.coqtop is not None

        message = "Locate {}.".format(target)

        try:
            success, res_msg, _ = self.call_and_wait(self.coqtop.dispatch,
                                                     message,
                                                     in_script=False,
                                                     encoding=self.encoding)
        except CT.CoqtopError as e:
            fail(e)
            return None

        if not success:
            print(res_msg)
            return None

        # Join lines that start with whitespace to the previous line
        res_msg = re.sub(r'\n +', ' ', res_msg)

        # Choose first match from 'Locate' since that is the default in the
        # current context
        qual_tgt = None
        match = res_msg.split('\n')[0]
        if 'No object of basename' in match:
            return None
        else:
            info = match.split()
            # Special case for Module Type
            if info[0] == 'Module' and info[1] == 'Type':
                tgt_type = 'Module Type'
                qual_tgt = info[2]
            else:
                tgt_type = info[0]
                qual_tgt = info[1]

            # Look for alias
            alias = re.search(r'\(alias of (.*)\)', match)
            if alias is not None:
                # Found an alias, search again using that
                return self.qual_name(alias.group(1))

        return qual_tgt, tgt_type

    def log_to_phy(self, qual_tgt, tgt_type):
        # type: (Text, Text) -> Tuple[Optional[Text], Text]
        """Find the Coq file corresponding to the logical path 'qual_tgt'."""
        assert self.coqtop is not None

        message = 'Print LoadPath.'

        try:
            success, loadpath, _ = self.call_and_wait(self.coqtop.dispatch,
                                                      message,
                                                      in_script=False,
                                                      encoding=self.encoding,
                                                      timeout=self.timeout)
        except CT.CoqtopError as e:
            fail(e)
            return None, str(e)

        # Build a map from logical to physical paths using LoadPath
        if success:
            path_map = ddict(list)  # type: Mapping[Text, List[Text]]
            paths = loadpath.split()[4:]
            logic = paths[::2]
            physic = paths[1::2]

            for log, phy in zip(logic, physic):
                path_map[log].append(phy)
        else:
            return None, 'Failed to query LoadPath.'

        # Return the location of the target
        loc = qual_tgt.split('.')
        tgt_name = loc[-1]
        if loc[0] == 'Top' or tgt_type == 'Variable':
            # If 'tgt_type' is Variable then 'target' is defined using
            # Variable or Context inside a section
            tgt_file = vim.eval('expand("%:p")')
        elif loc[0] == 'Coq':
            tgt_file = 'Coq'
        else:
            # Find the longest prefix of 'loc' that matches a logical path in
            # 'path_map'
            for end in range(-1, -len(loc), -1):
                logpath = '.'.join(loc[:end])

                if logpath in path_map:
                    libpaths = path_map[logpath]
                    coqfile = loc[end] + '.v'
                    tgt_files = [os.path.join(libpath, coqfile)
                                 for libpath in libpaths]
                    # TODO: maybe should return tgt_name = '.'.join(loc[end:])?
                    break
            else:
                # Check the empty (<>) logical path
                coqfile = loc[0] + '.v'
                tgt_files = [os.path.join(libpath, coqfile)
                             for libpath in path_map['<>']]

            # Convert to absolute path and filter out nonexistent files
            tgt_files = [f for f in (os.path.abspath(f) for f in tgt_files)
                         if os.path.isfile(f)]

            if tgt_files == []:
                return None, "Could not find {}".format(qual_tgt)

            # TODO: Currently assume only file is left. Maybe this is false
            if len(tgt_files) > 1:
                print("Warning: More than one file matches: {}"
                      .format(tgt_files))
            tgt_file = tgt_files[0]

        return tgt_file, tgt_name

    def call_and_wait(self, func, *args, **kwargs):
        # type: (Callable[..., Generator[Any, bool, None]], *Any, **Any) -> Any
        """Call a Coqtop function and wait for it to finish."""
        func_iter = func(*args, **kwargs)

        # Start function
        next(func_iter)
        while True:
            # Wait for Coqtop
            stopped = self.wait_coqtop()
            # Reset b:coqtop_done
            vim.current.buffer.vars['coqtop_done'] = 0
            # Respond with whether user interrupted
            ret = func_iter.send(stopped)
            # If 'ret' is None then Coqtop is being called again, otherwise it
            # is the final result
            if ret is not None:
                return ret

    # Goals and Infos #
    def refresh(self):
        # type: () -> None
        """Refresh the goals and info panels."""
        self.show_goal()
        self.show_info()
        self.reset_color()

    def show_goal(self):
        # type: () -> None
        """Display the current goals."""
        assert self.coqtop is not None

        try:
            success, msg, goals = self.call_and_wait(self.coqtop.goals,
                                                     timeout=self.timeout)
        except CT.CoqtopError as e:
            fail(e)
            return

        if not success:
            unexpected(success, 'show_goal()')
            return

        if msg != '':
            self.info_msg = msg

        if goals is None:
            self.goal_msg = 'No goals.'
        else:
            ngoals = len(goals)
            plural = '' if ngoals == 1 else 's'
            msg = ["{} subgoal{}\n".format(ngoals, plural)]

            for idx, goal in enumerate(goals):
                if idx == 0:
                    # Print the environment only for the current goal
                    msg += goal.hyp

                msg.append("\n{:=>25} ({} / {})\n".format('', idx + 1, ngoals))
                msg.append(goal.ccl)

            self.goal_msg = '\n'.join(msg)

        self.restore_goal()

    def restore_goal(self):
        # type: () -> None
        """Restore the last-displayed goals."""
        # Switch to goal window and save the view
        cur_win = vim.current.window
        vim.current.window = self.bufwin(self.goal_buf)
        view = vim.eval('winsaveview()')

        # Update goal buffer text
        vim.current.buffer[:] = self.goal_msg.split('\n')

        # Restore the view and switch to original window
        vim.command("call winrestview({})".format(view))
        vim.command("call coqtail#ScrollPanel({})"
                    .format(vim.current.buffer.number))
        vim.current.window = cur_win

    def show_info(self):
        # type: () -> None
        """Display the info_msg buffer in the info panel."""
        # Switch to info window and save the view
        cur_win = vim.current.window
        vim.current.window = self.bufwin(self.info_buf)
        view = vim.eval('winsaveview()')

        # Update info buffer text
        vim.current.buffer[:] = self.info_msg.split('\n')

        # Restore the view and switch to original window
        vim.command("call winrestview({})".format(view))
        vim.command("call coqtail#ScrollPanel({})"
                    .format(vim.current.buffer.number))
        vim.current.window = cur_win

    def clear_info(self):
        # type: () -> None
        """Clear the info panel."""
        self.info_msg = ''
        self.show_info()

    def reset_color(self):
        # type: () -> None
        """Recolor sections."""
        vim.command('call coqtail#ClearHighlight()')

        # Recolor
        if self.endpoints != []:
            (line, col) = self.endpoints[-1]

            start = {'line': 0, 'col': 0}
            stop = {'line': line + 1, 'col': col}
            zone = _make_matcher(start, stop)
            vim.command("let b:checked = matchadd('CheckedByCoq', '{}')"
                        .format(zone))

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
            vim.command("let b:sent = matchadd('SentToCoq', '{}')"
                        .format(zone))

        if self.error_at is not None:
            ((sline, scol), (eline, ecol)) = self.error_at

            start = {'line': sline + 1, 'col': scol}
            stop = {'line': eline + 1, 'col': ecol}
            zone = _make_matcher(start, stop)
            vim.command("let b:errors = matchadd('CoqError', '{}')"
                        .format(zone))

            self.error_at = None

    def splash(self, version):
        # type: (Text) -> None
        """Display the logo in the info panel."""
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

        top_pad = [u''] * ((h // 2) - (len(msg) // 2 + 1))

        self.info_msg = '\n'.join(top_pad + msg)

    # Vim Helpers #
    @property
    def encoding(self):
        # type: () -> str
        """Get the encoding or default to utf-8."""
        return vim.options['encoding'].decode('utf-8') or 'utf-8'

    @property
    def timeout(self):
        # type: () -> int
        """Get the value of coq_timeout for this buffer."""
        return vim.current.buffer.vars['coq_timeout']  # type: ignore

    @property
    def goal_buf(self):
        # type: () -> Any
        """Get this buffer's goal buffer."""
        return vim.buffers[vim.current.buffer.vars['goal_buf']]

    @property
    def info_buf(self):
        # type: () -> Any
        """Get this buffer's info buffer."""
        return vim.buffers[vim.current.buffer.vars['info_buf']]

    @staticmethod
    def bufwin(buf):
        # type: (Any) -> Any
        """Get the window that contains buf."""
        return vim.windows[int(vim.eval("bufwinnr({})".format(buf.number))) - 1]

    def wait_coqtop(self):
        # type: () -> bool
        """Wait for b:coqtop_done to be set and report whether it was
        interrupted."""
        assert self.coqtop is not None

        stopped = False

        while True:
            try:
                vim.command('while !b:coqtop_done | endwhile')
                break
            except KeyboardInterrupt:
                # Forward interrupt to Coqtop
                self.coqtop.interrupt()
                stopped = True

        return stopped


# Searching for Coq Definitions #
# TODO: could search more intelligently by searching only within relevant
# section/module, or sometimes by looking at the type (for constructors for
# example, or record projections)
def get_searches(tgt_type, tgt_name):
    # type: (Text, Text) -> List[Text]
    """Construct a search expression given an object type and name."""
    auto_names = [('Constructor', 'Inductive', 'Build_(.*)', 1),
                  ('Constant', 'Inductive', '(.*)_(ind|rect?)', 1)]
    searches = []  # type: List[Text]
    type_to_vernac = {
        'Inductive': ['Inductive', 'Class', 'Record'],
        'Constant': ['Definition', 'Fixpoint', 'Function', 'Instance', 'Fact',
                     'Remark', 'Lemma', 'Corollary', 'Theorem', 'Axiom',
                     'Conjecture', 'Let'],
        'Notation': ['Notation'],
        'Variable': ['Variables?', 'Context'],
        'Ltac': ['Ltac'],
        'Module': ['Module'],
        'Module Type': ['Module Type']
    }  # type: Mapping[Text, List[Text]]

    # Look for some implicitly generated names
    search_names = [tgt_name]
    search_types = [tgt_type]
    for from_type, to_type, pat, grp in auto_names:
        if tgt_type == from_type:
            match = re.match(pat, tgt_name)
            if match is not None:
                search_names.append(match.group(grp))
                search_types.append(to_type)
    search_name = '|'.join(search_names)

    # What Vernacular command to look for
    search_vernac = '|'.join(vernac
                             for typ in search_types
                             for vernac in type_to_vernac.get(typ, []))

    searches.append(r"<({})>\s*<({})>".format(search_vernac, search_name))
    searches.append(r"<({})>".format(search_name))

    return searches


# Finding Start and End of Coq Chunks #
# From here on is largely copied from Coquille
def _pos_from_offset(col, msg, offset):
    # type: (int, Text, int) -> Tuple[int, int]
    """Calculate the line and column of a given offset."""
    msg = msg[:offset]
    lines = msg.split('\n')

    line = len(lines) - 1
    col = len(lines[-1]) + (col if line == 0 else 0)

    return (line, col)


def _between(start, end):
    # type: (Tuple[int, int], Tuple[int, int]) -> Text
    """Return the text between a given start and end point."""
    (sline, scol) = start
    (eline, ecol) = end

    buf = vim.current.buffer

    lines = []  # type: List[Text]
    for idx, line in enumerate(buf[sline:eline + 1]):
        lcol = scol if idx == 0 else 0
        rcol = ecol + 1 if idx == eline - sline else len(line)
        lines.append(line[lcol:rcol])

    return '\n'.join(lines)


def _get_message_range(lines, after):
    # type: (Sequence[str], Tuple[int, int]) -> Optional[Mapping[str, Tuple[int, int]]]
    """Return the next chunk to send after a given point."""
    end_pos = _find_next_chunk(lines, *after)

    if end_pos is not None:
        return {'start': after, 'stop': end_pos}
    return None


def _find_next_chunk(lines, sline, scol):
    # type: (Sequence[str], int, int) -> Optional[Tuple[int, int]]
    """Find the next chunk to send to Coq."""
    bullets = ['{', '}', '-', '+', '*']

    (line, col) = (sline, scol)
    while True:
        # Skip leading whitespace
        for line in range(sline, len(lines)):
            first_line = lines[line][col:].lstrip()
            if first_line.rstrip() != '':
                col += len(lines[line][col:]) - len(first_line)
                break

            col = 0
        else:  # break not reached, nothing left in the buffer but whitespace
            return None

        # Skip leading comments
        if first_line.startswith('(*'):
            com_end = _skip_comment(lines, line, col + 2)
            if com_end is None:
                return None

            (sline, col) = com_end
        else:
            break

    # Check if the first character of the chunk is a bullet
    if first_line[0] in bullets:
        return (line, col)

    # Otherwise, find an ending '.'
    return _find_dot_after(lines, line, col)


def _find_dot_after(lines, sline, scol):
    # type: (Sequence[str], int, int) -> Optional[Tuple[int, int]]
    """Find the next '.' after a given point."""
    max_line = len(lines)

    while sline < max_line:
        line = lines[sline][scol:]
        dot_pos = line.find('.')
        com_pos = line.find('(*')
        str_pos = line.find('"')

        if com_pos == -1 and dot_pos == -1 and str_pos == -1:
            # Nothing on this line
            sline += 1
            scol = 0
        elif dot_pos == -1 or (0 <= com_pos < dot_pos) or (0 <= str_pos < dot_pos):
            if str_pos == -1 or (0 <= com_pos < str_pos):
                # We see a comment opening before the next '.'
                com_end = _skip_comment(lines, sline, scol + com_pos + 2)
                if com_end is None:
                    return None

                sline, scol = com_end
            else:
                # We see a string starting before the next '.'
                str_end = _skip_str(lines, sline, scol + str_pos + 1)
                if str_end is None:
                    return None

                sline, scol = str_end
        elif line[dot_pos:dot_pos + 2] in ('.', '. '):
            # Don't stop for '.' used in qualified name or for '..'
            return (sline, scol + dot_pos)
        elif line[dot_pos:dot_pos + 3] == '...':
            # But do allow '...'
            return (sline, scol + dot_pos + 2)
        else:
            scol += dot_pos + 1

    return None


def _skip_str(lines, sline, scol):
    # type: (Sequence[str], int, int) -> Optional[Tuple[int, int]]
    """Skip the next block contained in " "."""
    return _skip_block(lines, sline, scol, '"')


def _skip_comment(lines, sline, scol):
    # type: (Sequence[str], int, int) -> Optional[Tuple[int, int]]
    """Skip the next block contained in (* *)."""
    return _skip_block(lines, sline, scol, '*)', '(*')


def _skip_block(lines, sline, scol, estr, sstr=None):
    # type: (Sequence[str], int, int, str, Optional[str]) -> Optional[Tuple[int, int]]
    """A generic function to skip the next block contained in sstr estr."""
    nesting = 1
    max_line = len(lines)

    while nesting > 0:
        if sline >= max_line:
            return None

        line = lines[sline][scol:]
        blk_end = line.find(estr)
        if sstr is not None:
            blk_start = line.find(sstr)
        else:
            blk_start = -1

        if blk_end != -1 and (blk_end < blk_start or blk_start == -1):
            # Found an end and no new start
            scol += blk_end + len(estr)
            nesting -= 1
        elif blk_start != -1:
            # Found a new start
            # N.B. mypy complains that 'sstr' might be None, but it won't be if
            # 'blk_start' != -1
            assert sstr is not None
            scol += blk_start + len(sstr)
            nesting += 1
        else:
            # Nothing on this line
            sline += 1
            scol = 0

    return (sline, scol)


# Region Highlighting #
def _make_matcher(start, stop):
    # type: (Mapping[str, int], Mapping[str, int]) -> str
    """A wrapper function to call the appropriate _matcher function."""
    if start['line'] == stop['line']:
        return _easy_matcher(start, stop)
    return _hard_matcher(start, stop)


def _easy_matcher(start, stop):
    # type: (Mapping[str, int], Mapping[str, Optional[int]]) -> str
    """Create a single-line Vim match expression."""
    startl = ''
    startc = ''

    if start['line'] > 0:
        startl = r"\%>{0}l".format(start['line'] - 1)
    if start['col'] > 0:
        startc = r"\%>{0}c".format(start['col'])

    assert stop['line'] is not None
    start_match = "{0}{1}".format(startl, startc)
    if stop['col'] is not None:
        end_match = r"\%<{0}l\%<{1}c".format(stop['line'] + 1, stop['col'] + 1)
    else:
        end_match = r"\%<{0}l".format(stop['line'] + 1)

    return ''.join((start_match, end_match))


def _hard_matcher(start, stop):
    # type: (Mapping[str, int], Mapping[str, int]) -> str
    """Create a multi-line Vim match expression."""
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
