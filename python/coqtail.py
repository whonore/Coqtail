# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Classes and functions for managing goal and info panels and Coqtop interfaces."""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import re
import sys
from collections import deque

# Mypy doesn't know where to find these modules
import vim  # type: ignore
import vimbufsync  # type: ignore

import coqtop as CT

# For Mypy
try:
    from typing import (
        Any,
        Callable,
        Deque,
        Dict,
        Generator,
        List,
        Optional,
        Mapping,
        Sequence,
        Text,
        Tuple,
    )
except ImportError:
    pass

vimbufsync.check_version("0.1.0", who="coqtail")


# Error Messages #
def fail(err):
    # type: (Exception) -> None
    """Print an error and stop Coqtail."""
    print(err, file=sys.stderr)
    vim.command("call coqtail#Stop()")


def unexpected(response, where):
    # type: (Any, str) -> None
    """Print a debugging error about an unexpected response."""
    print(
        "Coqtail received unexpected response {} in {}".format(response, where),
        file=sys.stderr,
    )


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
        endpoints - A stack of the end positions of the sentences sent to Coqtop
                    (grows to the right)
        send_queue - A queue of the sentences to send to Coqtop
        error_at - The position of the last error
        info_msg - The text to display in the info panel
        goal_msg - The text to display in the goal panel
        """
        self.saved_sync = None
        self.endpoints = []  # type: List[Tuple[int, int]]
        self.send_queue = deque([])  # type: Deque[Mapping[str, Tuple[int, int]]]
        self.error_at = None  # type: Optional[Tuple[Tuple[int, int], Tuple[int, int]]]
        self.info_msg = []  # type: List[Text]
        self.goal_msg = []  # type: List[Text]

        self.reset_color()

    def sync(self):
        # type: () -> None
        """Check if the buffer has been updated and rewind Coqtop if so."""
        curr_sync = vimbufsync.sync()

        if self.saved_sync is None or curr_sync.buf() != self.saved_sync.buf():
            self._reset()
        else:
            line, col = self.saved_sync.pos()
            self.rewind_to(line - 1, col)

        self.saved_sync = curr_sync

    # Coqtop Interface #
    def start(self, version, *args):
        # type: (Text, *Text) -> None
        """Start a new Coqtop instance."""
        success = False
        errmsg = ["Failed to launch Coq"]

        def set_done():
            # type: () -> None
            """Callback to be triggered when Coqtop is done executing."""
            self.coqtop_done = True

        try:
            self.coqtop = CT.Coqtop(version, set_done)
            success = self.call_and_wait(self.coqtop.start, *args, timeout=self.timeout)
        except ValueError as e:
            errmsg.append(str(e))

        if not success:
            print(". ".join(errmsg), file=sys.stderr)

    def stop(self):
        # type: () -> None
        """Stop Coqtop and reset variables."""
        if self.coqtop is not None:
            self.coqtop.stop()
        self._reset()
        self.coqtop = None
        self.log = ""

    def step(self, steps=1):
        # type: (int) -> None
        """Advance Coq by 'steps' sentences."""
        self.sync()

        if steps < 1:
            return

        # Get the location of the last '.'
        line, col = self.endpoints[-1] if self.endpoints != [] else (0, 0)

        to_send = _get_message_range(vim.current.buffer, (line, col))
        for _ in range(steps):
            if to_send is None:
                break
            eline, ecol = to_send["stop"]
            self.send_queue.append(to_send)
            to_send = _get_message_range(vim.current.buffer, (eline, ecol + 1))

        self.send_until_fail()

    def rewind(self, steps=1):
        # type: (int) -> None
        """Rewind Coq by 'steps' sentences."""
        assert self.coqtop is not None

        if steps < 1 or self.endpoints == []:
            return

        try:
            success, extra_steps = self.call_and_wait(self.coqtop.rewind, steps)
        except CT.CoqtopError as e:
            fail(e)
            return

        if success:
            self.endpoints = self.endpoints[: -(steps + extra_steps)]
        else:
            unexpected(success, "rewind()")

        self.refresh()

    def to_line(self, line):
        # type: (int) -> None
        """Advance/rewind Coq to the given position."""
        self.sync()

        if line == 0:
            # If no line was given then use the cursor's position
            line, col = vim.current.window.cursor
        else:
            # Otherwise, use the last column in the line
            col = len(vim.current.buffer[line - 1])
        line -= 1

        # Get the location of the last '.'
        sline, scol = self.endpoints[-1] if self.endpoints != [] else (0, 0)

        # Check if should rewind or advance
        if (line, col) < (sline, scol):
            self.rewind_to(line, col + 2)
        else:
            to_send = _get_message_range(vim.current.buffer, (sline, scol))
            while to_send is not None and to_send["stop"] <= (line, col):
                eline, ecol = to_send["stop"]
                self.send_queue.append(to_send)
                to_send = _get_message_range(vim.current.buffer, (eline, ecol + 1))

            self.send_until_fail()

    def to_top(self):
        # type: () -> None
        """Rewind to the beginning of the file."""
        self.rewind_to(0, 1)

    def query(self, *args):
        # type: (*Text) -> None
        """Forward Coq query to Coqtop interface."""
        _, msg = self.do_query(" ".join(args))
        self.show_info(msg)

    def jump_to_end(self):
        # type: () -> None
        """Move the cursor to the end of the Coq checked section."""
        # Get the location of the last '.'
        if self.endpoints != []:
            line, col = self.endpoints[-1]
        else:
            line, col = (0, 1)

        vim.current.window.cursor = (line + 1, col)

    def make_match(self, ty):
        # type: (Text) -> None
        """Create a "match" statement template for the given inductive type."""
        assert self.coqtop is not None

        try:
            success, msg = self.call_and_wait(
                self.coqtop.mk_cases, ty, encoding=self.encoding
            )
        except CT.CoqtopError as e:
            fail(e)
            return

        match = ["match _ with"]
        if success:
            for con in msg:
                match.append("| {} => _".format(" ".join(con)))
            match.append("end")

            # Decide whether to insert here or on new line
            if vim.current.line.strip() == "":
                mode = "i"
            else:
                mode = "o"

            # Insert text and indent
            vim.command("normal {}{}".format(mode, "\n".join(match)))
            vim.command("normal ={}k".format(len(match) - 1))
        else:
            print("Cannot make cases for {}".format(ty), file=sys.stderr)

    # Helpers #
    def send_until_fail(self):
        # type: () -> None
        """Send all sentences in 'send_queue' until an error is encountered."""
        assert self.coqtop is not None

        first = True
        while self.send_queue:
            self.reset_color()

            to_send = self.send_queue.popleft()
            message = _between(to_send["start"], to_send["stop"])

            try:
                no_comments, com_pos = _strip_comments(message)
                success, msg, err_loc = self.call_and_wait(
                    self.coqtop.dispatch,
                    no_comments,
                    encoding=self.encoding,
                    timeout=self.timeout,
                )
            except CT.CoqtopError as e:
                fail(e)
                return

            if msg != "":
                self.show_info(msg, first)
                first = False

            if success:
                line, col = to_send["stop"]
                self.endpoints.append((line, col + 1))
            else:
                self.send_queue.clear()

                # Highlight error location
                loc_s, loc_e = err_loc
                if loc_s == loc_e == -1:
                    self.error_at = (to_send["start"], to_send["stop"])
                else:
                    line, col = to_send["start"]
                    loc_s, loc_e = _adjust_offset(loc_s, loc_e, com_pos)
                    sline, scol = _pos_from_offset(col, message, loc_s)
                    eline, ecol = _pos_from_offset(col, message, loc_e)
                    self.error_at = ((line + sline, scol), (line + eline, ecol))

        # Clear info if no messages
        if first:
            self.show_info("")
        self.refresh()

    def rewind_to(self, line, col):
        # type: (int, int) -> None
        """Rewind to a specific location."""
        # Count the number of endpoints after the specified location
        steps_too_far = sum(pos >= (line, col) for pos in self.endpoints)
        self.rewind(steps_too_far)

    def do_query(self, query):
        # type: (Text) -> Tuple[bool, Text]
        """Execute a query and return the reply."""
        assert self.coqtop is not None

        # Ensure that the query ends in '.'
        if not query.endswith("."):
            query += "."

        try:
            success, msg, _ = self.call_and_wait(
                self.coqtop.dispatch,
                query,
                in_script=False,
                encoding=self.encoding,
                timeout=self.timeout,
            )
        except CT.CoqtopError as e:
            fail(e)
            return False, str(e)

        return success, msg

    def qual_name(self, target):
        # type: (Text) -> Optional[Tuple[Text, Text]]
        """Find the fully qualified name of 'target' using 'Locate'."""
        success, locate = self.do_query("Locate {}.".format(target))
        if not success:
            return None

        # Join lines that start with whitespace to the previous line
        locate = re.sub(r"\n +", " ", locate)

        # Choose first match from 'Locate' since that is the default in the
        # current context
        match = locate.split("\n")[0]
        if "No object of basename" in match:
            return None
        else:
            # Look for alias
            alias = re.search(r"\(alias of (.*)\)", match)
            if alias is not None:
                # Found an alias, search again using that
                return self.qual_name(alias.group(1))

            info = match.split()
            # Special case for Module Type
            if info[0] == "Module" and info[1] == "Type":
                tgt_type = "Module Type"  # type: Text
                qual_tgt = info[2]
            else:
                tgt_type, qual_tgt = info[:2]

        return qual_tgt, tgt_type

    def find_lib(self, lib):
        # type: (Text) -> Optional[Text]
        """Find the path to the .v file corresponding to the libary 'lib'."""
        success, locate = self.do_query("Locate Library {}.".format(lib))
        if not success:
            return None

        path = re.search(r"file\s+(.*)\.vo", locate)
        return path.group(1) if path is not None else None

    def find_qual(self, qual_tgt, tgt_type):
        # type: (Text, Text) -> Optional[Tuple[Text, Text]]
        """Find the Coq file containing the qualified name 'qual_tgt'."""
        qual_comps = qual_tgt.split(".")
        base_name = qual_comps[-1]

        # If 'qual_comps' starts with Top or 'tgt_type' is Variable then
        # 'qual_tgt' is defined in the current file
        if qual_comps[0] == "Top" or tgt_type == "Variable":
            return self.filename, base_name

        # Find the longest prefix of 'qual_tgt' that matches a logical path in
        # 'path_map'
        for end in range(-1, -len(qual_comps), -1):
            path = self.find_lib(".".join(qual_comps[:end]))
            if path is not None:
                return path + ".v", base_name

        return None

    def find_def(self, target):
        # type: (Text) -> Optional[Tuple[Text, List[Text]]]
        """Create patterns to jump to the definition of 'target'."""
        # Get the fully qualified version of 'target'
        qual = self.qual_name(target)
        if qual is None:
            return None
        qual_tgt, tgt_type = qual

        # Find what file the definition is in and what type it is
        tgt = self.find_qual(qual_tgt, tgt_type)
        if tgt is None:
            return None
        tgt_file, tgt_name = tgt

        return tgt_file, get_searches(tgt_type, tgt_name)

    def next_bullet(self):
        # type: () -> Optional[Text]
        """Check the bullet expected for the next subgoal."""
        success, show = self.do_query("Show.")
        if not success:
            return None

        bmatch = re.search(r'(?:bullet |unfocusing with ")([-+*}]+)', show)
        return bmatch.group(1) if bmatch is not None else None

    def call_and_wait(self, func, *args, **kwargs):
        # type: (Callable[..., Generator[Any, bool, None]], *Any, **Any) -> Any
        """Call a Coqtop function and wait for it to finish."""
        func_iter = func(*args, **kwargs)

        # Start function
        next(func_iter)
        while True:
            # Wait for Coqtop
            stopped = self.wait_coqtop()
            # Reset b:coqtail_coqtop_done
            self.coqtop_done = False
            # Respond with whether user interrupted
            ret = func_iter.send(stopped)
            # If 'ret' is None then Coqtop is being called again, otherwise it
            # is the final result
            if ret is not None:
                return ret

    # Goals and Infos #
    def refresh(self):
        # type: () -> None
        """Refresh the goal and info panels."""
        goals, info = self.get_goals()
        if info != "":
            self.show_info(info, False)
        if goals is not None:
            self.show_goal(self.pp_goals(goals))
        else:
            self.show_goal("")
        self.reset_color()

    def get_goals(self):
        # type: () -> Tuple[Optional[Tuple[List[Any], List[Any], List[Any], List[Any]]], Text]
        """Get the current goals."""
        assert self.coqtop is not None

        try:
            success, msg, goals = self.call_and_wait(
                self.coqtop.goals, timeout=self.timeout
            )
        except CT.CoqtopError as e:
            fail(e)
            return None, str(e)

        if not success:
            unexpected(success, "get_goals()")
            return None, ""

        return goals, msg

    def pp_goals(self, goals):
        # type: (Tuple[List[Any], List[Any], List[Any], List[Any]]) -> Text
        """Pretty print the goals."""
        fg, bg, shelved, given_up = goals
        bg_joined = [pre + post for pre, post in bg]

        ngoals = len(fg)
        nhidden = len(bg_joined[0]) if bg_joined != [] else 0
        nshelved = len(shelved)
        nadmit = len(given_up)

        # Information about number of remaining goals
        plural = "" if ngoals == 1 else "s"
        goal_info = "{} subgoal{}".format(ngoals, plural)
        hidden_info = (
            "{} unfocused at this level".format(nhidden) if nhidden > 0 else ""
        )
        extra_info = " ".join(
            s
            for s in (
                "{} shelved".format(nshelved) if nshelved > 0 else "",
                "{} admitted".format(nadmit) if nadmit > 0 else "",
            )
            if s != ""
        )
        if hidden_info != "":
            goal_info += " ({})".format(hidden_info)

        msg = [goal_info]
        if extra_info != "":
            msg.append(extra_info + "\n")
        else:
            msg[0] += "\n"

        # When a subgoal is finished
        if ngoals == 0:
            next_goal = None
            for bgs in bg_joined:
                if bgs != []:
                    next_goal = bgs[0]
                    break

            if next_goal is not None:
                bullet = self.next_bullet()
                bullet_info = ""
                if bullet is not None:
                    if bullet == "}":
                        bullet_info = "end this goal with '}'"
                    else:
                        bullet_info = "use bullet '{}'".format(bullet)

                next_info = "\nNext goal"
                if bullet_info != "":
                    next_info += " ({})".format(bullet_info)
                next_info += ":\n"

                msg += [next_info, next_goal.ccl]
            else:
                msg.append("All goals completed.")

        for idx, goal in enumerate(fg):
            if idx == 0:
                # Print the environment only for the current goal
                msg += goal.hyp

            msg.append("\n{:=>25} ({} / {})\n".format("", idx + 1, ngoals))
            msg.append(goal.ccl)

        return "\n".join(msg)

    def restore_panel(self, buf, msg):
        # type: (Any, List[Text]) -> None
        """Set the text in 'buf' to 'msg' while preserving the current window's view."""
        # Switch windows and save the view
        cur_win = vim.current.window
        vim.current.window = self.bufwin(buf)
        view = vim.eval("winsaveview()")

        # Update buffer text
        vim.current.buffer[:] = msg

        # Restore the view and switch to original window
        vim.command("call winrestview({})".format(view))
        vim.command("call coqtail#ScrollPanel()")
        vim.current.window = cur_win

    def show_goal(self, msg=None):
        # type: (Optional[Text]) -> None
        """Update the goal panel."""
        if msg is not None:
            self.goal_msg = msg.split("\n")
        if self.goal_msg == [] or self.goal_msg == [""]:
            self.goal_msg = ["No goals."]
        self.restore_panel(self.panel("goal"), self.goal_msg)

    def show_info(self, msg=None, reset=True):
        # type: (Optional[Text], bool) -> None
        """Update the info panel."""
        if msg is not None:
            info = msg.split("\n")
            if reset:
                self.info_msg = info
            else:
                self.info_msg += [u""] + info
        self.restore_panel(self.panel("info"), self.info_msg)

    def reset_color(self):
        # type: () -> None
        """Recolor sections."""
        vim.command("call coqtail#ClearHighlight()")

        # Recolor
        if self.endpoints != []:
            line, col = self.endpoints[-1]
            self.matchadd(
                "coqtail_checked",
                "CoqtailChecked",
                _make_matcher((0, 0), (line + 1, col)),
            )

        if self.send_queue:
            if self.endpoints != []:
                sline, scol = self.endpoints[-1]
            else:
                sline, scol = (0, -1)

            to_send = self.send_queue[0]
            eline, ecol = to_send["stop"]
            self.matchadd(
                "coqtail_sent",
                "CoqtailSent",
                _make_matcher((sline, scol + 1), (eline + 1, ecol)),
            )

        if self.error_at is not None:
            (sline, scol), (eline, ecol) = self.error_at
            self.matchadd(
                "coqtail_errors",
                "CoqtailError",
                _make_matcher((sline + 1, scol), (eline + 1, ecol)),
            )
            self.error_at = None

        vim.command("redraw")

    def splash(self, version):
        # type: (Text) -> None
        """Display the logo in the info panel."""
        # This is called before the panels are displayed so the window size is
        # actually half
        w = vim.current.window.width // 2
        h = vim.current.window.height // 2

        msg = [
            u"~~~~~~~~~~~~~~~~~~~~~~~",
            u"λ                     /",
            u" λ      Coqtail      / ",
            u"  λ   Wolf Honoré   /  ",
            u"   λ               /   ",
            u"    λ{}/    ".format(("Coq " + version).center(13)),
            u"     λ           /     ",
            u"      λ         /      ",
            u"       λ       /       ",
            u"        λ     /        ",
            u"         λ   /         ",
            u"          λ /          ",
            u"           ‖           ",
            u"           ‖           ",
            u"           ‖           ",
            u"          / λ          ",
            u"         /___λ         ",
        ]
        msg_maxw = max(len(line) for line in msg)
        msg = [line.center(w - msg_maxw // 2) for line in msg]

        top_pad = [u""] * ((h // 2) - (len(msg) // 2 + 1))

        self.info_msg = top_pad + msg

    def toggle_debug(self):
        # type: () -> None
        """Enable or disable logging of debug messages."""
        assert self.coqtop is not None

        log = self.coqtop.toggle_debug()
        if log is None:
            msg = "Debugging disabled."
            self.log = ""
        else:
            msg = "Debugging enabled. Log: {}.".format(log)
            self.log = log

        self.show_info(msg)

    # Vim Helpers #
    @property
    def encoding(self):
        # type: () -> str
        """Get the encoding or default to utf-8."""
        return vim.options["encoding"].decode("utf-8") or "utf-8"

    @property
    def timeout(self):
        # type: () -> int
        """Get the value of coq_timeout for this buffer."""
        # Mypy doesn't know type of vim variables
        return vim.current.buffer.vars["coqtail_timeout"]  # type: ignore

    @property
    def coqtop_done(self):
        # type: () -> bool
        """Check if Coqtop is done."""
        return bool(vim.current.buffer.vars["coqtail_coqtop_done"])

    @coqtop_done.setter
    def coqtop_done(self, done):
        # type: (bool) -> None
        """Set whether Coqtop is done."""
        vim.current.buffer.vars["coqtail_coqtop_done"] = int(done)

    @property
    def log(self):
        # type: () -> Text
        """Get the name of this buffer's debug log."""
        # Mypy doesn't know type of vim variables
        return vim.current.buffer.vars["coqtail_log_name"]  # type: ignore

    @log.setter
    def log(self, log):
        # type: (Text) -> None
        """Set the name of this buffer's debug log."""
        vim.current.buffer.vars["coqtail_log_name"] = log

    @property
    def filename(self):
        # type: () -> Text
        """Get the absolute path of this buffer's current Coq file."""
        return vim.eval("expand('%:p')")  # type: ignore

    @staticmethod
    def panel(name):
        # type: (str) -> Any
        """Get the goal or info panel for this buffer."""
        return vim.buffers[vim.current.buffer.vars["coqtail_panel_bufs"][name]]

    @staticmethod
    def bufwin(buf):
        # type: (Any) -> Any
        """Get the window that contains buf."""
        return vim.windows[int(vim.eval("bufwinnr({})".format(buf.number))) - 1]

    @staticmethod
    def matchadd(var, group, zone):
        # type: (str, str, str) -> None
        """Highlight 'zone' using 'group'."""
        vim.command("let b:{} = matchadd('{}', '{}')".format(var, group, zone))

    def wait_coqtop(self):
        # type: () -> bool
        """Wait for b:coqtail_coqtop_done to be set and report whether it was interrupted."""
        assert self.coqtop is not None

        stopped = False

        while True:
            try:
                vim.command("while !b:coqtail_coqtop_done | endwhile")
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
    auto_names = [
        ("Constructor", "Inductive", "Build_(.*)", 1),
        ("Constant", "Inductive", "(.*)_(ind|rect?)", 1),
    ]
    type_to_vernac = {
        "Inductive": ["(Co)?Inductive", "Variant", "Class", "Record"],
        "Constant": [
            "Definition",
            "Let",
            "(Co)?Fixpoint",
            "Function",
            "Instance",
            "Theorem",
            "Lemma",
            "Remark",
            "Fact",
            "Corollary",
            "Proposition",
            "Example",
            "Parameters?",
            "Axioms?",
            "Conjectures?",
        ],
        "Notation": ["Notation"],
        "Variable": ["Variables?", "Hypothes[ie]s", "Context"],
        "Ltac": ["Ltac"],
        "Module": ["Module"],
        "Module Type": ["Module Type"],
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
    search_name = "|".join(search_names)

    # What Vernacular command to look for
    search_vernac = "|".join(
        vernac for typ in search_types for vernac in type_to_vernac.get(typ, [])
    )

    return [
        r"<({})>\s*\zs<({})>".format(search_vernac, search_name),
        r"<({})>".format(search_name),
    ]


# Finding Start and End of Coq Chunks #
def _adjust_offset(start, end, com_pos):
    # type: (int, int, List[List[int]]) -> Tuple[int, int]
    """Adjust offsets by taking the stripped comments into account."""
    # Move start and end forward by the length of the preceding comments
    for coff, clen in com_pos:
        if coff <= start:
            # N.B. Subtract one because comments are replaced by " ", not ""
            start += clen - 1
        if coff <= end:
            end += clen - 1

    return (start, end)


def _pos_from_offset(col, msg, offset):
    # type: (int, Text, int) -> Tuple[int, int]
    """Calculate the line and column of a given offset."""
    msg = msg[:offset]
    lines = msg.split("\n")

    line = len(lines) - 1
    col = len(lines[-1]) + (col if line == 0 else 0)

    return (line, col)


def _between(start, end):
    # type: (Tuple[int, int], Tuple[int, int]) -> Text
    """Return the text between a given start and end point."""
    sline, scol = start
    eline, ecol = end

    buf = vim.current.buffer

    lines = []  # type: List[Text]
    for idx, line in enumerate(buf[sline : eline + 1]):
        lcol = scol if idx == 0 else 0
        rcol = ecol + 1 if idx == eline - sline else len(line)
        lines.append(line[lcol:rcol])

    return "\n".join(lines)


def _get_message_range(lines, after):
    # type: (Sequence[str], Tuple[int, int]) -> Optional[Mapping[str, Tuple[int, int]]]
    """Return the next sentence to send after a given point."""
    end_pos = _find_next_sentence(lines, *after)

    if end_pos is not None:
        return {"start": after, "stop": end_pos}
    return None


def _find_next_sentence(lines, sline, scol):
    # type: (Sequence[str], int, int) -> Optional[Tuple[int, int]]
    """Find the next sentence to send to Coq."""
    bullets = ("{", "}", "-", "+", "*")

    line, col = (sline, scol)
    while True:
        # Skip leading whitespace
        for line in range(sline, len(lines)):
            first_line = lines[line][col:].lstrip()
            if first_line.rstrip() != "":
                col += len(lines[line][col:]) - len(first_line)
                break

            col = 0
        else:  # break not reached, nothing left in the buffer but whitespace
            return None

        # Skip leading comments
        if first_line.startswith("(*"):
            com_end = _skip_comment(lines, line, col + 2)
            if com_end is None:
                return None

            sline, col = com_end
        elif first_line.startswith("*)"):
            # Unmatched end-comment
            return None
        else:
            break

    # Check if the first character of the sentence is a bullet
    if first_line[0] in bullets:
        # '-', '+', '*' can be repeated
        for c in first_line[1:]:
            if c in bullets[2:] and c == first_line[0]:
                col += 1
            else:
                break
        return (line, col)

    # Check if this is a bracketed goal selector
    if first_line[0].isdigit():
        state = "digit"
        selcol = col
        for c in first_line[1:]:
            if state == "digit" and c.isdigit():
                selcol += 1
            elif state == "digit" and c.isspace():
                state = "beforecolon"
                selcol += 1
            elif state == "digit" and c == ":":
                state = "aftercolon"
                selcol += 1
            elif state == "beforecolon" and c.isspace():
                selcol += 1
            elif state == "beforecolon" and c == ":":
                state = "aftercolon"
                selcol += 1
            elif state == "aftercolon" and c.isspace():
                selcol += 1
            elif state == "aftercolon" and c == "{":
                selcol += 1
                return (line, selcol)
            else:
                break

    # Otherwise, find an ending '.'
    return _find_dot_after(lines, line, col)


def _find_dot_after(lines, sline, scol):
    # type: (Sequence[str], int, int) -> Optional[Tuple[int, int]]
    """Find the next '.' after a given point."""
    max_line = len(lines)

    while sline < max_line:
        line = lines[sline][scol:]
        dot_pos = line.find(".")
        com_pos = line.find("(*")
        com_end_post = line.find("*)")
        str_pos = line.find('"')

        if com_pos == -1 and com_end_post != -1:
            # Unmatched end-comment
            return None

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
        elif line[dot_pos : dot_pos + 2] in (".", ". "):
            # Don't stop for '.' used in qualified name or for '..'
            return (sline, scol + dot_pos)
        elif line[dot_pos : dot_pos + 3] == "...":
            # But do allow '...'
            return (sline, scol + dot_pos + 2)
        elif line[dot_pos : dot_pos + 2] == "..":
            # Skip second '.'
            scol += dot_pos + 2
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
    return _skip_block(lines, sline, scol, "*)", "(*")


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
    # type: (Tuple[int, int], Tuple[int, int]) -> str
    """A wrapper function to call the appropriate _matcher function."""
    if start[0] == stop[0]:
        return _easy_matcher(start, stop)
    return _hard_matcher(start, stop)


def _easy_matcher(start, stop):
    # type: (Tuple[int, int], Tuple[int, Optional[int]]) -> str
    """Create a Vim match expression with the same start and end columns."""
    startl = startc = ""
    sline, scol = start
    eline, ecol = stop

    if sline > 0:
        startl = r"\%>{0}l".format(sline - 1)
    if scol > 0:
        startc = r"\%>{0}c".format(scol)

    start_match = startl + startc
    if ecol is not None:
        end_match = r"\%<{0}l\%<{1}c".format(eline + 1, ecol + 1)
    else:
        end_match = r"\%<{0}l".format(eline + 1)

    return start_match + end_match


def _hard_matcher(start, stop):
    # type: (Tuple[int, int], Tuple[int, int]) -> str
    """Create a Vim match expression with different start and end columns."""
    sline, scol = start
    eline, ecol = stop

    first_start = (sline, scol)
    first_stop = (sline, None)
    first_line = _easy_matcher(first_start, first_stop)

    mid_start = (sline + 1, 0)
    mid_stop = (eline - 1, None)
    middle = _easy_matcher(mid_start, mid_stop)

    last_start = (eline, 0)
    last_stop = (eline, ecol)
    last_line = _easy_matcher(last_start, last_stop)

    return r"{0}\|{1}\|{2}".format(first_line, middle, last_line)


# Misc #
def _strip_comments(msg):
    # type: (Text) -> Tuple[Text, List[List[int]]]
    """Remove all comments from 'msg'."""
    # N.B. Coqtop will ignore comments, but it makes it easier to inspect
    # commands in Coqtail (e.g. options in coqtop.do_option) if we remove
    # them.
    # N.B. Assumes comments are properly matched.
    nocom = []
    com_pos = []  # Remember comment offset and length
    off = 0
    nesting = 0

    while msg != "":
        start = msg.find("(*")
        end = msg.find("*)")
        if start == -1 and end == -1:
            # No comments left
            nocom.append(msg)
            break
        elif start != -1 and (start < end or end == -1):
            # New nested comment
            if nesting == 0:
                nocom.append(msg[:start])
                com_pos.append([off + start, 0])
            msg = msg[start + 2 :]
            off += start + 2
            nesting += 1
        elif end != -1 and (end < start or start == -1):
            # End of a comment
            msg = msg[end + 2 :]
            off += end + 2
            nesting -= 1
            if nesting == 0:
                com_pos[-1][1] = off - com_pos[-1][0]

    return " ".join(nocom), com_pos
