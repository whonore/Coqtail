# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Classes and functions for managing auxiliary panels and Coqtop interfaces."""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import json
import re
import threading
import time
from collections import defaultdict as ddict, deque
from itertools import islice

from six.moves import zip_longest
from six.moves.queue import Empty, Queue
from six.moves.socketserver import StreamRequestHandler, TCPServer, ThreadingMixIn

import coqtop as CT

# For Mypy
try:
    from typing import (
        Any,
        DefaultDict,
        Deque,
        Dict,
        List,
        Iterator,
        Optional,
        Mapping,
        Sequence,
        Text,
        Tuple,
    )
except ImportError:
    pass


# Error Messages #
def unexpected(response, where):
    # type: (Any, str) -> str
    """Create a debugging error about an unexpected response."""
    return "Coqtail received unexpected response {} in {}".format(response, where)


class UnmatchedError(Exception):
    """An unmatched comment or string was found."""

    def __init__(self, token, loc):
        # type: (Text, Tuple[int, int]) -> None
        super(UnmatchedError, self).__init__("Found unmatched {}.".format(token))
        line, col = loc
        self.range = (loc, (line, col + len(token)))


class NoDotError(Exception):
    """No more sentences were found."""


# Coqtail Server #
class Coqtail(object):
    """Manage Coqtop interfaces and auxiliary buffers for each Coq file."""

    def __init__(self, handler):
        # type: (CoqtailHandler) -> None
        """Initialize variables.

        coqtop - The Coqtop interface
        handler - The Vim interface
        oldchange - The previous number of changes to the buffer
        oldbuf - The buffer corresponding to oldchange
        endpoints - A stack of the end positions of the sentences sent to Coqtop
                    (grows to the right)
        send_queue - A queue of the sentences to send to Coqtop
        error_at - The position of the last error
        info_msg - The text to display in the info panel
        goal_msg - The text to display in the goal panel
        """
        self.coqtop = None  # type: Optional[CT.Coqtop]
        self.handler = handler
        self.oldchange = 0
        self.oldbuf = []  # type: List[Text]
        self.endpoints = []  # type: List[Tuple[int, int]]
        self.send_queue = deque()  # type: Deque[Mapping[str, Tuple[int, int]]]
        self.error_at = None  # type: Optional[Tuple[Tuple[int, int], Tuple[int, int]]]
        self.info_msg = []  # type: List[Text]
        self.goal_msg = []  # type: List[Text]

    def sync(self):
        # type: () -> Optional[str]
        """Check if the buffer has been updated and rewind Coqtop if so."""
        err = None
        newchange = self.changedtick
        if newchange != self.oldchange:
            newbuf = self.buffer

            if self.endpoints != []:
                eline, ecol = self.endpoints[-1]
                linediff = _find_diff(self.oldbuf, newbuf, eline + 1)
                if linediff is not None:
                    try:
                        coldiff = _find_diff(
                            self.oldbuf[linediff],
                            newbuf[linediff],
                            ecol if linediff == eline else None,
                        )
                    except IndexError:
                        linediff = len(newbuf) - 1
                        coldiff = len(newbuf[-1])
                    if coldiff is not None:
                        err = self.rewind_to(linediff, coldiff + 1)

            self.oldchange = newchange
            self.oldbuf = newbuf

        return err

    # Coqtop Interface #
    def start(self, version, coq_path, args):
        # type: (str, str, List[str]) -> Optional[str]
        """Start a new Coqtop instance."""
        success = False
        errmsg = ["Failed to launch Coq"]

        try:
            self.coqtop = CT.Coqtop(version)
            success = self.coqtop.start(coq_path, *args, timeout=self.timeout)
        except (ValueError, CT.CoqtopError) as e:
            errmsg.append(str(e))

        if not success:
            return ". ".join(errmsg)
        return None

    def stop(self):
        # type: () -> None
        """Stop Coqtop."""
        if self.coqtop is not None:
            self.coqtop.stop()

    def step(self, steps=1):
        # type: (int) -> Optional[str]
        """Advance Coq by 'steps' sentences."""
        self.sync()

        if steps < 1:
            return None

        # Get the location of the last '.'
        line, col = self.endpoints[-1] if self.endpoints != [] else (0, 0)

        unmatched = None
        for _ in range(steps):
            try:
                to_send = _get_message_range(self.buffer, (line, col))
            except UnmatchedError as e:
                unmatched = e
                break
            except NoDotError:
                break
            line, col = to_send["stop"]
            col += 1
            self.send_queue.append(to_send)

        failed_at, err = self.send_until_fail()
        if unmatched is not None and failed_at is None:
            # Only report unmatched if no other errors occured first
            self.set_info(str(unmatched), False)
            self.error_at = unmatched.range
            self.refresh(goals=False)

        return err

    def rewind(self, steps=1):
        # type: (int) -> Optional[str]
        """Rewind Coq by 'steps' sentences."""
        assert self.coqtop is not None

        if steps < 1 or self.endpoints == []:
            return None

        try:
            success, extra_steps = self.coqtop.rewind(steps)
        except CT.CoqtopError as e:
            return str(e)

        if not success:
            return unexpected(success, "rewind()")

        self.endpoints = self.endpoints[: -(steps + extra_steps)]
        self.error_at = None
        self.refresh()
        return None

    def to_line(self, line, col):
        # type: (int, int) -> Optional[str]
        """Advance/rewind Coq to the specified position."""
        self.sync()

        # Get the location of the last '.'
        eline, ecol = self.endpoints[-1] if self.endpoints != [] else (0, 0)

        # Check if should rewind or advance
        if (line, col) < (eline, ecol):
            return self.rewind_to(line, col + 2)
        else:
            unmatched = None
            while True:
                try:
                    to_send = _get_message_range(self.buffer, (eline, ecol))
                except UnmatchedError as e:
                    # Only report unmatched if it occurs after the desired position
                    if e.range[0] <= (line, col):
                        unmatched = e
                    break
                except NoDotError:
                    break
                if (line, col) < to_send["stop"]:
                    break
                eline, ecol = to_send["stop"]
                ecol += 1
                self.send_queue.append(to_send)

            failed_at, err = self.send_until_fail()
            if unmatched is not None and failed_at is None:
                # Only report unmatched if no other errors occured first
                self.set_info(str(unmatched), False)
                self.error_at = unmatched.range
                self.refresh(goals=False)

            return err

    def to_top(self):
        # type: () -> Optional[str]
        """Rewind to the beginning of the file."""
        return self.rewind_to(0, 1)

    def query(self, args):
        # type: (List[Text]) -> None
        """Forward Coq query to Coqtop interface."""
        _, msg = self.do_query(" ".join(args))

        self.set_info(msg)
        self.refresh(goals=False)

    def endpoint(self):
        # type: () -> Tuple[int, int]
        """Return the end of the Coq checked section."""
        # Get the location of the last '.'
        if self.endpoints != []:
            line, col = self.endpoints[-1]
        else:
            line, col = (0, 1)
        return (line + 1, col)

    # Helpers #
    def send_until_fail(self):
        # type: () -> Tuple[Optional[Tuple[int, int]], Optional[str]]
        """Send all sentences in 'send_queue' until an error is encountered."""
        assert self.coqtop is not None

        failed_at = None
        no_msgs = True
        self.error_at = None
        while self.send_queue:
            self.refresh(goals=False, force=False)
            to_send = self.send_queue.popleft()
            message = _between(self.buffer, to_send["start"], to_send["stop"])
            no_comments, com_pos = _strip_comments(message)

            try:
                success, msg, err_loc = self.coqtop.dispatch(
                    no_comments, encoding=self.encoding, timeout=self.timeout,
                )
            except CT.CoqtopError as e:
                return None, str(e)

            if msg != "":
                self.set_info(msg, no_msgs)
                no_msgs = False

            if success:
                line, col = to_send["stop"]
                self.endpoints.append((line, col + 1))
            else:
                self.send_queue.clear()
                failed_at = to_send["start"]

                # Highlight error location
                assert err_loc is not None
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
        if no_msgs:
            self.set_info("")
        self.refresh()
        return failed_at, None

    def rewind_to(self, line, col):
        # type: (int, int) -> Optional[str]
        """Rewind to a specific location."""
        # Count the number of endpoints after the specified location
        steps_too_far = sum(pos >= (line, col) for pos in self.endpoints)
        return self.rewind(steps_too_far)

    def do_query(self, query):
        # type: (Text) -> Tuple[bool, Text]
        """Execute a query and return the reply."""
        assert self.coqtop is not None

        # Ensure that the query ends in '.'
        if not query.endswith("."):
            query += "."

        try:
            success, msg, _ = self.coqtop.dispatch(
                query, in_script=False, encoding=self.encoding, timeout=self.timeout,
            )
        except CT.CoqtopError as e:
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

    # Goals and Infos #
    def refresh(self, goals=True, force=True):
        # type: (bool, bool) -> None
        """Refresh the auxiliary panels."""
        if goals:
            newgoals, newinfo = self.get_goals()
            if newinfo != "":
                self.set_info(newinfo, False)
            if newgoals is not None:
                self.set_goal(self.pp_goals(newgoals))
            else:
                self.set_goal("")
        self.handler.refresh(goals=goals, force=force)

    def get_goals(self):
        # type: () -> Tuple[Optional[Tuple[List[Any], List[Any], List[Any], List[Any]]], Text]
        """Get the current goals."""
        assert self.coqtop is not None

        try:
            success, msg, goals = self.coqtop.goals(timeout=self.timeout)
        except CT.CoqtopError as e:
            return None, str(e)

        if not success:
            return None, unexpected(success, "get_goals()")

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

    def set_goal(self, msg=None):
        # type: (Optional[Text]) -> None
        """Update the goal message."""
        if msg is not None:
            self.goal_msg = msg.split("\n")
        if self.goal_msg == [] or self.goal_msg == [""]:
            self.goal_msg = ["No goals."]

    def set_info(self, msg=None, reset=True):
        # type: (Optional[Text], bool) -> None
        """Update the info message."""
        if msg is not None:
            info = msg.split("\n")
            if reset or self.info_msg == [] or self.info_msg == [""]:
                self.info_msg = info
            else:
                self.info_msg += [u""] + info

    @property
    def highlights(self):
        # type: () -> Dict[str, Optional[str]]
        """Vim match patterns for highlighting."""
        matches = {
            "coqtail_checked": None,
            "coqtail_sent": None,
            "coqtail_error": None,
        }  # type: Dict[str, Optional[str]]

        if self.endpoints != []:
            line, col = self.endpoints[-1]
            matches["coqtail_checked"] = _make_matcher((0, 0), (line + 1, col))

        if self.send_queue:
            if self.endpoints != []:
                sline, scol = self.endpoints[-1]
            else:
                sline, scol = (0, -1)

            to_send = self.send_queue[0]
            eline, ecol = to_send["stop"]
            matches["coqtail_sent"] = _make_matcher(
                (sline, scol + 1), (eline + 1, ecol)
            )

        if self.error_at is not None:
            (sline, scol), (eline, ecol) = self.error_at
            matches["coqtail_error"] = _make_matcher(
                (sline + 1, scol), (eline + 1, ecol)
            )

        return matches

    def panels(self, goals=True):
        # type: (bool) -> Mapping[str, List[Text]]
        """The auxiliary panel content."""
        panels = {"info": self.info_msg}
        if goals:
            panels["goal"] = self.goal_msg
        return panels

    def splash(self, version, width, height):
        # type: (Text, int, int) -> None
        """Display the logo in the info panel."""
        msg = [
            u"~~~~~~~~~~~~~~~~~~~~~~~",
            u"λ                     /",
            u" λ      Coqtail      / ",
            u"  λ                 /  ",
            u"   λ{}/    ".format(("Coq " + version).center(15)),
            u"    λ             /    ",
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
        msg = [line.center(width - msg_maxw // 2) for line in msg]

        top_pad = [u""] * ((height // 2) - (len(msg) // 2 + 1))

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

        self.set_info(msg)
        self.refresh(goals=False)

    # Vim Helpers #
    @property
    def encoding(self):
        # type: () -> str
        """Vim's encoding."""
        # TODO async: need ensure_str?
        return self.handler.vimexpr("&encoding")  # type: ignore[no-any-return]

    @property
    def timeout(self):
        # type: () -> int
        """The value of coq_timeout for this buffer."""
        return self.handler.vimvar("coqtail_timeout")  # type: ignore[no-any-return]

    @property
    def changedtick(self):
        # type: () -> int
        """The value of changedtick for this buffer."""
        return self.handler.vimvar("changedtick")  # type: ignore

    @property
    def log(self):
        # type: () -> Text
        """The name of this buffer's debug log."""
        return self.handler.vimvar("coqtail_log_name")  # type: ignore[no-any-return]

    @log.setter
    def log(self, log):
        # type: (Text) -> None
        """The name of this buffer's debug log."""
        self.handler.vimvar("coqtail_log_name", log)

    @property
    def filename(self):
        # type: () -> str
        """The absolute path of this buffer's current Coq file."""
        return self.handler.vimcall("expand", "#{}:p".format(self.handler.bnum))  # type: ignore

    @property
    def buffer(self):
        # type: () -> List[Text]
        """The contents of this buffer."""
        return self.handler.vimcall("getbufline", self.handler.bnum, 1, "$")  # type: ignore


class ThreadedTCPServer(ThreadingMixIn, TCPServer):
    """Create a thread for each client."""


class CoqtailHandler(StreamRequestHandler):
    """Forward messages between Vim and Coqtail."""

    # Redraw rate in seconds
    refresh_rate = 0.05

    # How often to check for a closed channel
    check_close_rate = 1

    # Is the channel open
    closed = False

    # Is a request currently being handled
    working = False

    def parse_msgs(self):
        # type: () -> None
        """Parse messages sent over a Vim channel."""
        while not self.closed:
            try:
                msg = self.rfile.readline().decode("utf-8")
            except ValueError:
                msg = ""
            # Check if channel closed
            if msg == "":
                self.closed = True
                break

            msg_id, data = json.loads(msg)
            if msg_id >= 0:
                bnum, func, args = data
                if func == "interrupt":
                    self.interrupt()
                else:
                    self.reqs.put((msg_id, bnum, func, args))
            else:
                # N.B. Accessing self.resps concurrently creates a race condition
                # where defaultdict could construct a Queue twice
                with self.resp_lk:
                    self.resps[-msg_id].put((msg_id, data))

    def get_msg(self, msg_id=None):
        # type: (Optional[int]) -> Sequence[Any]
        """Check for any pending messages from Vim."""
        if msg_id is None:
            queue = self.reqs  # type: Queue[Any]
        else:
            with self.resp_lk:
                queue = self.resps[msg_id]
        while not self.closed:
            try:
                return queue.get(timeout=self.check_close_rate)  # type: ignore
            except Empty:
                pass
        raise EOFError

    def handle(self):
        # type: () -> None
        """Forward requests from Vim to the appropriate Coqtail function."""
        self.coq = Coqtail(self)
        self.closed = False
        self.reqs = Queue()  # type: Queue[Tuple[int, int, str, Mapping[str, Any]]]
        self.resps = ddict(Queue)  # type: DefaultDict[int, Queue[Tuple[int, Any]]]
        self.resp_lk = threading.Lock()

        read_thread = threading.Thread(target=self.parse_msgs)
        read_thread.daemon = True
        read_thread.start()

        while not self.closed:
            try:
                self.working = False
                self.msg_id, self.bnum, func, args = self.get_msg()
                self.refresh_time = 0.0
                self.working = True
            except EOFError:
                break

            handler = {
                "start": self.coq.start,
                "stop": self.coq.stop,
                "step": self.coq.step,
                "rewind": self.coq.rewind,
                "to_line": self.coq.to_line,
                "to_top": self.coq.to_top,
                "query": self.coq.query,
                "endpoint": self.coq.endpoint,
                "toggle_debug": self.coq.toggle_debug,
                "splash": self.coq.splash,
                "sync": self.coq.sync,
                "find_def": self.coq.find_def,
                "find_lib": self.coq.find_lib,
                "refresh": self.coq.refresh,
            }.get(func, None)

            try:
                ret = handler(**args) if handler is not None else None  # type: ignore
            except EOFError:
                break
            msg = [self.msg_id, {"buf": self.bnum, "ret": ret}]
            self.wfile.write(json.dumps(msg).encode("utf-8"))

            try:
                del self.resps[self.msg_id]
            except KeyError:
                pass

            if func == "stop":
                break

    def vimeval(self, expr):
        # type: (List[Any]) -> Any
        """Send Vim a request."""
        self.wfile.write(json.dumps(expr + [-self.msg_id]).encode("utf-8"))

        msg_id, res = self.get_msg(self.msg_id)
        assert msg_id == -self.msg_id
        return res

    def vimexpr(self, expr):
        # type: (str) -> Any
        """Request Vim to evaluate an expression."""
        return self.vimeval(["expr", expr])

    def vimcall(self, expr, *args):
        # type: (str, *Any) -> Any
        """Request Vim to evaluate a function call."""
        return self.vimeval(["call", expr, args])

    def vimvar(self, var, val=None):
        # type: (str, Optional[Any]) -> Any
        """Get or set the value of a Vim variable."""
        if val is None:
            return self.vimcall("getbufvar", self.bnum, var)
        else:
            return self.vimcall("setbufvar", self.bnum, var, val)

    def refresh(self, goals=True, force=True):
        # type: (bool, bool) -> None
        """Refresh the highlighting and auxiliary panels."""
        if not force:
            cur_time = time.time()
            force = cur_time - self.refresh_time > self.refresh_rate
            self.refresh_time = cur_time
        if force:
            self.vimcall(
                "coqtail#Refresh",
                self.bnum,
                self.coq.highlights,
                self.coq.panels(goals),
            )

    def interrupt(self):
        # type: () -> None
        """Interrupt Coqtop and clear the request queue."""
        if self.coq.coqtop is not None and self.working:
            self.working = False
            while not self.reqs.empty():
                try:
                    self.reqs.get_nowait()
                except Empty:
                    break
            self.coq.coqtop.interrupt()


serv = None


def start_server():
    # type: () -> int
    """Start the TCP server through which Vim and Coqtail communicate."""
    # N.B. port = 0 chooses any arbitrary open one
    global serv
    serv = ThreadedTCPServer(("localhost", 0), CoqtailHandler)
    # Mypy isn't aware of this attribute on ThreadingMixin
    serv.daemon_threads = True  # type: ignore
    _, port = serv.server_address

    serv_thread = threading.Thread(target=serv.serve_forever)
    serv_thread.daemon = True
    serv_thread.start()

    return port


def stop_server():
    # type: () -> None
    """Stop the TCP server."""
    global serv
    if serv is not None:
        serv.shutdown()
        serv.server_close()
        serv = None


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


def _between(buf, start, end):
    # type: (List[Text], Tuple[int, int], Tuple[int, int]) -> Text
    """Return the text between a given start and end point."""
    sline, scol = start
    eline, ecol = end

    lines = []  # type: List[Text]
    for idx, line in enumerate(buf[sline : eline + 1]):
        lcol = scol if idx == 0 else 0
        rcol = ecol + 1 if idx == eline - sline else len(line)
        lines.append(line[lcol:rcol])

    return "\n".join(lines)


def _get_message_range(lines, after):
    # type: (List[Text], Tuple[int, int]) -> Mapping[str, Tuple[int, int]]
    """Return the next sentence to send after a given point."""
    end_pos = _find_next_sentence(lines, *after)
    return {"start": after, "stop": end_pos}


def _find_next_sentence(lines, sline, scol):
    # type: (List[Text], int, int) -> Tuple[int, int]
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
            raise NoDotError()

        # Skip leading comments
        if first_line.startswith("(*"):
            com_end = _skip_comment(lines, line, col + 2)
            if com_end is None:
                raise UnmatchedError("(*", (line, col))

            sline, col = com_end
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
    # type: (List[Text], int, int) -> Tuple[int, int]
    """Find the next '.' after a given point."""
    max_line = len(lines)

    while sline < max_line:
        line = lines[sline][scol:]
        dot_pos = line.find(".")
        com_pos = line.find("(*")
        str_pos = line.find('"')

        if dot_pos == -1 and com_pos == -1 and str_pos == -1:
            # Nothing on this line
            sline += 1
            scol = 0
        elif dot_pos == -1 or (0 <= com_pos < dot_pos) or (0 <= str_pos < dot_pos):
            if str_pos == -1 or (0 <= com_pos < str_pos):
                # We see a comment opening before the next '.'
                com_end = _skip_comment(lines, sline, scol + com_pos + 2)
                if com_end is None:
                    raise UnmatchedError("(*", (sline, scol + com_pos))

                sline, scol = com_end
            else:
                # We see a string starting before the next '.'
                str_end = _skip_str(lines, sline, scol + str_pos + 1)
                if str_end is None:
                    raise UnmatchedError('"', (sline, scol + str_pos))

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

    raise NoDotError()


def _skip_str(lines, sline, scol):
    # type: (List[Text], int, int) -> Optional[Tuple[int, int]]
    """Skip the next block contained in " "."""
    return _skip_block(lines, sline, scol, '"')


def _skip_comment(lines, sline, scol):
    # type: (List[Text], int, int) -> Optional[Tuple[int, int]]
    """Skip the next block contained in (* *)."""
    return _skip_block(lines, sline, scol, "*)", "(*")


def _skip_block(lines, sline, scol, estr, sstr=None):
    # type: (List[Text], int, int, str, Optional[str]) -> Optional[Tuple[int, int]]
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
    nocom = []
    com_pos = []  # Remember comment offset and length
    off = 0
    nesting = 0

    while msg != "":
        start = msg.find("(*")
        end = msg.find("*)")
        if start == -1 and (end == -1 or (end != -1 and nesting == 0)):
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


def _find_diff(x, y, stop=None):
    # type: (Sequence[Any], Sequence[Any], Optional[int]) -> Optional[int]
    """Locate the first differing element in 'x' and 'y' up to 'stop'."""
    seq = enumerate(zip_longest(x, y))  # type: Iterator[Tuple[int, Any]]
    if stop is not None:
        seq = islice(seq, stop)
    return next((i for i, vs in seq if vs[0] != vs[1]), None)
