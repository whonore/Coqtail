# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Classes and functions for managing auxiliary panels and Coqtop interfaces."""

import json
import re
import socket
import threading
import time
from collections import defaultdict as ddict
from collections import deque
from concurrent import futures
from itertools import count, islice, zip_longest
from queue import Empty, Queue
from socketserver import StreamRequestHandler, ThreadingTCPServer
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    DefaultDict,
    Deque,
    Dict,
    Iterable,
    Iterator,
    List,
    Mapping,
    NamedTuple,
    Optional,
    Sequence,
    Tuple,
    TypeVar,
    Union,
    cast,
    overload,
)

import coqtop as CT
from xmlInterface import Goals, PPTag, TaggedToken

T = TypeVar("T")
Highlight = NamedTuple(
    "Highlight",
    [("line_no", int), ("index", int), ("tok_len", int), ("tag", PPTag)],
)
ProofRange = NamedTuple(
    "ProofRange",
    (("proof", Mapping[str, Tuple[int, int]]), ("qed", Mapping[str, Tuple[int, int]])),
)
Req = Tuple[int, int, str, Mapping[str, Any]]  # (msg_id, bnum, func, args)
Res = Tuple[int, Any]  # (msg_id, data)
SkipFun = Callable[[Sequence[bytes], int, int], Optional[Tuple[int, int]]]

if TYPE_CHECKING:
    # Some types are only subscriptable during type checking.
    from typing_extensions import TypedDict

    ReqQueue = Queue[Req]
    ResQueue = Queue[Res]
    VimOptions = TypedDict(
        "VimOptions",
        {
            "encoding": str,
            "timeout": int,
            "filename": str,
            "stderr_is_warning": bool,
        },
    )
    ResFuture = futures.Future[Optional[str]]
else:
    ReqQueue = Queue
    ResQueue = Queue
    VimOptions = Mapping[str, Any]
    ResFuture = futures.Future

PROOF_START_PAT = re.compile(rb"^\s*(Proof)\b")
PROOF_END_PAT = re.compile(rb"^\s*(Qed|Admitted|Defined|Abort|Save)\b")
OPAQUE_PROOF_ENDS = {b"Qed", b"Admitted"}


def lines_and_highlights(
    tagged_tokens: Union[str, Iterable[TaggedToken]],
    line_no: int,
) -> Tuple[List[str], List[Highlight]]:
    """Converts a sequence of tagged tokens into lines and higlight positions.

    Note that matchaddpos()'s highlight positions are 1-indexed,
    but this function expects line_no to be 0-indexed.
    """
    # If tagged_tokens turns out to already be a string (which is the case for
    # older versions of Coq), just return it as is, with no highlights.
    if isinstance(tagged_tokens, str):
        return tagged_tokens.splitlines(), []

    lines: List[str] = []
    highlights: List[Highlight] = []
    line_no += 1  # Convert to 1-indexed per matchaddpos()'s spec
    line, index = "", 1

    for token, tag in tagged_tokens:
        # NOTE: Can't use splitlines or else tokens like ' =\n' won't properly
        # begin a new line
        for i, tok in enumerate(token.split("\n")):
            if i > 0:
                # Encountered a newline in token
                lines.append(line)
                line_no += 1
                line, index = "", 1

            tok_len = len(tok.encode("utf-8"))
            if tag is not None:
                highlights.append(Highlight(line_no, index, tok_len, tag))

            line += tok
            index += tok_len

    lines.append(line)
    return lines, highlights


class UnmatchedError(Exception):
    """An unmatched comment or string was found."""

    def __init__(self, token: str, loc: Tuple[int, int]) -> None:
        super().__init__(f"Found unmatched {token}.")
        line, col = loc
        self.range = (loc, (line, col + len(token)))


class NoDotError(Exception):
    """No more sentences were found."""


# Coqtail Server #
class Coqtail:
    """Manage Coqtop interfaces and auxiliary buffers for each Coq file."""

    def __init__(self, handler: "CoqtailHandler") -> None:
        """Initialize variables.

        coqtop - The Coqtop interface
        handler - The Vim interface
        changedtick - The most recent value of `b:changedtick` that Coqtail has
                      observed. The positions stored in other variables
                      (`endpoints`, `send_queue`, `error_at`) can become
                      invalid when this value gets outdated. To protect Coqtail
                      from this inconsistency, the buffer is locked (unset
                      `modifiable`) when processing. When processing, `sync()`
                      should be called first to refresh this variable and
                      remove the positions invalidated by the new changes to
                      the buffer.
        buffer - The buffer corresponding to changedtick
        endpoints - A stack (grows to the right) of the end positions of the
                    sentences checked by CoqTop. The end position of a sentence
                    is the start position of its next sentence.
        send_queue - A queue of the sentences to send to Coqtop. Each item
                     contains the "start" and "end" (inclusive, including the
                     dot) position of the sentence.
        error_at - The position of the last error
        omitted_proofs - The positions of the starts and ends of the proofs
                         that have been skipped by `to_line()`.
        info_msg - Lines of text to display in the info panel
        goal_msg - Lines of text to display in the goal panel
        goal_hls - Highlight positions for each line of goal_msg
        """
        self.coqtop = CT.Coqtop(self.add_info_callback)
        self.handler = handler
        self.changedtick = 0
        self.buffer: List[bytes] = []
        self.endpoints: List[Tuple[int, int]] = []
        self.send_queue: Deque[Mapping[str, Tuple[int, int]]] = deque()
        self.error_at: Optional[Tuple[Tuple[int, int], Tuple[int, int]]] = None
        self.omitted_proofs: List[ProofRange] = []
        self.info_msg: List[str] = []
        self.goal_msg: List[str] = []
        self.goal_hls: List[Highlight] = []

    def sync(self, opts: VimOptions) -> Optional[str]:
        """Check if the buffer has been updated and rewind Coqtop if so."""
        err = None
        newtick = self.get_changedtick()
        if newtick != self.changedtick:
            newbuf = self.get_buffer()

            if self.endpoints != []:
                diff = _diff_lines(self.buffer, newbuf, self.endpoints[-1])
                if diff is not None:
                    linediff, coldiff = diff
                    err = self.rewind_to(linediff, coldiff + 1, opts=opts)

            self.changedtick = newtick
            self.buffer = newbuf

        return err

    def find_coq(
        self,
        coq_path: str,
        coq_prog: str,
        opts: VimOptions,
    ) -> Union[CT.VersionInfo, str]:
        # pylint: disable=unused-argument
        # opts is always passed by handle().
        """Find the Coqtop executable."""
        try:
            ver_or_err = self.coqtop.find_coq(
                coq_path if coq_path != "" else None,
                coq_prog if coq_prog != "" else None,
            )
        except (ValueError, CT.CoqtopError) as e:
            ver_or_err = str(e)
        return ver_or_err

    # Coqtop Interface #
    def start(
        self,
        coqproject_args: List[str],
        use_dune: bool,
        dune_compile_deps: bool,
        opts: VimOptions,
    ) -> Tuple[Optional[str], str]:
        """Start a new Coqtop instance."""
        try:
            err, stderr = self.coqtop.start(
                opts["filename"],
                coqproject_args,
                use_dune,
                dune_compile_deps,
                timeout=opts["timeout"],
                stderr_is_warning=opts["stderr_is_warning"],
            )
            self.print_stderr(stderr)
        except (ValueError, CT.CoqtopError) as e:
            err, stderr = str(e), ""
        return err, stderr

    def stop(self, opts: VimOptions) -> None:
        """Stop Coqtop."""
        # pylint: disable=unused-argument
        # opts is always passed by handle().
        self.coqtop.stop()

    def step(self, steps: int, opts: VimOptions) -> Optional[str]:
        """Advance Coq by 'steps' sentences."""
        self.sync(opts=opts)

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

        failed_at, err = self.send_until_fail(self.buffer, opts=opts)
        if unmatched is not None and failed_at is None:
            # Only report unmatched if no other errors occurred first
            self.set_info(str(unmatched), reset=False)
            self.error_at = unmatched.range
            self.refresh(goals=False, opts=opts)

        return err

    def rewind(self, steps: int, opts: VimOptions) -> Optional[str]:
        """Rewind Coq by 'steps' sentences."""
        if steps < 1 or self.endpoints == []:
            return None

        try:
            _, msg, extra_steps, stderr = self.coqtop.rewind(
                steps,
                stderr_is_warning=opts["stderr_is_warning"],
            )
            self.print_stderr(stderr)
        except CT.CoqtopError as e:
            return str(e)

        if extra_steps is None:
            return msg

        self.endpoints = self.endpoints[: -(steps + extra_steps)]
        self.omitted_proofs = [
            range_
            for range_ in self.omitted_proofs
            if self.endpoints != [] and range_.qed["stop"] <= self.endpoints[-1]
        ]
        self.error_at = None
        self.refresh(opts=opts)
        return None

    def to_line(
        self,
        line: int,
        col: int,
        admit: bool,
        opts: VimOptions,
    ) -> Optional[str]:
        """Advance/rewind Coq to the specified position."""
        self.sync(opts=opts)

        # Get the location of the last '.'
        eline, ecol = self.endpoints[-1] if self.endpoints != [] else (0, 0)

        # Check if should rewind or advance
        if (line, col) < (eline, ecol):
            # Don't rewind the sentence whose dot is on the specified position.
            #                               vvv
            return self.rewind_to(line, col + 1 + 1, opts=opts)

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

        failed_at, err = self.send_until_fail(self.buffer, admit=admit, opts=opts)
        if unmatched is not None and failed_at is None:
            # Only report unmatched if no other errors occurred first
            self.set_info(str(unmatched), reset=False)
            self.error_at = unmatched.range
            self.refresh(goals=False, opts=opts)

        return err

    def to_top(self, opts: VimOptions) -> Optional[str]:
        """Rewind to the beginning of the file."""
        return self.rewind_to(0, 1, opts=opts)

    def query(
        self,
        args: Iterable[str],
        opts: VimOptions,
        silent: bool = False,
    ) -> None:
        """Forward Coq query to Coqtop interface."""
        success, msg, stderr = self.do_query(" ".join(args), opts=opts)

        if not success or not silent:
            self.set_info(msg, reset=True)
        self.print_stderr(stderr)
        self.refresh(goals=False, opts=opts)

    def endpoint(self, opts: VimOptions) -> Tuple[int, int]:
        """Return the end of the Coq checked section."""
        # pylint: disable=unused-argument
        # opts is always passed by handle().
        # Get the location of the last '.'
        line, col = self.endpoints[-1] if self.endpoints != [] else (0, 1)
        return (line + 1, col - 1 + 1)

    def errorpoint(self, opts: VimOptions) -> Optional[Tuple[int, int]]:
        """Return the start of the error region."""
        # pylint: disable=unused-argument
        # opts is always passed by handle().
        if self.error_at is not None:
            line, col = self.error_at[0]
            return (line + 1, col + 1)

        return None

    # Helpers #
    def send_until_fail(
        self,
        buffer: Sequence[bytes],
        opts: VimOptions,
        admit: bool = False,
    ) -> Tuple[Optional[Tuple[int, int]], Optional[str]]:
        """Send all sentences in 'send_queue' until an error is encountered."""
        empty = self.send_queue == deque()
        scroll = len(self.send_queue) > 1
        failed_at = None
        no_msgs = True
        self.error_at = None
        admit_up_to: Optional[Mapping[str, Tuple[int, int]]] = None

        while self.send_queue:
            self.refresh(goals=False, force=False, scroll=scroll, opts=opts)
            to_send = self.send_queue.popleft()
            message = _between(buffer, to_send["start"], to_send["stop"])
            no_comments, _ = _strip_comments(message)

            if admit:
                if admit_up_to is None:
                    pstart = PROOF_START_PAT.match(no_comments)
                    if pstart is not None:
                        # Reached the beginning of a proof in admit mode.
                        admit_up_to = _find_opaque_proof_end(buffer, self.send_queue)
                        if admit_up_to is not None:
                            admit_from = _shrink_range_to_match(
                                to_send,
                                pstart.group(),
                                pstart.start(1),
                            )
                            self.omitted_proofs.append(
                                ProofRange(admit_from, admit_up_to)
                            )
                elif admit_up_to["stop"] == to_send["stop"]:
                    # Reached the end of an opaque proof in admit mode. Replace
                    # with `Admitted`.
                    match = PROOF_END_PAT.match(no_comments)
                    assert match is not None and match.group(1) in OPAQUE_PROOF_ENDS
                    message = no_comments = b"Admitted."
                    admit_up_to = None
                else:
                    # Inside an opaque proof in admit mode. Skip this sentence.
                    continue

            try:
                success, msg, err_loc, stderr = self.coqtop.dispatch(
                    message.decode("utf-8"),
                    no_comments.decode("utf-8"),
                    encoding=opts["encoding"],
                    timeout=opts["timeout"],
                    stderr_is_warning=opts["stderr_is_warning"],
                )
            except CT.CoqtopError as e:
                return None, str(e)

            if msg != "":
                self.set_info(msg, reset=no_msgs)
                no_msgs = False

            self.print_stderr(stderr)
            no_msgs = no_msgs and stderr == ""

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
                    sline, scol = _pos_from_offset(col, message, loc_s)
                    eline, ecol = _pos_from_offset(col, message, loc_e)
                    self.error_at = ((line + sline, scol), (line + eline, ecol))

        # Clear info if no messages and at least one message was sent
        if no_msgs and not empty:
            self.set_info("", reset=True)
        self.refresh(opts=opts, scroll=scroll)
        return failed_at, None

    def rewind_to(self, line: int, col: int, opts: VimOptions) -> Optional[str]:
        """Rewind to the point where all remaining endpoints are strictly
        before the specified position.
        """
        # Count the number of endpoints after the specified location
        steps_too_far = sum(pos >= (line, col) for pos in self.endpoints)
        return self.rewind(steps_too_far, opts=opts)

    def do_query(self, query: str, opts: VimOptions) -> Tuple[bool, str, str]:
        """Execute a query and return the reply."""
        # Ensure that the query ends in '.'
        if not query.endswith("."):
            query += "."

        try:
            success, msg, _, stderr = self.coqtop.dispatch(
                query,
                in_script=False,
                encoding=opts["encoding"],
                timeout=opts["timeout"],
                stderr_is_warning=opts["stderr_is_warning"],
            )
        except CT.CoqtopError as e:
            return False, str(e), ""

        return success, msg, stderr

    def qual_name(self, target: str, opts: VimOptions) -> Optional[Tuple[str, str]]:
        """Find the fully qualified name of 'target' using 'Locate'."""
        success, locate, _ = self.do_query(f"Locate {target}.", opts=opts)
        if not success:
            return None

        # Join lines that start with whitespace to the previous line
        locate = re.sub(r"\n +", " ", locate)

        # Choose first match from 'Locate' since that is the default in the
        # current context
        match = locate.split("\n")[0]
        if "No object of basename" in match:
            return None

        # Look for alias
        alias = re.search(r"\(alias of (.*)\)", match)
        if alias is not None:
            # Found an alias, search again using that
            return self.qual_name(alias.group(1), opts=opts)

        info = match.split()
        # Special case for Module Type
        if info[0] == "Module" and info[1] == "Type":
            tgt_type = "Module Type"
            qual_tgt = info[2]
        else:
            tgt_type, qual_tgt = info[:2]

        return qual_tgt, tgt_type

    def find_lib(self, lib: str, opts: VimOptions) -> Optional[str]:
        """Find the path to the .v file corresponding to the libary 'lib'."""
        success, locate, _ = self.do_query(f"Locate Library {lib}.", opts=opts)
        if not success:
            return None

        path = re.search(r"file\s+(.*)\.vo", locate)
        return path.group(1) if path is not None else None

    def find_qual(
        self,
        qual_tgt: str,
        tgt_type: str,
        opts: VimOptions,
    ) -> Optional[Tuple[str, str]]:
        """Find the Coq file containing the qualified name 'qual_tgt'."""
        qual_comps = qual_tgt.split(".")
        base_name = qual_comps[-1]

        # If 'qual_comps' starts with Top or 'tgt_type' is Variable then
        # 'qual_tgt' is defined in the current file
        if qual_comps[0] == "Top" or tgt_type == "Variable":
            return opts["filename"], base_name

        # Find the longest prefix of 'qual_tgt' that matches a logical path in
        # 'path_map'
        for end in range(-1, -len(qual_comps), -1):
            path = self.find_lib(".".join(qual_comps[:end]), opts=opts)
            if path is not None:
                return path + ".v", base_name

        return None

    def find_def(
        self,
        target: str,
        opts: VimOptions,
    ) -> Optional[Tuple[str, List[str]]]:
        """Create patterns to jump to the definition of 'target'."""
        # Get the fully qualified version of 'target'
        qual = self.qual_name(target, opts=opts)
        if qual is None:
            return None
        qual_tgt, tgt_type = qual

        # Find what file the definition is in and what type it is
        tgt = self.find_qual(qual_tgt, tgt_type, opts=opts)
        if tgt is None:
            return None
        tgt_file, tgt_name = tgt

        return tgt_file, get_searches(tgt_type, tgt_name)

    def next_bullet(self, opts: VimOptions) -> Optional[str]:
        """Check the bullet expected for the next subgoal."""
        success, show, _ = self.do_query("Show.", opts=opts)
        if not success:
            return None

        bmatch = re.search(r'(?:bullet |unfocusing with ")([-+*}]+)', show)
        return bmatch.group(1) if bmatch is not None else None

    # Goals and Infos #
    def refresh(
        self,
        opts: VimOptions,
        goals: bool = True,
        force: bool = True,
        scroll: bool = False,
    ) -> None:
        """Refresh the auxiliary panels."""
        if goals:
            newgoals, newinfo = self.get_goals(opts=opts)
            if newinfo != "":
                self.set_info(newinfo, reset=False)
            if newgoals is not None:
                self.set_goal(self.pp_goals(newgoals, opts=opts))
            else:
                self.set_goal(clear=True)
        self.handler.refresh(goals=goals, force=force, scroll=scroll)

    def get_goals(self, opts: VimOptions) -> Tuple[Optional[Goals], str]:
        """Get the current goals."""
        try:
            _, msg, goals, stderr = self.coqtop.goals(
                timeout=opts["timeout"],
                stderr_is_warning=opts["stderr_is_warning"],
            )
            self.print_stderr(stderr)
            return goals, msg
        except CT.CoqtopError as e:
            return None, str(e)

    def pp_goals(
        self,
        goals: Goals,
        opts: VimOptions,
    ) -> Tuple[List[str], List[Highlight]]:
        """Pretty print the goals."""
        lines: List[str] = []
        highlights: List[Highlight] = []

        ngoals = len(goals.fg)
        nhidden = len(goals.bg[0]) if goals.bg != [] else 0
        nshelved = len(goals.shelved)
        nadmit = len(goals.given_up)

        # Information about number of remaining goals
        lines.append(f"{ngoals} subgoal{'' if ngoals == 1 else 's'}")
        if nhidden > 0:
            lines.append(f"({nhidden} unfocused at this level)")
        if nshelved > 0 or nadmit > 0:
            line = []
            if nshelved > 0:
                line.append(f"{nshelved} shelved")
            if nadmit > 0:
                line.append(f"{nadmit} admitted")
            lines.append(" ".join(line))

        lines.append("")

        # When a subgoal is finished
        if ngoals == 0:
            next_goal = next((bgs[0] for bgs in goals.bg if bgs != []), None)
            if next_goal is not None:
                bullet = self.next_bullet(opts=opts)
                bullet_info = ""
                if bullet is not None:
                    if bullet == "}":
                        bullet_info = "end this goal with '}'"
                    else:
                        bullet_info = f"use bullet '{bullet}'"

                next_info = "Next goal"
                if next_goal.name is not None:
                    next_info += f" [{next_goal.name}]"
                if bullet_info != "":
                    next_info += f" ({bullet_info})"
                next_info += ":"

                lines += [next_info, ""]

                ls, hls = lines_and_highlights(next_goal.ccl, len(lines))
                lines += ls
                highlights += hls
            else:
                lines.append("All goals completed.")

        for idx, goal in enumerate(goals.fg):
            if idx == 0:
                # Print the environment only for the current goal
                for hyp in goal.hyp:
                    ls, hls = lines_and_highlights(hyp, len(lines))
                    lines += ls
                    highlights += hls

            hbar = f"{'':=>25} ({idx + 1} / {ngoals})"
            if goal.name is not None:
                hbar += f" [{goal.name}]"
            lines += ["", hbar, ""]

            ls, hls = lines_and_highlights(goal.ccl, len(lines))
            lines += ls
            highlights += hls

        return lines, highlights

    def set_goal(
        self,
        msg: Optional[Tuple[List[str], List[Highlight]]] = None,
        clear: bool = False,
    ) -> None:
        """Update the goal message."""
        if msg is not None:
            self.goal_msg, self.goal_hls = msg
        if clear or "".join(self.goal_msg) == "":
            self.goal_msg, self.goal_hls = ["No goals."], []

    def add_info_callback(self, msg: str) -> None:
        """Callback for appending to the info panel and refreshing it."""
        self.set_info(msg.split("\n"), reset=False)
        self.handler.refresh(goals=False, force=True, scroll=True)

    def set_info(
        self,
        msg: Optional[Union[str, List[str]]] = None,
        reset: bool = True,
    ) -> None:
        """Update the info message."""
        if msg is not None:
            info = msg.split("\n") if isinstance(msg, str) else msg
            if reset or self.info_msg == []:
                self.info_msg = info
            else:
                self.info_msg += [""] + info

            # Normalize an empty buffer to an empty list instead of a single
            # empty line.
            if self.info_msg == [""]:
                self.info_msg = []

    def print_stderr(self, err: str) -> None:
        """Display a message from Coqtop stderr."""
        if err != "":
            self.set_info("From stderr:\n" + err, reset=False)

    @property
    def highlights(self) -> Dict[str, Optional[Union[str, List[Tuple[int, int, int]]]]]:
        """Vim match patterns for highlighting."""
        matches: Dict[str, Optional[Union[str, List[Tuple[int, int, int]]]]] = {
            "checked": None,
            "sent": None,
            "error": None,
            "omitted": None,
        }

        if self.endpoints != []:
            line, col = self.endpoints[-1]
            matches["checked"] = matcher[: line + 1, :col]

        if self.send_queue:
            sline, scol = self.endpoints[-1] if self.endpoints != [] else (0, -1)
            eline, ecol = self.send_queue[-1]["stop"]
            matches["sent"] = matcher[sline : eline + 1, scol:ecol]

        if self.error_at is not None:
            (sline, scol), (eline, ecol) = self.error_at
            matches["error"] = matcher[sline : eline + 1, scol:ecol]

        if self.omitted_proofs != []:
            ranges = []
            for pstart, pend in self.omitted_proofs:
                for range_ in (pstart, pend):
                    sline, scol = range_["start"]
                    eline, ecol = range_["stop"]
                    for line in range(sline, eline + 1):
                        col = scol if line == sline else 0
                        span = (
                            ecol - col
                            if line == eline
                            else len(self.buffer[line]) - col
                        )
                        ranges.append((line + 1, col + 1, span))
            matches["omitted"] = ranges

        return matches

    def panels(
        self,
        goals: bool = True,
    ) -> Mapping[str, Tuple[List[str], List[Highlight]]]:
        """The auxiliary panel content."""
        panels: Dict[str, Tuple[List[str], List[Highlight]]] = {
            "info": (self.info_msg, [])
        }
        if goals:
            panels["goal"] = (self.goal_msg, self.goal_hls)
        return panels

    def splash(
        self,
        version: str,
        width: int,
        height: int,
        opts: VimOptions,
    ) -> None:
        """Display the logo in the info panel."""
        msg = [
            "~~~~~~~~~~~~~~~~~~~~~~~",
            "λ                     /",
            " λ      Coqtail      / ",
            "  λ                 /  ",
            f"   λ{('Coq ' + version).center(15)}/    ",
            "    λ             /    ",
            "     λ           /     ",
            "      λ         /      ",
            "       λ       /       ",
            "        λ     /        ",
            "         λ   /         ",
            "          λ /          ",
            "           ‖           ",
            "           ‖           ",
            "           ‖           ",
            "          / λ          ",
            "         /___λ         ",
        ]
        msg_maxw = max(len(line) for line in msg)
        msg = [line.center(width - msg_maxw // 2) for line in msg]

        # Center vertically if the Info panel is empty.
        if self.info_msg == []:
            msg = [""] * ((height // 2) - (len(msg) // 2 + 1)) + msg
        msg = [line.rstrip() for line in msg]
        self.set_info(msg, reset=False)
        self.refresh(goals=False, opts=opts)

    def toggle_debug(self, opts: VimOptions) -> None:
        """Enable or disable logging of debug messages."""
        log = self.coqtop.toggle_debug()
        if log is None:
            msg = "Debugging disabled."
            self.log = ""
        else:
            msg = f"Debugging enabled. Log: {log}."
            self.log = log

        self.set_info(msg, reset=True)
        self.refresh(goals=False, opts=opts)

    # Vim Helpers #
    def get_changedtick(self) -> int:
        """Get the value of changedtick for this buffer."""
        return cast(int, self.handler.vimvar("changedtick"))

    @property
    def log(self) -> str:
        """The name of this buffer's debug log."""
        return cast(str, self.handler.vimvar("coqtail_log_name"))

    @log.setter
    def log(self, log: str) -> None:
        """The name of this buffer's debug log."""
        self.handler.vimvar("coqtail_log_name", log)

    def get_buffer(self) -> List[bytes]:
        """Get the contents of this buffer."""
        lines: List[str] = self.handler.vimcall(
            "getbufline",
            True,
            self.handler.bnum,
            1,
            "$",
        )
        return [line.encode("utf-8") for line in lines]


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

    # Is the client synchronous
    sync = False

    def parse_msgs(self) -> None:
        """Parse messages sent over a Vim channel."""
        while not self.closed:
            try:
                msg = self.rfile.readline()
                msg_id, data = json.loads(msg)
            except (json.JSONDecodeError, ConnectionError, ValueError):
                # Check if channel closed
                self.closed = True
                break

            if msg_id >= 0:  # request from Vim
                bnum, func, args = data
                if func == "interrupt":
                    self.interrupt()
                else:
                    self.reqs.put((msg_id, bnum, func, args))
            else:  # response to a `vimeval` request
                # NOTE: Accessing self.resps concurrently creates a race
                # condition where defaultdict could construct a Queue twice
                with self.resp_lk:
                    self.resps[-msg_id].put((msg_id, data))

    @overload
    def get_msg(self, msg_id: None = ...) -> Req: ...

    @overload
    def get_msg(self, msg_id: int) -> Res: ...

    def get_msg(self, msg_id: Optional[int] = None) -> Union[Res, Req]:
        """Check for any pending messages from Vim."""
        queue: Union[ReqQueue, ResQueue]
        if msg_id is None:
            queue = self.reqs
        else:
            with self.resp_lk:
                queue = self.resps[msg_id]
        while not self.closed:
            try:
                return queue.get(timeout=self.check_close_rate)
            except Empty:
                pass
        raise EOFError

    def handle(self) -> None:
        """Forward requests from Vim to the appropriate Coqtail function."""
        self.coq = Coqtail(self)
        self.closed = False
        # Requests from Vim (`s:call`)
        self.reqs: ReqQueue = Queue()
        # Responses to `vimeval` requests.
        # The key is the id of Vim's request that was being handled at the
        # moment of `vimeval` call.
        self.resps: DefaultDict[int, ResQueue] = ddict(Queue)
        self.resp_lk = threading.Lock()

        threading.Thread(target=self.parse_msgs, daemon=True).start()

        while not self.closed:
            try:
                self.working = False
                self.msg_id, self.bnum, func, args = self.get_msg()
                self.refresh_time = 0.0
                self.working = True
            except EOFError:
                break

            handlers: Mapping[str, Callable[..., object]] = {
                "find_coq": self.coq.find_coq,
                "start": self.coq.start,
                "stop": self.coq.stop,
                "step": self.coq.step,
                "rewind": self.coq.rewind,
                "to_line": self.coq.to_line,
                "to_top": self.coq.to_top,
                "query": self.coq.query,
                "endpoint": self.coq.endpoint,
                "errorpoint": self.coq.errorpoint,
                "toggle_debug": self.coq.toggle_debug,
                "splash": self.coq.splash,
                "sync": self.coq.sync,
                "find_def": self.coq.find_def,
                "find_lib": self.coq.find_lib,
                "refresh": self.coq.refresh,
            }
            handler = handlers.get(func, None)

            try:
                ret = handler(**args) if handler is not None else None
                msg = [self.msg_id, {"buf": self.bnum, "ret": ret}]
                self.wfile.write(_to_jsonl(msg))
            except (EOFError, ConnectionError):
                break

            try:
                del self.resps[self.msg_id]
            except KeyError:
                pass

            if func == "stop":
                break

    def vimeval(self, expr: List[Any], wait: bool = True) -> Any:
        """Send Vim a request as `:h channel-commands`."""
        if wait:
            expr += [-self.msg_id]
        self.wfile.write(_to_jsonl(expr))

        if wait:
            msg_id, res = self.get_msg(self.msg_id)
            assert msg_id == -self.msg_id
            return res
        return None

    def vimcall(self, expr: str, wait: bool, *args: Any) -> Any:
        """Request Vim to evaluate a function call."""
        return self.vimeval(["call", expr, args], wait=wait)

    def vimvar(self, var: str, val: Optional[Any] = None) -> Any:
        """Get or set the value of a Vim variable."""
        return (
            self.vimcall("getbufvar", True, self.bnum, var)
            if val is None
            else self.vimcall("setbufvar", True, self.bnum, var, val)
        )

    def refresh(
        self,
        goals: bool = True,
        force: bool = True,
        scroll: bool = False,
    ) -> None:
        """Refresh the highlighting and auxiliary panels."""
        # pylint: disable=attribute-defined-outside-init
        # refresh_time is defined in handle() when the connection is opened.
        if not force:
            cur_time = time.time()
            force = cur_time - self.refresh_time > self.refresh_rate
            self.refresh_time = cur_time
        if force:
            self.vimcall(
                "coqtail#panels#refresh",
                self.sync,
                self.bnum,
                self.coq.highlights,
                self.coq.panels(goals),
                scroll,
            )

    def interrupt(self) -> None:
        """Interrupt Coqtop and clear the request queue."""
        if self.working:
            self.working = False
            while not self.reqs.empty():
                try:
                    msg_id, bnum, _, _ = self.reqs.get_nowait()
                    msg = [msg_id, {"buf": bnum, "ret": None}]
                    self.wfile.write(_to_jsonl(msg))
                except Empty:
                    break
            self.coq.coqtop.interrupt()


class CoqtailServer:
    """A server through which Vim and Coqtail communicate."""

    serv = None

    @staticmethod
    def start_server(sync: bool) -> int:
        """Start the TCP server."""
        # NOTE: port = 0 chooses any arbitrary open one
        CoqtailHandler.sync = sync
        CoqtailServer.serv = ThreadingTCPServer(("localhost", 0), CoqtailHandler)
        CoqtailServer.serv.daemon_threads = True
        _, port = CoqtailServer.serv.server_address

        threading.Thread(target=CoqtailServer.serv.serve_forever, daemon=True).start()

        return port

    @staticmethod
    def stop_server() -> None:
        """Stop the TCP server."""
        if CoqtailServer.serv is not None:
            CoqtailServer.serv.shutdown()
            CoqtailServer.serv.server_close()
            CoqtailServer.serv = None


class ChannelManager:
    """Emulate Vim's ch_* functions with sockets."""

    pool = futures.ThreadPoolExecutor()
    channels: Dict[int, socket.socket] = {}
    results: Dict[int, ResFuture] = {}
    sessions: Dict[int, int] = {}
    ch_id = count(1)
    msg_id = count(1)

    @staticmethod
    def open(address: str) -> int:
        """Open a channel."""
        ch_id = next(ChannelManager.ch_id)
        host, port = address.split(":")
        ChannelManager.channels[ch_id] = socket.create_connection((host, int(port)))
        return ch_id

    @staticmethod
    def close(handle: int) -> None:
        """Close a channel."""
        try:
            ChannelManager.channels[handle].close()
            del ChannelManager.channels[handle]
            del ChannelManager.results[handle]
            del ChannelManager.sessions[handle]
        except KeyError:
            pass

    @staticmethod
    def status(handle: int) -> str:
        """Check if a channel is open."""
        return "open" if handle in ChannelManager.channels else "closed"

    @staticmethod
    def send(
        handle: int,
        session: Optional[int],
        expr: str,
        reply_id: Optional[int] = None,
        returns: bool = True,
    ) -> bool:
        """Send a command request or reply on a channel."""
        try:
            ch = ChannelManager.channels[handle]
        except KeyError:
            return False

        if reply_id is None and session is not None:
            if ChannelManager.sessions.get(handle, None) == session:
                return True
            ChannelManager.sessions[handle] = session

        msg_id = reply_id if reply_id is not None else next(ChannelManager.msg_id)
        ch.sendall(_to_jsonl([msg_id, expr]))

        if returns:
            ChannelManager.results[handle] = ChannelManager.pool.submit(
                ChannelManager._recv,
                ChannelManager.channels[handle],
            )
        return True

    @staticmethod
    def poll(handle: int) -> Optional[str]:
        """Wait for a response on a channel."""
        try:
            return ChannelManager.results[handle].result(timeout=0)
        except futures.TimeoutError:
            return None

    @staticmethod
    def _recv(channel: socket.socket) -> Optional[str]:
        """Wait for a response on a channel."""
        data = []
        while True:
            try:
                data.append(channel.recv(4096).decode("utf-8"))
                # NOTE: Some older Vims can't convert expressions with None to
                # Vim values so just return a string
                res = "".join(data)
                _ = json.loads(res)
                return res
            except json.JSONDecodeError:
                pass
            except (KeyError, ConnectionError):
                return None


# Searching for Coq Definitions #
# TODO: could search more intelligently by searching only within relevant
# section/module, or sometimes by looking at the type (for constructors for
# example, or record projections)
def get_searches(tgt_type: str, tgt_name: str) -> List[str]:
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
    }

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
        rf"<({search_vernac})>\s*\zs<({search_name})>",
        rf"<({search_name})>",
    ]


# Finding Start and End of Coq Chunks #
def _pos_from_offset(col: int, msg: bytes, offset: int) -> Tuple[int, int]:
    """Calculate the line and column of a given offset."""
    msg = msg[:offset]
    lines = msg.split(b"\n")

    line = len(lines) - 1
    col = len(lines[-1]) + (col if line == 0 else 0)

    return (line, col)


def _between(
    buf: Sequence[bytes],
    start: Tuple[int, int],
    end: Tuple[int, int],
) -> bytes:
    """Return the text between a given start and end point (inclusive)."""
    sline, scol = start
    eline, ecol = end

    lines: List[bytes] = []
    for idx, line in enumerate(buf[sline : eline + 1]):
        lcol = scol if idx == 0 else 0
        rcol = ecol + 1 if idx == eline - sline else len(line)
        lines.append(line[lcol:rcol])

    return b"\n".join(lines)


def _get_message_range(
    lines: Sequence[bytes],
    after: Tuple[int, int],
) -> Mapping[str, Tuple[int, int]]:
    """Return the next sentence to send after a given point."""
    end_pos = _find_next_sentence(lines, *after)
    return {"start": after, "stop": end_pos}


def _find_next_sentence(
    lines: Sequence[bytes],
    sline: int,
    scol: int,
) -> Tuple[int, int]:
    """Find the next sentence to send to Coq."""
    braces = {ord(c) for c in "{}"}
    bullets = {ord(c) for c in "-+*"}

    line, col = (sline, scol)
    while True:
        # Skip leading whitespace
        for line in range(sline, len(lines)):
            first_line = lines[line][col:].lstrip()
            if first_line.rstrip() != b"":
                col += len(lines[line][col:]) - len(first_line)
                break

            col = 0
        else:  # break not reached, nothing left in the buffer but whitespace
            raise NoDotError()

        # Skip leading comments
        if first_line.startswith(b"(*"):
            com_end = _skip_comment(lines, line, col)
            if com_end is None:
                raise UnmatchedError("(*", (line, col))

            sline, col = com_end
        # Skip leading attributes
        elif first_line.startswith(b"#["):
            attr_end = _skip_attribute(lines, line, col)
            if attr_end is None:
                raise UnmatchedError("#[", (line, col))

            sline, col = attr_end
        else:
            break

    # Check if the first character of the sentence is a bullet
    if first_line[0] in braces | bullets:
        # '-', '+', '*' can be repeated
        for c in first_line[1:]:
            if c in bullets and c == first_line[0]:
                col += 1
            else:
                break
        return (line, col)

    # Check if this is a bracketed goal selector
    if _char_isdigit(first_line[0]):
        state = "digit"
        selcol = col
        selline = line
        max_line = len(lines)
        while selline < max_line:
            if selcol >= len(lines[selline]):
                selcol = 0
                selline += 1
                continue
            c = lines[selline][selcol]

            if state == "digit" and _char_isdigit(c):
                selcol += 1
            elif state == "digit" and _char_isspace(c):
                state = "beforecolon"
                selcol += 1
            elif state == "digit" and c == ord(":"):
                state = "aftercolon"
                selcol += 1
            elif state == "beforecolon" and _char_isspace(c):
                selcol += 1
            elif state == "beforecolon" and c == ord(":"):
                state = "aftercolon"
                selcol += 1
            elif state == "aftercolon" and _char_isspace(c):
                selcol += 1
            elif state == "aftercolon" and c == ord("{"):
                return (selline, selcol)
            else:
                break

    # Otherwise, find an ending '.'
    return _find_dot_after(lines, line, col)


def _find_dot_after(lines: Sequence[bytes], sline: int, scol: int) -> Tuple[int, int]:
    """Find the next '.' after a given point."""
    max_line = len(lines)

    while sline < max_line:
        line = lines[sline][scol:]
        dot_pos = line.find(b".")
        com_pos = line.find(b"(*")
        str_pos = line.find(b'"')
        elpi_pos = line.find(b"lp:{{")

        first_pos = dot_pos
        for p in (com_pos, str_pos, elpi_pos):
            if first_pos == -1 or (0 <= p < first_pos):
                first_pos = p

        if first_pos == -1:
            # Nothing on this line
            sline += 1
            scol = 0
        elif first_pos == com_pos:
            # We see a comment opening before the next '.'
            com_end = _skip_comment(lines, sline, scol + com_pos)
            if com_end is None:
                raise UnmatchedError("(*", (sline, scol + com_pos))
            sline, scol = com_end
        elif first_pos == str_pos:
            # We see a string starting before the next '.'
            str_end = _skip_str(lines, sline, scol + str_pos)
            if str_end is None:
                raise UnmatchedError('"', (sline, scol + str_pos))
            sline, scol = str_end
        elif first_pos == elpi_pos:
            lp_end = _skip_elpi(lines, sline, scol + elpi_pos)
            if lp_end is None:
                raise UnmatchedError("lp:{{", (sline, scol + elpi_pos))
            sline, scol = lp_end
        elif line[dot_pos : dot_pos + 2].rstrip() == b".":
            # Don't stop for '.' used in qualified name or for '..'
            return (sline, scol + dot_pos)
        elif line[dot_pos : dot_pos + 3] == b"...":
            # But do allow '...'
            return (sline, scol + dot_pos + 2)
        elif line[dot_pos : dot_pos + 2] == b"..":
            # Skip second '.'
            scol += dot_pos + 2
        else:
            scol += dot_pos + 1

    raise NoDotError()


def _skip_str(
    lines: Sequence[bytes],
    sline: int,
    scol: int,
) -> Optional[Tuple[int, int]]:
    """Skip the next block contained in " "."""
    return _skip_block(lines, sline, scol, b'"', b'"')


def _skip_comment(
    lines: Sequence[bytes],
    sline: int,
    scol: int,
) -> Optional[Tuple[int, int]]:
    """Skip the next block contained in (* *)."""
    return _skip_block(lines, sline, scol, b"(*", b"*)")


# In an elpi antiquotation lp:{{ }} we currently ignore strings "" and comments %
# For example the lp:{{ }} may end in the middle of a string "}}" or a comment % }}
# which is not ideal, but intentional to agree with the current Coq parser
# https://github.com/coq/coq/blob/f2bf445b8f4f5241ebdc348b69961041b4e57883/parsing/cLexer.ml#L542
# See also this discussion: https://github.com/whonore/Coqtail/pull/278#discussion_r841927125
def _skip_elpi(
    lines: Sequence[bytes],
    sline: int,
    scol: int,
) -> Optional[Tuple[int, int]]:
    """Skip the next block contained in lp:{{ }}."""
    return _skip_block(lines, sline, scol, b"lp:{{", b"}}", {b"{{": _skip_br2})


def _skip_br2(
    lines: Sequence[bytes],
    sline: int,
    scol: int,
) -> Optional[Tuple[int, int]]:
    """Skip the next block contained in {{ }}."""
    return _skip_block(lines, sline, scol, b"{{", b"}}")


def _skip_attribute(
    lines: Sequence[bytes],
    sline: int,
    scol: int,
) -> Optional[Tuple[int, int]]:
    """Skip the next block contained in #[ ]."""
    return _skip_block(lines, sline, scol, b"#[", b"]", {b'"': _skip_str})


def _skip_block(
    lines: Sequence[bytes],
    sline: int,
    scol: int,
    sstr: bytes,
    estr: bytes,
    skips: Optional[Mapping[bytes, SkipFun]] = None,
) -> Optional[Tuple[int, int]]:
    """A generic function to skip the next block contained in sstr estr."""
    assert lines[sline].startswith(sstr, scol)
    nesting = 1
    max_line = len(lines)
    scol += len(sstr)
    if skips is None:
        skips = {}

    while nesting > 0:
        if sline >= max_line:
            return None

        line = lines[sline]
        blk_end = line.find(estr, scol)
        blk_end = blk_end if blk_end != -1 else None
        if sstr != estr:
            blk_start = line.find(sstr, scol, blk_end)
            blk_start = blk_start if blk_start != -1 else None
        else:
            blk_start = None
        assert blk_start is None or blk_end is None or blk_start < blk_end

        # Look for contained blocks to skip
        skip_stop = blk_start if blk_start is not None else blk_end
        skip_starts = [(line.find(skip, scol, skip_stop), skip) for skip in skips]
        skip_starts = [(start, skip) for start, skip in skip_starts if start != -1]
        skip_start, skip = min(skip_starts, default=(None, None))
        if skip is not None and skip_start is not None:
            skip_end = skips[skip](lines, sline, skip_start)
            if skip_end is None:
                return None

            sline, scol = skip_end
            continue

        if blk_end is not None and blk_start is None:
            # Found an end and no new start
            scol = blk_end + len(estr)
            nesting -= 1
        elif blk_start is not None:
            # Found a new start
            scol = blk_start + len(sstr)
            nesting += 1
        else:
            # Nothing on this line
            sline += 1
            scol = 0

    return (sline, scol)


# Region Highlighting #
class Matcher:
    """Construct Vim regexes to pass to 'matchadd()' for an arbitrary region."""

    class _Matcher:
        """Construct regexes for a row or column."""

        def __getitem__(self, key: Tuple[Union[int, slice], str]) -> str:
            """Construct the regex."""
            match_range, match_type = key
            match = []
            if isinstance(match_range, slice):
                if match_range.start is not None and match_range.start > 1:
                    match.append(rf"\%>{match_range.start - 1}{match_type}")
                if match_range.stop is not None:
                    match.append(rf"\%<{match_range.stop}{match_type}")
            else:
                match.append(rf"\%{match_range}{match_type}")
            return "".join(match)

    def __init__(self) -> None:
        """Initialize the row/column matcher."""
        self._matcher = Matcher._Matcher()

    def __getitem__(self, key: Tuple[slice, slice]) -> str:
        """Construct the regex.

        'key' is [line-start : line-end, col-start : col-end]
        where positions are 0-indexed.
        Ranges are inclusive on the left and exclusive on the right.
        """
        lines, cols = map(Matcher.shift_slice, key)
        assert lines.stop is not None

        if lines.start == lines.stop - 1:
            return self._matcher[lines.start, "l"] + self._matcher[cols, "c"]
        return r"\|".join(
            x
            for x in (
                # First line
                self._matcher[lines.start, "l"] + self._matcher[cols.start :, "c"],
                # Middle lines
                (
                    self._matcher[lines.start + 1 : lines.stop - 1, "l"]
                    + self._matcher[:, "c"]
                    if lines.start + 1 < lines.stop - 1
                    else ""
                ),
                # Last line
                self._matcher[lines.stop - 1, "l"] + self._matcher[: cols.stop, "c"],
            )
            if x != ""
        )

    @staticmethod
    def shift_slice(s: slice) -> slice:
        """Shift a 0-indexed to 1-indexed slice."""
        return slice(
            s.start + 1 if s.start is not None else 1,
            s.stop + 1 if s.stop is not None else None,
        )


matcher = Matcher()


# Misc #
def _strip_comments(msg: bytes) -> Tuple[bytes, List[Tuple[int, int]]]:
    """Replace all comments in 'msg' with whitespace."""
    # pylint: disable=no-else-break
    # NOTE: Coqtop will ignore comments, but it makes it easier to inspect
    # commands in Coqtail (e.g. options in coqtop.do_option) if we remove them.
    nocom = []
    com_pos = []  # Remember comment offset and length
    off = 0
    nesting = 0

    while msg != b"":
        start = msg.find(b"(*")
        end = msg.find(b"*)")
        if start == -1 and (end == -1 or (end != -1 and nesting == 0)):
            # No comments left
            nocom.append(msg)
            break
        elif start != -1 and (start < end or end == -1):
            # New nested comment
            if nesting == 0:
                nocom.append(msg[:start])
                nocom.append(b" " * 2)  # Replace '(*'
                com_pos.append((off + start, 0))
            else:
                # Replace everything up to and including nested comment start.
                nocom.append(re.sub(rb"\S", b" ", msg[: start + 2]))
            msg = msg[start + 2 :]  # Skip '(*'
            off += start + 2
            nesting += 1
        elif end != -1 and (end < start or start == -1):
            # End of a comment
            # Replace everything up to and including comment end.
            nocom.append(re.sub(rb"\S", b" ", msg[: end + 2]))
            msg = msg[end + 2 :]
            off += end + 2
            nesting -= 1
            if nesting == 0:
                com_pos[-1] = (com_pos[-1][0], off - com_pos[-1][0])

    return b"".join(nocom), com_pos


def _find_opaque_proof_end(
    buffer: Sequence[bytes],
    ranges: Iterable[Mapping[str, Tuple[int, int]]],
) -> Optional[Mapping[str, Tuple[int, int]]]:
    """
    Find the end of the current proof to check if it's opaque.

    A proof that contains a non-opaque nested proof is considered
    non-opaque. A proof without an ending is also considered non-opaque.
    """
    pdepth = 1
    for range_ in ranges:
        message, _ = _strip_comments(_between(buffer, range_["start"], range_["stop"]))
        pstart = PROOF_START_PAT.match(message)
        pend = PROOF_END_PAT.match(message)
        if pstart is not None:
            pdepth += 1
        elif pend is not None:
            pdepth -= 1
            if pdepth == 0 and pend.group(1) in OPAQUE_PROOF_ENDS:
                # Found a non-nested opaque end.
                return _shrink_range_to_match(range_, pend.group(), pend.start(1))
            if pend.group(1) not in OPAQUE_PROOF_ENDS:
                # Found a non-opaque end.
                return None

        if pdepth == 0:
            break
    return None


def _shrink_range_to_match(
    range_: Mapping[str, Tuple[int, int]],
    match: bytes,
    match_off: int,
) -> Mapping[str, Tuple[int, int]]:
    """Shrink a sentence range to begin at the start of a given match."""
    nline_breaks = match.count(b"\n")
    sline = range_["start"][0] + nline_breaks
    # Offset the match start by the initial column if there are no line breaks,
    # else discount everything before the last line break.
    scol = match_off + (
        range_["start"][1] if nline_breaks == 0 else -(match.rindex(b"\n") + 1)
    )
    return {"start": (sline, scol), "stop": range_["stop"]}


def _find_diff(
    x: Iterable[T],
    y: Iterable[T],
    stop: Optional[int] = None,
) -> Optional[int]:
    """Locate the first differing element in 'x' and 'y' up to 'stop'
    (exclusive).
    """
    seq: Iterator[Tuple[int, Tuple[T, T]]] = enumerate(zip_longest(x, y))
    if stop is not None:
        seq = islice(seq, stop)
    return next((i for i, vs in seq if vs[0] != vs[1]), None)


def _diff_lines(
    old: Sequence[bytes],
    new: Sequence[bytes],
    stop: Tuple[int, int],
) -> Optional[Tuple[int, int]]:
    """Locate the first differing position in 'old' and 'new' lines of text up
    to 'stop' (exclusive).
    """
    sline, scol = stop
    linediff = _find_diff(old, new, sline + 1)
    if linediff is None:
        return None
    try:
        coldiff = _find_diff(
            old[linediff],
            new[linediff],
            scol if linediff == sline else None,
        )
    except IndexError:
        linediff = len(new) - 1
        coldiff = len(new[-1])
    if coldiff is None:
        return None
    return (linediff, coldiff)


def _char_isdigit(c: int) -> bool:
    return ord("0") <= c <= ord("9")


def _char_isspace(c: int) -> bool:
    return c in b" \t\n\r\x0b\f"


def _to_jsonl(obj: Any) -> bytes:
    return (json.dumps(obj) + "\n").encode("utf-8")
