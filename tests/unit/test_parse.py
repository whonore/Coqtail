# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Sentence parsing unit tests."""

from typing import Iterable, Sequence, Tuple, Union

import pytest

from coqtail import NoDotError, UnmatchedError, _get_message_range, _strip_comments

# Test name, input lines, start position, stop position or exception
# The start can be omitted, in which case it defaults to (0, 0).
# The stop can be a position, or an exception, in which case it is expected to
# be raised.
_ParseIn = Sequence[str]
ParseStart = Tuple[int, int]
ParseStop = Union[Exception, Tuple[int, int]]
_ParseTest = Union[
    Tuple[str, _ParseIn, ParseStop],
    Tuple[str, _ParseIn, ParseStart, ParseStop],
]
ParseIn = Sequence[bytes]
ParseTest = Tuple[str, ParseIn, ParseStart, ParseStop]

_parse_tests: Sequence[_ParseTest] = [
    # Valid tests, no offset
    ("word", ["A."], (0, 1)),
    ("word2", ["A B."], (0, 3)),
    ("lspace", [" A."], (0, 2)),
    ("rspace", ["A. "], (0, 1)),
    ("ltab", ["\tA."], (0, 2)),
    ("rtab", ["A.\t"], (0, 1)),
    ("comment pre", ["(* c. *) A."], (0, 10)),
    ("comment mid", ["A (* c. *) B."], (0, 12)),
    ("comment post", ["A (* c. *)."], (0, 10)),
    ("comment nest", ["A (* (* c. *) *)."], (0, 16)),
    ("str", ['A "B.".'], (0, 6)),
    ("str nest", ['A """B.""".'], (0, 10)),
    ("qualified", ["A.B."], (0, 3)),
    ("multi line", ["A", "B."], (1, 1)),
    ("multi line comment", ["A (*", ". *) B."], (1, 6)),
    ("multi line string", ['A "', '." B.'], (1, 4)),
    ("multi line comment nest", ["A (* (*", "c. ", "*) *) ."], (2, 6)),
    ("extra words", ["A. B."], (0, 1)),
    ("bullet -", ["- A."], (0, 0)),
    ("bullet +", ["+ A."], (0, 0)),
    ("bullet *", ["* A."], (0, 0)),
    ("bullet --", ["-- A."], (0, 1)),
    ("bullet ++", ["++ A."], (0, 1)),
    ("bullet **", ["** A."], (0, 1)),
    ("bullet {", ["{ A. }"], (0, 0)),
    ("bullet {{", ["{{ A. }}"], (0, 0)),
    ("bullet {{ 2", ["{{ A. }}"], (0, 1), (0, 1)),
    ("dot3", ["A..."], (0, 3)),
    ("large space", ("A" + ("\n" * 5000) + ".").split("\n"), (5000, 0)),
    ("large comment", ("(*" + ("\n" * 5000) + "*) A.").split("\n"), (5000, 4)),
    ("attribute word", ["#[A] B."], (0, 6)),
    ("attribute bullet {", ["#[A] { A. }"], (0, 5)),
    ("attribute string", ['#[A="B]."] C.'], (0, 12)),
    # Accept (tactic in *)
    ("star paren ok", ["A *) ."], (0, 5)),
    # or a bullet followed by a tactic notation that starts with ')'
    ("star paren ok post comment", ["(* A *) *) ."], (0, 8)),
    # Valid tests, offset
    ("bullet }", ["{ A. }"], (0, 4), (0, 5)),
    ("bullet dot } 1", ["{ A. }."], (0, 4), (0, 5)),
    ("bullet dot } 2", ["{ A. }."], (0, 6), (0, 6)),
    # Valid tests for non-bracketed goal selectors
    ("select no spacing", ["1:t."], (0, 3)),
    ("select space after colon", ["1: t."], (0, 4)),
    ("select space before space after", ["1 : t."], (0, 5)),
    ("select space before colon", ["1 :t."], (0, 4)),
    # Valid tests with bracketed goal selectors
    ("focus no spacing", ["1:{"], (0, 2)),
    ("focus trailing spacing", ["1:{ "], (0, 2)),
    ("focus space after colon", ["1: {"], (0, 3)),
    ("focus space before space after", ["1 : {"], (0, 4)),
    ("focus double space before double space after", ["1  :  {"], (0, 6)),
    ("focus space before colon", ["1 :{"], (0, 3)),
    ("focus trailing command no spaces", ["2:{t."], (0, 2)),
    ("focus trailing command with spaces", ["2 : { t."], (0, 4)),
    # elpi
    ("elpi antiquote", ["Elpi Accumulate lp:{{ }}."], (0, 24)),
    ("elpi antiquote quote", ["Elpi Accumulate lp:{{ {{ }}. }}."], (0, 31)),
    (
        "elpi antiquote quote antiquote",
        ["Elpi Accumulate lp:{{ {{ lp:{{ }} }}. }}."],
        (0, 40),
    ),
    # Invalid tests
    ("no dot", ["A"], NoDotError()),
    ("dot2", ["A.."], NoDotError()),
    ("unclosed comment pre", ["(* ."], UnmatchedError("(*", (0, 0))),
    ("unclosed comment", ["A (* ."], UnmatchedError("(*", (0, 2))),
    ("unclosed comment nest pre", ["(* (* A *) ."], UnmatchedError("(*", (0, 0))),
    ("unclosed string", ['A " .'], UnmatchedError('"', (0, 2))),
    ("unclosed attribute", ["#[A B."], UnmatchedError("#[", (0, 0))),
    ("unclosed string attribute", ['#[A="B] C.'], UnmatchedError("#[", (0, 0))),
    ("only white", [" "], NoDotError()),
    ("empty", [""], NoDotError()),
]
# Default 'start' to (0, 0)
# Not sure why, but the first ignore is needed to silence "Generator has
# incompatible item type".
# The second one silences "Tuple index out of range".
parse_tests: Iterable[ParseTest] = (
    (
        t[0],  # type: ignore[misc]
        [s.encode("utf-8") for s in t[1]],
        t[2] if len(t) == 4 else (0, 0),
        t[3] if len(t) == 4 else t[2],  # type: ignore[misc]
    )
    for t in _parse_tests
)


@pytest.mark.parametrize("_name, lines, start, stop_or_ex", parse_tests)
def test_parse(
    _name: str,
    lines: ParseIn,
    start: ParseStart,
    stop_or_ex: ParseStop,
) -> None:
    """'_get_message_range(lines)' should range from 'start' to 'stop'."""
    if isinstance(stop_or_ex, tuple):
        assert _get_message_range(lines, start) == {"start": start, "stop": stop_or_ex}
    else:
        with pytest.raises(type(stop_or_ex)) as e:
            _get_message_range(lines, start)
        if isinstance(stop_or_ex, UnmatchedError):
            assert isinstance(e.value, UnmatchedError)
            assert str(e.value) == str(stop_or_ex)
            assert e.value.range == stop_or_ex.range


# Test name, input string, output string and comment positions
CommentIn = bytes
CommentOut = Tuple[bytes, Sequence[Tuple[int, int]]]
CommentTest = Tuple[str, CommentIn, CommentOut]

com_tests: Sequence[CommentTest] = (
    ("no comment", b"abc", (b"abc", [])),
    ("pre", b"(*abc*)def", (b" def", [(0, 7)])),
    ("mid", b"ab(* c *)de", (b"ab de", [(2, 7)])),
    ("post", b"abc(*def *)", (b"abc", [(3, 8)])),
    (
        "multi",
        b"abc (* com1 *)  def (*com2 *) g",
        (b"abc    def   g", [(4, 10), (20, 9)]),
    ),
    ("nested", b"abc (* c1 (*c2 (*c3*) (*c4*) *) *)def", (b"abc  def", [(4, 30)])),
    ("no comment newline", b"\nabc\n\n", (b"\nabc\n\n", [])),
    ("pre newline", b"(*ab\nc*)d\nef", (b" d\nef", [(0, 8)])),
    ("mid newline", b"ab(* c *)\nde", (b"ab \nde", [(2, 7)])),
    ("post newline", b"abc\n(*def *)\n", (b"abc\n \n", [(4, 8)])),
    (
        "multi newline",
        b"abc (* com1 *)\n def \n(*\ncom2 *) g",
        (b"abc  \n def \n  g", [(4, 10), (21, 10)]),
    ),
    (
        "nested newline",
        b"\nabc (* c1 (*c2 \n\n(*c3\n*) (*c4*) *) *)def\n",
        (b"\nabc  def\n", [(5, 33)]),
    ),
    ("star paren", b"abc *)", (b"abc *)", [])),
    ("star paren post comment", b"(*abc*) *)", (b"  *)", [(0, 7)])),
)


@pytest.mark.parametrize("_name, msg, expected", com_tests)
def test_strip_comment(_name: str, msg: CommentIn, expected: CommentOut) -> None:
    """_strip_comments() should remove only comments"""
    assert _strip_comments(msg) == expected
