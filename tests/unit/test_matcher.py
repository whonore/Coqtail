# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Match patterns unit tests."""

from __future__ import absolute_import, division, print_function

import pytest

from coqtail import matcher

tests = (
    ("Both lines, both cols", matcher[1:5, 1:5], r"\%2l\%>1v\|\%>2l\%<5l\|\%5l\%<6v"),
    ("Both lines, 1 start col", matcher[1:5, 0:5], r"\%2l\|\%>2l\%<5l\|\%5l\%<6v"),
    ("Both lines, no start col", matcher[1:5, :5], r"\%2l\|\%>2l\%<5l\|\%5l\%<6v"),
    ("Both lines, no end col", matcher[1:5, 1:], r"\%2l\%>1v\|\%>2l\%<5l\|\%5l"),
    ("Both lines, no col", matcher[1:5, :], r"\%2l\|\%>2l\%<5l\|\%5l"),
    ("0 start line, both cols", matcher[0:5, 1:5], r"\%1l\%>1v\|\%>1l\%<5l\|\%5l\%<6v"),
    ("No start line, both cols", matcher[:5, 1:5], r"\%1l\%>1v\|\%>1l\%<5l\|\%5l\%<6v"),
    ("One line, both cols", matcher[1:2, 1:5], r"\%2l\%>1v\%<6v"),
    ("One line, no col", matcher[1:2, :], r"\%2l"),
    ("Two lines, both cols", matcher[1:3, 1:5], r"\%2l\%>1v\|\%3l\%<6v"),
)


@pytest.mark.parametrize("_name, match, expected", tests)
def test_matcher(_name, match, expected):
    """Matcher builds match regexes correctly."""
    assert match == expected
