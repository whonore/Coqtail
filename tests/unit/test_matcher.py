# -*- coding: utf8 -*-
# Author: Wolf Honore
# mypy: ignore-errors
"""Match patterns unit tests."""

import pytest

from coqtail import matcher

tests = (
    ("Both lines, both cols", matcher[1:5, 1:5], r"\%2l\%>1c\|\%>2l\%<5l\|\%5l\%<6c"),
    ("Both lines, 1 start col", matcher[1:5, 0:5], r"\%2l\|\%>2l\%<5l\|\%5l\%<6c"),
    ("Both lines, no start col", matcher[1:5, :5], r"\%2l\|\%>2l\%<5l\|\%5l\%<6c"),
    ("Both lines, no end col", matcher[1:5, 1:], r"\%2l\%>1c\|\%>2l\%<5l\|\%5l"),
    ("Both lines, no col", matcher[1:5, :], r"\%2l\|\%>2l\%<5l\|\%5l"),
    ("0 start line, both cols", matcher[0:5, 1:5], r"\%1l\%>1c\|\%>1l\%<5l\|\%5l\%<6c"),
    ("No start line, both cols", matcher[:5, 1:5], r"\%1l\%>1c\|\%>1l\%<5l\|\%5l\%<6c"),
    ("One line, both cols", matcher[1:2, 1:5], r"\%2l\%>1c\%<6c"),
    ("One line, no col", matcher[1:2, :], r"\%2l"),
    ("Two lines, both cols", matcher[1:3, 1:5], r"\%2l\%>1c\|\%3l\%<6c"),
)


@pytest.mark.parametrize("_name, match, expected", tests)
def test_matcher(_name, match, expected):
    """Matcher builds match regexes correctly."""
    assert match == expected
