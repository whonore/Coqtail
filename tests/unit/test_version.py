# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Version parsing unit tests."""

import pytest

from xmlInterface import parse_version

tests = (
    ("1.2.3", (1, 2, 3)),
    ("1.2pl3", (1, 2, 3)),
    ("1.2", (1, 2, 0)),
    ("1.2+alpha3", (1, 2, 0)),
    ("1.2+alpha", (1, 2, 0)),
)


@pytest.mark.parametrize("version, expected", tests)
def test_matcher(version, expected):
    """parse_version parses versions correctly."""
    assert parse_version(version) == expected
