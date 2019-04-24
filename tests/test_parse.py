# -*- coding: utf8 -*-
"""
File: test_parse.py
Author: Wolf Honore

Description: Unit tests for parsing in coqtail.py.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import sys
try:
    from unittest.mock import Mock
except ImportError:
    from mock import Mock
import pytest

# Mock vim modules
sys.modules['vim'] = Mock()
sys.modules['vimbufsync'] = Mock()
from coqtail import _get_message_range, _strip_comments

# Test Values #
tests = (
    # Valid tests, no offset
    ('word', ['A.'], (0, 1)),
    ('word2', ['A B.'], (0, 3)),
    ('lwhite', [' A.'], (0, 2)),
    ('rwhite', ['A. '], (0, 1)),
    ('comment pre', ['(* c. *) A.'], (0, 10)),
    ('comment mid', ['A (* c. *) B.'], (0, 12)),
    ('comment post', ['A (* c. *).'], (0, 10)),
    ('comment nest', ['A (* (* c. *) *).'], (0, 16)),
    ('str', ['A "B.".'], (0, 6)),
    ('str nest', ['A """B.""".'], (0, 10)),
    ('qualified', ['A.B.'], (0, 3)),
    ('multi line', ['A', 'B.'], (1, 1)),
    ('multi line comment', ['A (*', '. *) B.'], (1, 6)),
    ('multi line string', ['A "', '." B.'], (1, 4)),
    ('extra words', ['A. B.'], (0, 1)),
    ('bullet -', ['- A.'], (0, 0)),
    ('bullet +', ['+ A.'], (0, 0)),
    ('bullet *', ['* A.'], (0, 0)),
    ('bullet --', ['-- A.'], (0, 1)),
    ('bullet ++', ['++ A.'], (0, 1)),
    ('bullet **', ['** A.'], (0, 1)),
    ('bullet {', ['{ A. }'], (0, 0)),
    ('bullet {{', ['{{ A. }}'], (0, 0)),
    ('bullet {{ 2', ['{{ A. }}'], (0, 1), (0, 1)),
    ('dot3', ['A...'], (0, 3)),
    ('large space', ('A' + ('\n' * 5000) + '.').split('\n'), (5000, 0)),
    ('large comment', ('(*' + ('\n' * 5000) + '*) A.').split('\n'), (5000, 4)),

    # Valid tests, offset
    ('bullet }', ['{ A. }'], (0, 4), (0, 5)),
    ('bullet dot } 1', ['{ A. }.'], (0, 4), (0, 5)),
    ('bullet dot } 2', ['{ A. }.'], (0, 6), (0, 6)),

    # Invalid tests,
    ('no dot', ['A'], None),
    ('dot2', ['A..'], None),
    ('unclosed comment pre', ['(* .'], None),
    ('unclosed comment', ['A (* .'], None),
    ('unclosed string', ['A " .'], None),
    ('only white', [' '], None),
    ('empty', [''], None)
)

# Default 'start' to (0, 0)
tests = ((t[0], t[1],
          t[2] if len(t) == 4 else (0, 0), t[3] if len(t) == 4 else t[2])
         for t in tests)


# Test Cases #
@pytest.mark.parametrize('_name, lines, start, stop', tests)
def test_parse(_name, lines, start, stop):
    """'_get_message_range(lines)' should range from 'start' to 'stop'."""
    if stop is not None:
        mrange = {'start': start, 'stop': stop}
    else:
        mrange = None
    assert _get_message_range(lines, start) == mrange


com_tests = (
    ('no comment', 'abc', 'abc'),
    ('pre', '(*abc*)def', ' def'),
    ('mid', 'ab(* c *)de', 'ab de'),
    ('post', 'abc(*def *)', 'abc'),
    ('multi', 'abc (* com1 *)  def (*com2 *) g', 'abc    def   g'),
    ('nested', 'abc (* c1 (*c2 (*c3*) (*c4*) *) *)def', 'abc  def'),
    ('no comment newline', '\nabc\n\n', '\nabc\n\n'),
    ('pre newline', '(*ab\nc*)d\nef', ' d\nef'),
    ('mid newline', 'ab(* c *)\nde', 'ab \nde'),
    ('post newline', 'abc\n(*def *)\n', 'abc\n \n'),
    ('multi newline', 'abc (* com1 *)\n def \n(*\ncom2 *) g',
     'abc  \n def \n  g'),
    ('nested newline', '\nabc (* c1 (*c2 \n\n(*c3\n*) (*c4*) *) *)def\n',
     '\nabc  def\n')
)


@pytest.mark.parametrize('_name, msg, expected', com_tests)
def test_strip_comment(_name, msg, expected):
    """_strip_comments() should remove only comments"""
    assert _strip_comments(msg) == expected
