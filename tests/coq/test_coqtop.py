# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Coq integration tests."""

from __future__ import absolute_import, division, print_function

from subprocess import check_output

import pytest

try:
    from unittest.mock import patch
except ImportError:
    from mock import patch

from coqtop import Coqtop

# Test Values #
# Check current version
# TODO: something less ugly
VERSION = check_output(("coqtop", "--version")).split()[5].decode()


# Test Helpers #
# TODO: Should also look at current goal, messages returned by Coqtop
def get_state(coq):
    """Collect the state variables for coq."""
    return coq.root_state, coq.state_id, coq.states[:]


# Test Fixtures #
@pytest.fixture(scope="function")
def coq():
    """Return a Coqtop for each version."""
    ct = Coqtop(VERSION)
    if ct.start(None, None, "")[0] is None:
        yield ct
        ct.stop()
    else:
        pytest.fail("Failed to create Coqtop instance")


# Test Cases #
def test_init_state(coq):
    """Make sure the state is initialized properly."""
    assert coq.root_state is not None
    assert coq.state_id == coq.root_state
    assert coq.states == []


def test_rewind_start(coq):
    """Rewinding at the start should do nothing."""
    old_state = get_state(coq)
    coq.rewind(1)
    assert old_state == get_state(coq)
    coq.rewind(5)
    assert old_state == get_state(coq)


def test_dispatch_rewind(coq):
    """Rewinding should cancel out in_script dispatches."""
    succ, _, _, _ = coq.dispatch("Let a := 0.")
    old_state = get_state(coq)

    succ, _, _, _ = coq.dispatch("Let x := 1.")
    assert succ
    coq.rewind(1)
    assert old_state == get_state(coq)
    succ, _, _, _ = coq.dispatch("Print nat.")
    assert succ
    coq.rewind(1)
    assert old_state == get_state(coq)
    succ, _, _, _ = coq.dispatch("Test Silent.")
    assert succ
    coq.rewind(1)
    assert old_state == get_state(coq)


def test_dispatch_not_in_script(coq):
    """Dispatch with not in_script arguments shouldn't change the state."""
    old_state = get_state(coq)
    coq.dispatch("Print nat.", in_script=False)
    assert old_state == get_state(coq)
    coq.dispatch("Test Silent.", in_script=False)
    assert old_state == get_state(coq)


def test_query_same_state_id(coq):
    """Dispatch with a query command shouldn't change the state id."""
    old_id = coq.state_id
    coq.dispatch("Print nat.")
    assert old_id == coq.state_id


def test_option_different_state_id(coq):
    """Dispatch with an option command should change the state id."""
    if coq.xml.versions < (8, 5, 0):
        pytest.skip("Only 8.5+ uses state ids")
    old_id = coq.state_id
    coq.dispatch("Test Silent.")
    assert old_id != coq.state_id


@patch.object(Coqtop, "do_option")
@patch.object(Coqtop, "query")
@patch.object(Coqtop, "advance")
def test_dispatch_correct(advance, query, do_option, coq):
    """Dispatch calls the correct methods."""
    advance.return_value = iter((None, None))
    query.return_value = iter((None, None))
    do_option.return_value = iter((None, None))
    coq.dispatch("Let x := 0.")
    advance.assert_called()
    coq.dispatch("Show.", in_script=False)
    query.assert_called()
    coq.dispatch("Test Silent.", in_script=False)
    do_option.assert_called()


def test_dispatch_unicode(coq):
    """Should be able to use unicode characters."""
    succ, _, _, _ = coq.dispatch("Let α := 0.")
    assert succ
    succ, _, _, _ = coq.dispatch("Print α.")
    assert succ


def test_goals_no_change(coq):
    """Calling goals will not change the state."""
    old_state = get_state(coq)
    coq.goals()
    assert old_state == get_state(coq)


def test_advance_fail(coq):
    """If advance fails then the state will not change."""
    old_state = get_state(coq)
    fail, _, _, _ = coq.dispatch("SyntaxError")
    assert not fail
    assert old_state == get_state(coq)
    succ, _, _, _ = coq.dispatch("Lemma x : False.")
    assert succ
    old_state = get_state(coq)
    fail, _, _, _ = coq.dispatch("reflexivity.")
    assert not fail
    assert old_state == get_state(coq)


# TODO: move interrupt tests to a separate file
# def test_advance_stop(coq):
#     """If advance is interrupted then the state will not change."""
#     succ, _, _, _ = coq.dispatch("Goal True.")
#     assert succ
#     old_state = get_state(coq)
#     fail, _, _, _ = coq.dispatch("repeat eapply proj1.", _stop=True)
#     assert not fail
#     assert old_state == get_state(coq)


# def test_advance_stop_rewind(coq):
#     """If advance is interrupted then succeeds, rewind will succeed."""
#     old_state = get_state(coq)
#     succ, _, _, _ = coq.dispatch("Goal True.")
#     assert succ
#     fail, _, _, _ = coq.dispatch("repeat eapply proj1.", _stop=True)
#     assert not fail
#     succ, _, _, _ = coq.dispatch("exact I.")
#     assert succ
#     coq.rewind(5)
#     assert old_state == get_state(coq)


def test_dispatch_ignore_comments_newlines(coq):
    """Dispatch ignores comments and extraneous newlines."""
    succ, _, _, _ = coq.dispatch("(*pre*) Test Silent .")
    assert succ
    succ, _, _, _ = coq.dispatch(" Set  (*mid*) Silent.")
    assert succ
    succ, _, _, _ = coq.dispatch("(*pre*) Unset\n (*mid*)\nSilent  (*post*).")
    assert succ


def test_recognize_not_option(coq):
    """Dispatch correctly identifies certain lines as not option commands."""
    succ, _, _, _ = coq.dispatch("Require Import\nSetoid.")
    assert succ
    succ, _, _, _ = coq.dispatch("Variable x :\nSet.")
    assert succ
    succ, _, _, _ = coq.dispatch("Definition Test := Type.")
    assert succ
    succ, _, _, _ = coq.dispatch("Variable y :\n Test.")
    assert succ


def test_recognize_not_query(coq):
    """Dispatch correctly identifies certain lines as not query commands."""
    if coq.xml.versions < (8, 5, 0):
        pytest.skip("Only 8.5+ uses state ids")
    succ, _, _, _ = coq.dispatch("Definition Print := Type.")
    assert succ
    old_id = coq.state_id
    succ, _, _, _ = coq.dispatch("Variable x :\nPrint.")
    assert succ
    assert old_id != coq.state_id
    succ, _, _, _ = coq.dispatch("Definition Abouts := Type.")
    assert succ
    old_id = coq.state_id
    succ, _, _, _ = coq.dispatch("Variable y :\n Abouts.")
    assert succ
    assert old_id != coq.state_id
