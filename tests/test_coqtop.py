# -*- coding: utf8 -*-
"""
File: test_coqtop.py
Author: Wolf Honore

Description: Unit/integration tests for coqtop.py.
TODO: test timeout similarly to manual interrupt
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

from subprocess import check_output

import pytest

from coqtop import Coqtop

# Test Values #
# Check current version
# TODO: something less ugly
VERSION = check_output(("coqtop", "--version")).split()[5].decode()
DONE = False


# Test Helpers #
# TODO: Should also look at current goal, messages returned by Coqtop
def get_state(coq):
    """Collect the state variables for coq."""
    return coq.root_state, coq.state_id, coq.states[:]


def set_done():
    """To be called when Coqtop is done."""
    global DONE
    DONE = True


def wait_done(stop):
    """Wait for Coqtop to finish."""
    global DONE
    while not DONE and not stop:
        pass


def call_and_wait(coq, func, *args, **kwargs):
    """Call a Coqtop function and wait for it to finish."""
    global DONE
    DONE = False

    if "_stop" in kwargs:
        stop = kwargs["_stop"]
        del kwargs["_stop"]
    else:
        stop = False

    func_iter = func(*args, **kwargs)

    next(func_iter)
    if stop:
        coq.interrupt()
    while True:
        wait_done(stop)
        ret = func_iter.send(stop)
        if ret is not None:
            return ret


# Test Fixtures #
@pytest.fixture(scope="function")
def coq():
    """Return a Coqtop for each version."""
    ct = Coqtop(VERSION, set_done)
    if call_and_wait(ct, ct.start):
        yield ct
        ct.stop()
    else:
        print("Failed to create Coqtop instance")
        yield None


# Test Cases #
def test_init_state(coq):
    """Make sure the state is initialized properly."""
    assert coq.root_state is not None
    assert coq.state_id == coq.root_state
    assert coq.states == []


def test_rewind_start(coq):
    """Rewinding at the start should do nothing."""
    old_state = get_state(coq)
    call_and_wait(coq, coq.rewind, 1)
    assert old_state == get_state(coq)
    call_and_wait(coq, coq.rewind, 5)
    assert old_state == get_state(coq)


def test_dispatch_rewind(coq):
    """Rewinding should cancel out in_script dispatches."""
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Let a := 0.")
    old_state = get_state(coq)

    succ, _, _ = call_and_wait(coq, coq.dispatch, "Let x := 1.")
    assert succ
    call_and_wait(coq, coq.rewind, 1)
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Print nat.")
    assert succ
    call_and_wait(coq, coq.rewind, 1)
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Test Silent.")
    assert succ
    call_and_wait(coq, coq.rewind, 1)
    assert old_state == get_state(coq)


def test_dispatch_not_in_script(coq):
    """Dispatch with not in_script arguments shouldn't change the state."""
    old_state = get_state(coq)
    call_and_wait(coq, coq.dispatch, "Print nat.", in_script=False)
    assert old_state == get_state(coq)
    call_and_wait(coq, coq.dispatch, "Test Silent.", in_script=False)
    assert old_state == get_state(coq)


def test_option_query_same_state_id(coq):
    """Dispatch with a query or option command shouldn't change the state id."""
    old_id = coq.state_id
    call_and_wait(coq, coq.dispatch, "Print nat.")
    assert old_id == coq.state_id
    call_and_wait(coq, coq.dispatch, "Test Silent.")
    assert old_id == coq.state_id


def test_dispatch_unicode(coq):
    """Should be able to use unicode characters."""
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Let α := 0.")
    assert succ
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Print α.")
    assert succ


def test_goals_no_change(coq):
    """Calling goals will not change the state."""
    old_state = get_state(coq)
    call_and_wait(coq, coq.goals)
    assert old_state == get_state(coq)


def test_mk_cases_no_change(coq):
    """Calling mk_cases will not change the state."""
    old_state = get_state(coq)
    call_and_wait(coq, coq.mk_cases, "nat")
    assert old_state == get_state(coq)


def test_advance_fail(coq):
    """If advance fails then the state will not change."""
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq, coq.dispatch, "SyntaxError")
    assert not fail
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Lemma x : False.")
    assert succ
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq, coq.dispatch, "reflexivity.")
    assert not fail
    assert old_state == get_state(coq)


def test_advance_stop(coq):
    """If advance is interrupted then the state will not change."""
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Goal True.")
    assert succ
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq, coq.dispatch, "repeat eapply proj1.", _stop=True)
    assert not fail
    assert old_state == get_state(coq)


def test_advance_stop_rewind(coq):
    """If advance is interrupted then succeeds, rewind will succeed."""
    old_state = get_state(coq)
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Goal True.")
    assert succ
    fail, _, _ = call_and_wait(coq, coq.dispatch, "repeat eapply proj1.", _stop=True)
    assert not fail
    succ, _, _ = call_and_wait(coq, coq.dispatch, "exact I.")
    assert succ
    call_and_wait(coq, coq.rewind, 5)
    assert old_state == get_state(coq)


def test_dispatch_ignore_comments_newlines(coq):
    """Dispatch ignores comments and extraneous newlines."""
    succ, _, _ = call_and_wait(coq, coq.dispatch, "(*pre*) Test Silent .")
    assert succ
    succ, _, _ = call_and_wait(coq, coq.dispatch, " Set  (*mid*) Silent.")
    assert succ
    succ, _, _ = call_and_wait(
        coq, coq.dispatch, "(*pre*) Unset\n (*mid*)\nSilent  (*post*)."
    )
    assert succ


def test_recognize_not_option(coq):
    """Dispatch correctly identifies certain lines as not option commands."""
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Require Import\nSetoid.")
    assert succ
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Variable x :\nSet.")
    assert succ
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Definition Test := Type.")
    assert succ
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Variable y :\n Test.")
    assert succ


def test_recognize_not_query(coq):
    """Dispatch correctly identifies certain lines as not query commands."""
    if coq.xml.versions < (8, 5, 0):
        pytest.skip('Only 8.5+ uses state ids')
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Definition Print := Type.")
    assert succ
    old_id = coq.state_id
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Variable x :\nPrint.")
    assert succ
    assert old_id != coq.state_id
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Definition Abouts := Type.")
    assert succ
    old_id = coq.state_id
    succ, _, _ = call_and_wait(coq, coq.dispatch, "Variable y :\n Abouts.")
    assert succ
    assert old_id != coq.state_id
