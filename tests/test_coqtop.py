# -*- coding: utf8 -*-
"""
File: test_coqtop.py
Author: Wolf Honore

Description: Unit/integration tests for coqtop.py.
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
VERSION = check_output(('coqtop', '--version')).split()[5].decode()
TIMEOUT = 3
DONE = False


# Test Helpers #
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


def call_and_wait(func, *args, **kwargs):
    """Call a Coqtop function and wait for it to finish."""
    global DONE
    DONE = False

    if '_stop' in kwargs:
        stop = kwargs['_stop']
        del kwargs['_stop']
    else:
        stop = False

    func_iter = func(*args, **kwargs)

    next(func_iter)
    while True:
        wait_done(stop)
        ret = func_iter.send(stop)
        if ret is not None:
            return ret


# Test Fixtures #
@pytest.fixture(scope='function')
def coq():
    """Return a Coqtop for each version."""
    ct = Coqtop(VERSION, set_done)
    if call_and_wait(ct.start):
        yield ct
        ct.stop()
    else:
        print('Failed to create Coqtop instance')
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
    call_and_wait(coq.rewind, 1)
    assert old_state == get_state(coq)
    call_and_wait(coq.rewind, 5)
    assert old_state == get_state(coq)


def test_dispatch_rewind(coq):
    """Rewinding should cancel out in_script dispatches."""
    succ, _, _ = call_and_wait(coq.dispatch, 'Let a := 0.', timeout=TIMEOUT)
    old_state = get_state(coq)

    succ, _, _ = call_and_wait(coq.dispatch, 'Let x := 1.', timeout=TIMEOUT)
    assert succ
    call_and_wait(coq.rewind, 1)
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq.dispatch, 'Print nat.', timeout=TIMEOUT)
    assert succ
    call_and_wait(coq.rewind, 1)
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq.dispatch, 'Test Silent.', timeout=TIMEOUT)
    assert succ
    call_and_wait(coq.rewind, 1)
    assert old_state == get_state(coq)


def test_dispatch_not_in_script(coq):
    """Dispatch with not in_script arguments shouldn't change the state."""
    old_state = get_state(coq)
    call_and_wait(coq.dispatch, 'Print nat.', in_script=False, timeout=TIMEOUT)
    assert old_state == get_state(coq)
    call_and_wait(coq.dispatch, 'Test Silent.', in_script=False,
                  timeout=TIMEOUT)
    assert old_state == get_state(coq)


def test_goals_no_change(coq):
    """Calling goals will not change the state."""
    old_state = get_state(coq)
    call_and_wait(coq.goals, timeout=TIMEOUT)
    assert old_state == get_state(coq)


def test_mk_cases_no_change(coq):
    """Calling mk_cases will not change the state."""
    old_state = get_state(coq)
    call_and_wait(coq.mk_cases, 'nat', timeout=TIMEOUT)
    assert old_state == get_state(coq)


def test_advance_fail(coq):
    """If advance fails then the state will not change."""
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq.dispatch, 'SyntaxError', timeout=TIMEOUT)
    assert not fail
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq.dispatch, 'Lemma x : False.',
                               timeout=TIMEOUT)
    assert succ
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq.dispatch, 'reflexivity.', timeout=TIMEOUT)
    assert not fail
    assert old_state == get_state(coq)


def test_advance_stop(coq):
    """If advance is interrupted then the state will not change."""
    succ, _, _ = call_and_wait(coq.dispatch, 'Ltac inf := inf.',
                               timeout=TIMEOUT)
    assert succ
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq.dispatch, 'Let x := ltac:(inf).',
                               timeout=TIMEOUT, _stop=True)
    assert not fail
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq.dispatch, 'Let x := 1.', timeout=TIMEOUT)
    assert succ


def test_advance_same_stop(coq):
    """If advance is interrupted then Coqtop will rollback."""
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq.dispatch, 'Let x := 1.', timeout=TIMEOUT,
                               _stop=True)
    assert not fail
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq.dispatch, 'Let x := 1.', timeout=TIMEOUT)
    assert succ


def test_query_stop(coq):
    """If query is interrupted then the state will not change."""
    old_state = get_state(coq)
    fail, _, _ = call_and_wait(coq.dispatch, 'Print nat.', timeout=TIMEOUT,
                               _stop=True)
    assert not fail
    assert old_state == get_state(coq)
    succ, _, _ = call_and_wait(coq.dispatch, 'Let x := 1.', timeout=TIMEOUT)
    assert succ
