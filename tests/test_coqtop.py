# -*- coding: utf8 -*-
"""
File: test_coqtop.py
Author: Wolf Honore

Description: Unit/integration tests for coqtop.py.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import pytest
from subprocess import check_output

from coqtop import Coqtop

# Test Values #
# Check current version
# TODO: something less ugly
VERSION = check_output(('coqtop', '--version')).split()[5].decode()
TIMEOUT = 3


# Test Helpers #
def get_state(coq):
    """Collect the state variables for coq."""
    return coq.root_state, coq.state_id, coq.states[:]


# Test Fixtures #
@pytest.fixture(scope='function')
def coq():
    """Return a Coqtop for each version."""
    ct = Coqtop(VERSION)
    if ct.start(timeout=TIMEOUT):
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
    coq.rewind(1)
    assert old_state == get_state(coq)
    coq.rewind(5)
    assert old_state == get_state(coq)


def test_dispatch_rewind(coq):
    """Rewinding should cancel out in_script dispatches."""
    old_state = get_state(coq)
    coq.dispatch('Let x := 1.', timeout=TIMEOUT)
    coq.rewind(1)
    assert old_state == get_state(coq)
    coq.dispatch('Print nat.', timeout=TIMEOUT)
    coq.rewind(1)
    assert old_state == get_state(coq)
    coq.dispatch('Test Silent.', timeout=TIMEOUT)
    coq.rewind(1)
    assert old_state == get_state(coq)
