# -*- coding: utf8 -*-
# Author: Wolf Honore
# pylint: disable=redefined-outer-name
"""Coq integration tests."""

from typing import Generator, List, Tuple
from unittest.mock import MagicMock, patch

import pytest

from coqtop import Coqtop
from xmlInterface import XMLInterface, join_tagged_tokens


# Test Helpers #
# TODO: Should also look at current goal, messages returned by Coqtop
def get_state(coq: Coqtop) -> Tuple[int, int, List[int]]:
    """Collect the state variables for coq."""
    return coq.root_state, coq.state_id, coq.states[:]


# Test Fixtures #
@pytest.fixture(scope="function")
def coq() -> Generator[Coqtop, None, None]:
    """Return a Coqtop for each version."""
    ct = Coqtop()
    if isinstance(ct.start(None, None, "", [])[0], dict):
        yield ct
        ct.stop()
    else:
        pytest.fail("Failed to create Coqtop instance")


# Test Cases #
def test_init_state(coq: Coqtop) -> None:
    """Make sure the state is initialized properly."""
    assert coq.root_state is not None
    assert coq.state_id == coq.root_state
    assert coq.states == []


def test_rewind_start(coq: Coqtop) -> None:
    """Rewinding at the start should do nothing."""
    old_state = get_state(coq)
    coq.rewind(1)
    assert old_state == get_state(coq)
    coq.rewind(5)
    assert old_state == get_state(coq)


def test_dispatch_rewind(coq: Coqtop) -> None:
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


def test_dispatch_not_in_script(coq: Coqtop) -> None:
    """Dispatch with not in_script arguments shouldn't change the state."""
    old_state = get_state(coq)
    coq.dispatch("Print nat.", in_script=False)
    assert old_state == get_state(coq)
    coq.dispatch("Test Silent.", in_script=False)
    assert old_state == get_state(coq)


def test_query_same_state_id(coq: Coqtop) -> None:
    """Dispatch with a query command shouldn't change the state id."""
    old_id = coq.state_id
    coq.dispatch("Print nat.")
    assert old_id == coq.state_id


def test_option_different_state_id(coq: Coqtop) -> None:
    """Dispatch with an option command should change the state id."""
    assert coq.xml is not None
    if coq.xml.version < (8, 5, 0):
        pytest.skip("Only 8.5+ uses state ids")
    old_id = coq.state_id
    coq.dispatch("Test Silent.")
    assert old_id != coq.state_id


@patch.object(Coqtop, "do_option")
@patch.object(Coqtop, "query")
@patch.object(Coqtop, "advance")
def test_dispatch_correct(
    advance: MagicMock,
    query: MagicMock,
    do_option: MagicMock,
    coq: Coqtop,
) -> None:
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


def test_dispatch_unicode(coq: Coqtop) -> None:
    """Should be able to use unicode characters."""
    succ, _, _, _ = coq.dispatch("Let α := 0.")
    assert succ
    succ, _, _, _ = coq.dispatch("Print α.")
    assert succ


def test_dispatch_unprintable(coq: Coqtop) -> None:
    """Should be able to handle unprintable characters."""
    succ, _, _, _ = coq.dispatch("Require Import String.")
    assert succ
    succ, out, _, _ = coq.dispatch("Compute String (Ascii.ascii_of_nat 0) EmptyString.")
    assert succ
    assert "\\x00" in out


def test_goals_no_change(coq: Coqtop) -> None:
    """Calling goals will not change the state."""
    succ, _, _, _ = coq.dispatch("Lemma x (n: nat) : False.")
    assert succ
    old_state = get_state(coq)
    (succ, _, goals, _) = coq.goals()
    assert succ
    assert goals is not None
    assert goals.bg == []
    assert goals.shelved == []
    assert goals.given_up == []
    assert len(goals.fg) == 1

    goal = goals.fg[0]
    assert len(goal.hyp) == 1
    hyp = (
        join_tagged_tokens(goal.hyp[0])
        if isinstance(goal.hyp[0], list)
        else goal.hyp[0]
    )
    ccl = join_tagged_tokens(goal.ccl) if isinstance(goal.ccl, list) else goal.ccl
    assert hyp == "n : nat"
    assert ccl == "False"

    assert old_state == get_state(coq)


def test_advance_fail(coq: Coqtop) -> None:
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
# def test_advance_stop(coq: Coqtop) -> None:
#     """If advance is interrupted then the state will not change."""
#     succ, _, _, _ = coq.dispatch("Goal True.")
#     assert succ
#     old_state = get_state(coq)
#     fail, _, _, _ = coq.dispatch("repeat eapply proj1.", _stop=True)
#     assert not fail
#     assert old_state == get_state(coq)


# def test_advance_stop_rewind(coq: Coqtop) -> None:
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


def test_dispatch_ignore_comments_newlines(coq: Coqtop) -> None:
    """Dispatch ignores comments and extraneous newlines."""
    succ, _, _, _ = coq.dispatch("(*pre*) Test Silent .")
    assert succ
    succ, _, _, _ = coq.dispatch(" Set  (*mid*) Silent.")
    assert succ
    succ, _, _, _ = coq.dispatch("(*pre*) Unset\n (*mid*)\nSilent  (*post*).")
    assert succ


def test_recognize_not_option(coq: Coqtop) -> None:
    """Dispatch correctly identifies certain lines as not option commands."""
    succ, _, _, _ = coq.dispatch("Require Import\nSetoid.")
    assert succ
    succ, _, _, _ = coq.dispatch("Variable x :\nSet.")
    assert succ
    succ, _, _, _ = coq.dispatch("Definition Test := Type.")
    assert succ
    succ, _, _, _ = coq.dispatch("Variable y :\n Test.")
    assert succ


def test_recognize_not_query(coq: Coqtop) -> None:
    """Dispatch correctly identifies certain lines as not query commands."""
    assert coq.xml is not None
    if coq.xml.version < (8, 5, 0):
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


def test_start_invalid_option() -> None:
    """Passing an invalid option on startup fails gracefully."""
    ct = Coqtop()
    res, stderr = ct.start(None, None, "", ["--fake"])
    assert isinstance(res, str)
    assert stderr == ""


def test_start_warning() -> None:
    """Warnings do not cause startup to fail."""
    ct = Coqtop()
    res, stderr = ct.start(None, None, "", ["-R", "fake", "Fake"])
    assert isinstance(res, dict)
    assert ct.xml is not None
    # Some versions of Coq don't print warnings in the expected format.
    if ct.xml.warnings_wf:
        assert stderr.startswith("Warning:")


@patch("coqtop.XMLInterface", autospec=True)
def test_start_invalid_xml(fake_interface: MagicMock) -> None:
    """Invalid XML commands do not cause Coqtail to hang."""
    # Create a fake XMLInterfaceBase and patch init() to return invalid XML.
    # Wrap the real XMLInterfaceBase so all other methods work as usual.
    real_xml = XMLInterface(None, None)[0]
    if not real_xml.warnings_wf:
        pytest.skip(f"{real_xml.str_version} doesn't print warnings correctly")
    fake_xml = MagicMock(wraps=real_xml)
    fake_xml.init.return_value = ("Init", b"<bad_xml></bad_xml>")
    fake_interface.return_value = (fake_xml, "")
    ct = Coqtop()
    res, stderr = ct.start(None, None, "", [])
    assert isinstance(res, str)
    assert stderr != ""
