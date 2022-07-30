# -*- coding: utf8 -*-
# Author: Wolf Honore
# pylint: disable=protected-access,redefined-outer-name
"""XMLInterface marshalling unit tests."""

from collections import namedtuple
from inspect import getmembers, isfunction, ismethod
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional
from xml.etree.ElementTree import Element, tostring

import pytest

from xmlInterface import (
    XMLInterface84,
    XMLInterface85,
    XMLInterface87,
    XMLInterface812,
    XMLInterface814,
    XMLInterfaceBase,
    XMLInterfaces,
    _escape_byte,
    partition_warnings,
)

# Pairs of Python values and the corresponding XML representation. Parametrized
# over an XMLInterface
PyXML = namedtuple("PyXML", ("py", "xml", "bijection"))


def mkXML(
    tag: str,
    text: str = "",
    attrs: Optional[Dict[str, str]] = None,
    children: Optional[Iterable[Any]] = None,
) -> Element:
    """Help build XML Elements."""
    if attrs is None:
        attrs = {}
    xml = Element(tag, attrs)
    if text:
        xml.text = text
    if children:
        xml.extend([child.xml for child in children])
    return xml


class ToOfTests:
    # pylint: disable=missing-function-docstring, no-else-return
    """Methods return test cases for _of_py and _to_py as PyXML objects."""

    @staticmethod
    def all_tests() -> List[str]:
        """Return the names of all test cases."""

        def isfunc(f: object) -> bool:
            return ismethod(f) or isfunction(f)

        return [
            n
            for n, _ in getmembers(ToOfTests, isfunc)
            if n not in ("__init__", "all_tests")
        ]

    def __init__(self, xmlInt: XMLInterfaceBase) -> None:
        self.xi = xmlInt

    def unit(self) -> PyXML:
        return PyXML((), mkXML("unit"), True)

    def true(self) -> PyXML:
        return PyXML(True, mkXML("bool", attrs={"val": "true"}), True)

    def false(self) -> PyXML:
        return PyXML(False, mkXML("bool", attrs={"val": "false"}), True)

    def one(self) -> PyXML:
        return PyXML(1, mkXML("int", text="1"), True)

    def abc(self) -> PyXML:
        return PyXML("abc", mkXML("string", text="abc"), True)

    def abc_u(self) -> PyXML:
        return PyXML("abc", self.abc().xml, True)

    def abc_richpp(self) -> Optional[PyXML]:
        if self.xi.version >= (8, 6, 0):
            return PyXML([("abc", None)], mkXML("richpp", text="abc"), False)
        return None

    def list1(self) -> PyXML:
        unit = self.unit()
        return PyXML([unit.py], mkXML("list", children=[unit]), True)

    def list2(self) -> PyXML:
        one = self.one()
        list1 = self.list1()
        return PyXML([one.py, list1.py], mkXML("list", children=[one, list1]), True)

    def pair(self) -> PyXML:
        one = self.one()
        abc = self.abc()
        return PyXML((one.py, abc.py), mkXML("pair", children=[one, abc]), True)

    def some(self) -> PyXML:
        false = self.false()
        return PyXML(
            self.xi.Some(false.py),
            mkXML("option", attrs={"val": "some"}, children=[false]),
            True,
        )

    def none(self) -> PyXML:
        return PyXML(None, mkXML("option", attrs={"val": "none"}), True)

    def inl(self) -> PyXML:
        true = self.true()
        return PyXML(
            self.xi.Inl(true.py),
            mkXML("union", attrs={"val": "in_l"}, children=[true]),
            True,
        )

    def inr(self) -> PyXML:
        none = self.none()
        return PyXML(
            self.xi.Inr(none.py),
            mkXML("union", attrs={"val": "in_r"}, children=[none]),
            True,
        )

    def evar(self) -> PyXML:
        assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
        abc = self.abc()
        return PyXML(self.xi.CoqEvar(abc.py), mkXML("evar", children=[abc]), False)

    def coq_info(self) -> PyXML:
        assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
        abc = self.abc()
        return PyXML(
            self.xi.CoqInfo(abc.py, abc.py, abc.py, abc.py),
            mkXML("coq_info", children=[abc, abc, abc, abc]),
            False,
        )

    def goal(self) -> PyXML:
        abc = self.abc()
        abc_rich = self.abc_richpp()
        if abc_rich is None:
            abc_rich = abc
        abc_list = PyXML([abc_rich.py], mkXML("list", children=[abc_rich]), True)
        if self.xi.version < (8, 14, 0):
            assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
            return PyXML(
                self.xi.CoqGoal(abc.py, abc_list.py, abc_rich.py),
                mkXML("goal", children=[abc, abc_list, abc_rich]),
                False,
            )
        else:
            assert isinstance(self.xi, XMLInterface814)
            return PyXML(
                self.xi.CoqGoal(abc.py, abc_list.py, abc_rich.py, abc.py),
                mkXML("goal", children=[abc, abc_list, abc_rich, abc]),
                False,
            )

    def goals(self) -> PyXML:
        goal = self.goal()
        goal_list = PyXML([goal.py], mkXML("list", children=[goal]), False)
        goal_pair = PyXML(
            (goal_list.py, goal_list.py),
            mkXML("pair", children=[goal_list, goal_list]),
            False,
        )
        goal_pair_list = PyXML(
            [goal_pair.py],
            mkXML("list", children=[goal_pair]),
            False,
        )
        if self.xi.version < (8, 5, 0):
            assert isinstance(self.xi, XMLInterface84)
            return PyXML(
                self.xi.CoqGoals(goal_list.py, goal_pair_list.py),
                mkXML("goals", children=[goal_list, goal_pair_list]),
                False,
            )
        else:
            assert isinstance(self.xi, XMLInterface85)
            return PyXML(
                self.xi.CoqGoals(
                    goal_list.py,
                    goal_pair_list.py,
                    goal_list.py,
                    goal_list.py,
                ),
                mkXML(
                    "goals",
                    children=[goal_list, goal_pair_list, goal_list, goal_list],
                ),
                False,
            )

    def option_value_bool(self) -> PyXML:
        assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
        true = self.true()
        return PyXML(
            self.xi.CoqOptionValue(true.py, "bool"),
            mkXML("option_value", attrs={"val": "boolvalue"}, children=[true]),
            True,
        )

    def option_value_int(self) -> PyXML:
        assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
        one = self.one()
        opt = PyXML(
            self.xi.Some(one.py),
            mkXML("option", attrs={"val": "some"}, children=[one]),
            True,
        )
        return PyXML(
            self.xi.CoqOptionValue(opt.py, "int"),
            mkXML("option_value", attrs={"val": "intvalue"}, children=[opt]),
            True,
        )

    def option_value_string(self) -> PyXML:
        assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
        abc = self.abc()
        return PyXML(
            self.xi.CoqOptionValue(abc.py, "str"),
            mkXML("option_value", attrs={"val": "stringvalue"}, children=[abc]),
            True,
        )

    def option_value_string_opt(self) -> Optional[PyXML]:
        assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
        abc = self.abc()
        opt = PyXML(
            self.xi.Some(abc.py),
            mkXML("option", attrs={"val": "some"}, children=[abc]),
            True,
        )
        if self.xi.version >= (8, 5, 0):
            return PyXML(
                self.xi.CoqOptionValue(opt.py, "str"),
                mkXML("option_value", attrs={"val": "stringoptvalue"}, children=[opt]),
                True,
            )
        return None

    def option_value_int_none(self) -> PyXML:
        assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
        none = self.none()
        return PyXML(
            self.xi.CoqOptionValue(None, "int"),
            mkXML("option_value", attrs={"val": "intvalue"}, children=[none]),
            True,
        )

    def option_value_str_none(self) -> Optional[PyXML]:
        none = self.none()
        if self.xi.version >= (8, 5, 0):
            assert isinstance(self.xi, XMLInterface85)
            return PyXML(
                self.xi.CoqOptionValue(None, "str"),
                mkXML("option_value", attrs={"val": "stringoptvalue"}, children=[none]),
                True,
            )
        return None

    def option_state(self) -> PyXML:
        true = self.true()
        abc = self.abc()
        opt = self.option_value_bool()
        if self.xi.version < (8, 12, 0):
            assert isinstance(self.xi, (XMLInterface84, XMLInterface85))
            return PyXML(
                self.xi.CoqOptionState(true.py, true.py, abc.py, opt.py),
                mkXML("option_state", children=[true, true, abc, opt]),
                False,
            )
        else:
            assert isinstance(self.xi, XMLInterface812)
            return PyXML(
                self.xi.CoqOptionState(true.py, true.py, opt.py),
                mkXML("option_state", children=[true, true, opt]),
                False,
            )

    def status(self) -> PyXML:
        one = self.one()
        abc = self.abc()
        abc_list = PyXML([abc.py], mkXML("list", children=[abc]), True)
        abc_opt = PyXML(
            self.xi.Some(abc.py),
            mkXML("option", attrs={"val": "some"}, children=[abc]),
            True,
        )
        if self.xi.version < (8, 5, 0):
            assert isinstance(self.xi, XMLInterface84)
            return PyXML(
                self.xi.CoqStatus(abc_list.py, abc_opt.py, abc_list.py, one.py, one.py),
                mkXML("status", children=[abc_list, abc_opt, abc_list, one, one]),
                False,
            )
        else:
            assert isinstance(self.xi, XMLInterface85)
            return PyXML(
                self.xi.CoqStatus(abc_list.py, abc_opt.py, abc_list.py, one.py),
                mkXML("status", children=[abc_list, abc_opt, abc_list, one]),
                False,
            )

    def message(self) -> PyXML:
        # TODO: actually parse the level and location
        abc = self.abc()
        level = PyXML((), mkXML("fake_message_level"), False)
        loc = PyXML((), mkXML("fake_loc"), False)
        if self.xi.version < (8, 6, 0):
            return PyXML(abc.py, mkXML("message", children=[level, abc]), False)
        else:
            return PyXML(abc.py, mkXML("message", children=[level, loc, abc]), False)

    def feedback(self) -> PyXML:
        # TODO: parse feedback correctly
        abc = self.abc()
        edit_id = PyXML((), mkXML("fake_edit_id"), False)
        _route: Optional[PyXML]
        if self.xi.version < (8, 6, 0):
            _route = self.one()  # noqa: F841
            content = PyXML(
                (),
                mkXML(
                    "fake_feedback_content",
                    attrs={"val": "errormsg"},
                    children=[abc, abc],
                ),
                False,
            )
            return PyXML(abc.py, mkXML("feedback", children=[content]), False)
        else:
            _route = self.route_id()  # noqa: F841
            content = PyXML(
                (),
                mkXML(
                    "fake_feedback_content",
                    attrs={"val": "message"},
                    children=[abc, abc],
                ),
                False,
            )
            return PyXML(abc.py, mkXML("feedback", children=[edit_id, content]), False)

    def state_id(self) -> Optional[PyXML]:
        one = self.one()
        if self.xi.version >= (8, 5, 0):
            assert isinstance(self.xi, XMLInterface85)
            return PyXML(
                self.xi.CoqStateId(one.py),
                mkXML("state_id", attrs={"val": str(one.py)}),
                True,
            )
        return None

    def route_id(self) -> Optional[PyXML]:
        one = self.one()
        if self.xi.version >= (8, 7, 0):
            assert isinstance(self.xi, XMLInterface87)
            return PyXML(
                self.xi.CoqRouteId(one.py),
                mkXML("route_id", attrs={"val": str(one.py)}),
                True,
            )
        return None


# Test Fixtures #
@pytest.fixture(scope="module", params=XMLInterfaces)
def xmlInt(request: pytest.FixtureRequest) -> XMLInterfaceBase:
    """Return an XMLInterface for each version."""
    min_ver, _max_ver, xi = request.param  # type: ignore[attr-defined]
    return xi(min_ver, "", Path(), None)  # type: ignore


@pytest.fixture(scope="module", params=ToOfTests.all_tests())
def py_xml(xmlInt: XMLInterfaceBase, request: pytest.FixtureRequest) -> Optional[PyXML]:
    """Return PyXML objects from ToOfTests."""
    return getattr(ToOfTests(xmlInt), request.param)()  # type: ignore


# Test Cases #
def test_to_of_py(xmlInt: XMLInterfaceBase, py_xml: Optional[PyXML]) -> None:
    """Test whether _to_py() and _of_py() convert correctly."""
    if py_xml is None:
        pytest.skip("No tests for this version")
    py = py_xml.py
    xml = py_xml.xml

    assert xmlInt._to_py(xml) == py
    if py_xml.bijection:
        assert tostring(xmlInt._of_py(py)) == tostring(xml)


def test_valid_module(xmlInt: XMLInterfaceBase) -> None:
    """Test whether valid_module correctly identifies valid module names."""
    assert xmlInt.valid_module("/a/b/c.v")
    assert xmlInt.valid_module("a/b/c.v")
    assert xmlInt.valid_module("C.v")
    assert xmlInt.valid_module("_c.v")
    assert xmlInt.valid_module("c3.v")
    assert xmlInt.valid_module("ç.v")
    assert not xmlInt.valid_module("")
    assert not xmlInt.valid_module("c.v.v")
    assert not xmlInt.valid_module("1.v")
    assert not xmlInt.valid_module("a b.v")


def test_topfile(xmlInt: XMLInterfaceBase) -> None:
    """Test whether topfile adds the correct argument."""
    if xmlInt.version < (8, 10, 0):
        assert xmlInt.topfile("c.v", []) == ()
    else:
        assert xmlInt.topfile("c.v", []) == ("-topfile", "c.v")
        assert xmlInt.topfile("", []) == ()
        assert xmlInt.topfile("c.v", ["-top", "x"]) == ()


def test_partition_warnings() -> None:
    """Test that partition_warnings separates warnings from error messages."""
    msg = """
Warning: message
continued
[name,category]
Warning: another one [name,category]
Not a warning,
just an error.
Warning: again [name,category]
Final error.
    """.strip()

    warn = """
Warning: message
continued
[name,category]
Warning: another one [name,category]
Warning: again [name,category]
    """.strip()

    err = """
Not a warning,
just an error.
Final error.
    """.strip()

    assert partition_warnings(msg) == (warn, err)


def test_escape_byte() -> None:
    """Test whether _escape_byte replaces the correct byte."""
    assert _escape_byte(b"a", 1, 0) == b"\\x61"
    assert _escape_byte(b"ab", 1, 1) == b"a\\x62"
    assert _escape_byte(b"ab\nc", 2, 0) == b"ab\n\\x63"
    assert _escape_byte(b"ab\ncd", 2, 1) == b"ab\nc\\x64"
