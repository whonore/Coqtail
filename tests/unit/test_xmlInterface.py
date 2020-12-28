# -*- coding: utf8 -*-
# Author: Wolf Honore
"""XMLInterface marshalling unit tests."""

from __future__ import absolute_import, division, print_function

from collections import namedtuple
from inspect import getmembers, isfunction, ismethod
from subprocess import check_output
from xml.etree.ElementTree import Element, tostring

import pytest

from xmlInterface import XMLInterface

# Test Values #
VERSIONS = ("8.{}.0".format(v) for v in range(4, 13))


# Pairs of Python values and the corresponding XML representation. Parametrized
# over an XMLInterface
PyXML = namedtuple("PyXML", ("py", "xml", "bijection"))


def mkXML(tag, text="", attrs=None, children=None):
    """Help build XML Elements."""
    if attrs is None:
        attrs = {}
    xml = Element(tag, attrs)
    if text:
        xml.text = text
    if children:
        xml.extend([child.xml for child in children])
    return xml


class ToOfTests(object):
    """Methods return test cases for _of_py and _to_py as PyXML objects."""

    @staticmethod
    def all_tests():
        """Return the names of all test cases."""

        def isfunc(f):
            return ismethod(f) or isfunction(f)

        return [
            n
            for n, _ in getmembers(ToOfTests, isfunc)
            if n not in ("__init__", "all_tests")
        ]

    def __init__(self, xmlInt):
        self.xi = xmlInt

    def unit(self):
        return PyXML((), mkXML("unit"), True)

    def true(self):
        return PyXML(True, mkXML("bool", attrs={"val": "true"}), True)

    def false(self):
        return PyXML(False, mkXML("bool", attrs={"val": "false"}), True)

    def one(self):
        return PyXML(1, mkXML("int", text="1"), True)

    def abc(self):
        return PyXML("abc", mkXML("string", text="abc"), True)

    def abc_u(self):
        return PyXML(u"abc", self.abc().xml, True)

    def abc_richpp(self):
        if self.xi.versions >= (8, 6, 0):
            return PyXML([("abc", None)], mkXML("richpp", text="abc"), False)
        return None

    def list1(self):
        unit = self.unit()
        return PyXML([unit.py], mkXML("list", children=[unit]), True)

    def list2(self):
        one = self.one()
        list1 = self.list1()
        return PyXML([one.py, list1.py], mkXML("list", children=[one, list1]), True)

    def pair(self):
        one = self.one()
        abc = self.abc()
        return PyXML((one.py, abc.py), mkXML("pair", children=[one, abc]), True)

    def some(self):
        false = self.false()
        return PyXML(
            self.xi.Option(false.py),
            mkXML("option", attrs={"val": "some"}, children=[false]),
            True,
        )

    def none(self):
        return PyXML(None, mkXML("option", attrs={"val": "none"}), True)

    def inl(self):
        true = self.true()
        return PyXML(
            self.xi.Inl(true.py),
            mkXML("union", attrs={"val": "in_l"}, children=[true]),
            True,
        )

    def inr(self):
        none = self.none()
        return PyXML(
            self.xi.Inr(none.py),
            mkXML("union", attrs={"val": "in_r"}, children=[none]),
            True,
        )

    def evar(self):
        abc = self.abc()
        return PyXML(self.xi.Evar(abc.py), mkXML("evar", children=[abc]), False)

    def coq_info(self):
        abc = self.abc()
        return PyXML(
            self.xi.CoqInfo(abc.py, abc.py, abc.py, abc.py),
            mkXML("coq_info", children=[abc, abc, abc, abc]),
            False,
        )

    def goal(self):
        abc = self.abc()
        if self.xi.versions < (8, 6, 0):
            abc_rich = abc
        else:
            abc_rich = self.abc_richpp()
        abc_list = PyXML([abc_rich.py], mkXML("list", children=[abc_rich]), True)
        return PyXML(
            self.xi.Goal(abc.py, abc_list.py, abc_rich.py),
            mkXML("goal", children=[abc, abc_list, abc_rich]),
            False,
        )

    def goals(self):
        goal = self.goal()
        goal_list = PyXML([goal.py], mkXML("list", children=[goal]), False)
        goal_pair = PyXML(
            (goal_list.py, goal_list.py),
            mkXML("pair", children=[goal_list, goal_list]),
            False,
        )
        goal_pair_list = PyXML(
            [goal_pair.py], mkXML("list", children=[goal_pair]), False
        )
        if self.xi.versions < (8, 5, 0):
            return PyXML(
                self.xi.Goals(goal_list.py, goal_pair_list.py),
                mkXML("goals", children=[goal_list, goal_pair_list]),
                False,
            )
        else:
            return PyXML(
                self.xi.Goals(
                    goal_list.py, goal_pair_list.py, goal_list.py, goal_list.py
                ),
                mkXML(
                    "goals", children=[goal_list, goal_pair_list, goal_list, goal_list]
                ),
                False,
            )

    def option_value_bool(self):
        true = self.true()
        return PyXML(
            self.xi.OptionValue(true.py, "bool"),
            mkXML("option_value", attrs={"val": "boolvalue"}, children=[true]),
            True,
        )

    def option_value_int(self):
        one = self.one()
        opt = PyXML(
            self.xi.Option(one.py),
            mkXML("option", attrs={"val": "some"}, children=[one]),
            True,
        )
        return PyXML(
            self.xi.OptionValue(opt.py, "int"),
            mkXML("option_value", attrs={"val": "intvalue"}, children=[opt]),
            True,
        )

    def option_value_string(self):
        abc = self.abc()
        return PyXML(
            self.xi.OptionValue(abc.py, "str"),
            mkXML("option_value", attrs={"val": "stringvalue"}, children=[abc]),
            True,
        )

    def option_value_string_opt(self):
        abc = self.abc()
        opt = PyXML(
            self.xi.Option(abc.py),
            mkXML("option", attrs={"val": "some"}, children=[abc]),
            True,
        )
        if self.xi.versions >= (8, 5, 0):
            return PyXML(
                self.xi.OptionValue(opt.py, "str"),
                mkXML("option_value", attrs={"val": "stringoptvalue"}, children=[opt]),
                True,
            )
        return None

    def option_value_int_none(self):
        none = self.none()
        return PyXML(
            self.xi.OptionValue(None, "int"),
            mkXML("option_value", attrs={"val": "intvalue"}, children=[none]),
            True,
        )

    def option_value_str_none(self):
        none = self.none()
        if self.xi.versions >= (8, 5, 0):
            return PyXML(
                self.xi.OptionValue(None, "str"),
                mkXML("option_value", attrs={"val": "stringoptvalue"}, children=[none]),
                True,
            )

    def option_state(self):
        true = self.true()
        abc = self.abc()
        opt = self.option_value_bool()
        if self.xi.versions < (8, 12, 0):
            return PyXML(
                self.xi.OptionState(true.py, true.py, abc.py, opt.py),
                mkXML("option_state", children=[true, true, abc, opt]),
                False,
            )
        else:
            return PyXML(
                self.xi.OptionState(true.py, true.py, opt.py),
                mkXML("option_state", children=[true, true, opt]),
                False,
            )

    def status(self):
        one = self.one()
        abc = self.abc()
        abc_list = PyXML([abc.py], mkXML("list", children=[abc]), True)
        abc_opt = PyXML(
            self.xi.Option(abc.py),
            mkXML("option", attrs={"val": "some"}, children=[abc]),
            True,
        )
        if self.xi.versions < (8, 5, 0):
            return PyXML(
                self.xi.Status(abc_list.py, abc_opt.py, abc_list.py, one.py, one.py),
                mkXML("status", children=[abc_list, abc_opt, abc_list, one, one]),
                False,
            )
        else:
            return PyXML(
                self.xi.Status(abc_list.py, abc_opt.py, abc_list.py, one.py),
                mkXML("status", children=[abc_list, abc_opt, abc_list, one]),
                False,
            )

    def message(self):
        # TODO: actually parse the level and location
        abc = self.abc()
        level = PyXML((), mkXML("fake_message_level"), False)
        loc = PyXML((), mkXML("fake_loc"), False)
        if self.xi.versions < (8, 6, 0):
            return PyXML(abc.py, mkXML("message", children=[level, abc]), False)
        else:
            return PyXML(abc.py, mkXML("message", children=[level, loc, abc]), False)

    def feedback(self):
        # TODO: parse feedback correctly
        abc = self.abc()
        edit_id = PyXML((), mkXML("fake_edit_id"), False)
        if self.xi.versions < (8, 6, 0):
            route = self.one()  # noqa: F841
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
            route = self.route_id()  # noqa: F841
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

    def state_id(self):
        one = self.one()
        if self.xi.versions >= (8, 5, 0):
            return PyXML(
                self.xi.StateId(one.py),
                mkXML("state_id", attrs={"val": str(one.py)}),
                True,
            )
        return None

    def route_id(self):
        one = self.one()
        if self.xi.versions >= (8, 7, 0):
            return PyXML(
                self.xi.RouteId(one.py),
                mkXML("route_id", attrs={"val": str(one.py)}),
                True,
            )
        return None


# Test Fixtures #
@pytest.fixture(scope="module", params=VERSIONS)
def xmlInt(request):
    """Return an XMLInterface for each version."""
    return XMLInterface(request.param)


@pytest.fixture(scope="module", params=ToOfTests.all_tests())
def py_xml(xmlInt, request):
    """Return PyXML objects from ToOfTests."""
    return getattr(ToOfTests(xmlInt), request.param)()


# Test Cases #
def test_to_of_py(xmlInt, py_xml):
    """Test whether _to_py() and _of_py() convert correctly."""
    if py_xml is None:
        pytest.skip("No tests for this version")
    py = py_xml.py
    xml = py_xml.xml

    assert xmlInt._to_py(xml) == py
    if py_xml.bijection:
        assert tostring(xmlInt._of_py(py)) == tostring(xml)


def test_valid_module(xmlInt):
    """Test whether valid_module correctly identifies valid module names."""
    assert xmlInt.valid_module("/a/b/c.v")
    assert xmlInt.valid_module("a/b/c.v")
    assert xmlInt.valid_module("C.v")
    assert xmlInt.valid_module("_c.v")
    assert xmlInt.valid_module("c3.v")
    assert xmlInt.valid_module(u"ç.v")
    assert not xmlInt.valid_module("")
    assert not xmlInt.valid_module("c.v.v")
    assert not xmlInt.valid_module("1.v")
    assert not xmlInt.valid_module("a b.v")


def test_topfile(xmlInt):
    """Test whether topfile adds the correct argument."""
    if xmlInt.versions < (8, 10, 0):
        assert xmlInt.topfile("c.v", []) == ()
    else:
        assert xmlInt.topfile("c.v", []) == ("-topfile", "c.v")
        assert xmlInt.topfile("", []) == ()
        assert xmlInt.topfile("c.v", ["-top", "x"]) == ()
