# -*- coding: utf8 -*-
"""
File: test_xmlInterface.py
Author: Wolf Honore

Description: Unit tests for xmlInterface.py.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

from collections import namedtuple
from inspect import getmembers, ismethod, isfunction
from subprocess import check_output
from xml.etree.ElementTree import tostring, Element
import pytest

from xmlInterface import XmlInterface

# Test Values #
# Check current version
VERSION = check_output(('coqtop', '--version')).split()[5].decode()


# Pairs of Python values and the corresponding XML representation. Parametrized
# over an XmlInterface
PyXml = namedtuple('PyXml', ['py', 'xml'])


def mkXml(tag, text='', attrs=None, children=None):
    """Help build XML Elements."""
    if attrs is None:
        attrs = {}
    xml = Element(tag, attrs)
    if text:
        xml.text = text
    if children:
        xml.extend([child.xml for child in children])
    return xml


class ToFromTests(object):
    """Methods return test cases for _from_value and _to_value as PyXml
    objects."""
    @staticmethod
    def all_tests():
        """Return the names of all test cases."""
        def isfunc(f):
            return ismethod(f) or isfunction(f)
        return [n for n, _ in getmembers(ToFromTests, isfunc)
                if n not in ('__init__', 'all_tests')]

    def __init__(self, xmlInt):
        self.xi = xmlInt

    def unit(self):
        return PyXml((), mkXml('unit'))

    def true(self):
        return PyXml(True, mkXml('bool', attrs={'val': 'true'}))

    def false(self):
        return PyXml(False, mkXml('bool', attrs={'val': 'false'}))

    def one(self):
        return PyXml(1, mkXml('int', text='1'))

    def abc(self):
        return PyXml('abc', mkXml('string', text='abc'))

    def abc_u(self):
        return PyXml(u'abc', self.abc().xml)

    def abc_richpp(self):
        if self.xi.versions >= (8, 6, 0):
            return PyXml(self.abc().py, mkXml('richpp', text='abc'))
        return None

    def list1(self):
        unit = self.unit()
        return PyXml([unit.py], mkXml('list', children=[unit]))

    def list2(self):
        one = self.one()
        list1 = self.list1()
        return PyXml([one.py, list1.py], mkXml('list', children=[one, list1]))

    def pair(self):
        one = self.one()
        abc = self.abc()
        return PyXml((one.py, abc.py), mkXml('pair', children=[one, abc]))

    def some(self):
        false = self.false()
        return PyXml(self.xi.Option(false.py),
                     mkXml('option', attrs={'val': 'some'}, children=[false]))

    def none(self):
        return PyXml(None, mkXml('option', attrs={'val': 'none'}))

    def inl(self):
        true = self.true()
        return PyXml(self.xi.Inl(true.py),
                     mkXml('union', attrs={'val': 'in_l'}, children=[true]))

    def inr(self):
        none = self.none()
        return PyXml(self.xi.Inr(none.py),
                     mkXml('union', attrs={'val': 'in_r'}, children=[none]))

    def evar(self):
        abc = self.abc()
        return PyXml(self.xi.Evar(abc.py), mkXml('evar', children=[abc]))

    def coq_info(self):
        abc = self.abc()
        return PyXml(self.xi.CoqInfo(abc.py, abc.py, abc.py, abc.py),
                     mkXml('coq_info', children=[abc, abc, abc, abc]))

    def goal(self):
        abc = self.abc()
        if self.xi.versions < (8, 6, 0):
            abc_rich = abc
        else:
            abc_rich = self.abc_richpp()
        abc_list = PyXml([abc_rich.py], mkXml('list', children=[abc_rich]))
        return PyXml(self.xi.Goal(abc.py, abc_list.py, abc_rich.py),
                     mkXml('goal', children=[abc, abc_list, abc_rich]))

    def goals(self):
        goal = self.goal()
        goal_list = PyXml([goal.py], mkXml('list', children=[goal]))
        goal_pair = PyXml((goal_list.py, goal_list.py),
                          mkXml('pair', children=[goal_list, goal_list]))
        goal_pair_list = PyXml([goal_pair.py],
                               mkXml('list', children=[goal_pair]))
        if self.xi.versions < (8, 5, 0):
            return PyXml(self.xi.Goals(goal_list.py, goal_pair_list.py),
                         mkXml('goals', children=[goal_list, goal_pair_list]))
        else:
            return PyXml(self.xi.Goals(goal_list.py, goal_pair_list.py,
                                       goal_list.py, goal_list.py),
                         mkXml('goals', children=[goal_list, goal_pair_list,
                                                  goal_list, goal_list]))

    def option_value_bool(self):
        true = self.true()
        return PyXml(self.xi.OptionValue(true.py),
                     mkXml('option_value', attrs={'val': 'boolvalue'},
                           children=[true]))

    def option_value_int(self):
        one = self.one()
        opt = PyXml(self.xi.Option(one.py),
                    mkXml('option', attrs={'val': 'some'}, children=[one]))
        return PyXml(self.xi.OptionValue(opt.py),
                     mkXml('option_value', attrs={'val': 'intvalue'},
                           children=[opt]))

    def option_value_string(self):
        abc = self.abc()
        return PyXml(self.xi.OptionValue(abc.py),
                     mkXml('option_value', attrs={'val': 'stringvalue'},
                           children=[abc]))

    def option_value_string_opt(self):
        abc = self.abc()
        opt = PyXml(self.xi.Option(abc.py),
                    mkXml('option', attrs={'val': 'some'}, children=[abc]))
        if self.xi.versions >= (8, 5, 0):
            return PyXml(self.xi.OptionValue(opt.py),
                         mkXml('option_value', attrs={'val': 'stringoptvalue'},
                               children=[opt]))
        return None

    def option_state(self):
        true = self.true()
        abc = self.abc()
        opt = self.option_value_bool()
        return PyXml(self.xi.OptionState(true.py, true.py, abc.py, opt.py),
                     mkXml('option_state', children=[true, true, abc, opt]))

    def status(self):
        one = self.one()
        abc = self.abc()
        abc_list = PyXml([abc.py], mkXml('list', children=[abc]))
        abc_opt = PyXml(self.xi.Option(abc.py),
                        mkXml('option', attrs={'val': 'some'}, children=[abc]))
        if self.xi.versions < (8, 5, 0):
            return PyXml(self.xi.Status(abc_list.py, abc_opt.py, abc_list.py,
                                        one.py, one.py),
                         mkXml('status', children=[abc_list, abc_opt, abc_list,
                                                   one, one]))
        else:
            return PyXml(self.xi.Status(abc_list.py, abc_opt.py, abc_list.py,
                                        one.py),
                         mkXml('status', children=[abc_list, abc_opt, abc_list,
                                                   one]))

    def message(self):
        # TODO: actually parse the level and location
        abc = self.abc()
        level = PyXml((), mkXml('fake_message_level'))
        loc = PyXml((), mkXml('fake_loc'))
        if self.xi.versions < (8, 6, 0):
            return PyXml(abc.py, mkXml('message', children=[level, abc]))
        else:
            return PyXml(abc.py, mkXml('message', children=[level, loc, abc]))

    def feedback(self):
        # TODO: parse feedback correctly
        abc = self.abc()
        edit_id = PyXml((), mkXml('fake_edit_id'))
        if self.xi.versions < (8, 6, 0):
            route = self.one()
            content = PyXml((),
                            mkXml('fake_feedback_content',
                                  attrs={'val': 'errormsg'},
                                  children=[abc, abc]))
            return PyXml(abc.py, mkXml('feedback', children=[content]))
        else:
            route = self.route_id()
            content = PyXml((),
                            mkXml('fake_feedback_content',
                                  attrs={'val': 'message'},
                                  children=[abc, abc]))
            return PyXml(abc.py,
                         mkXml('feedback', children=[edit_id, content]))

    def state_id(self):
        one = self.one()
        if self.xi.versions >= (8, 5, 0):
            return PyXml(self.xi.StateId(one.py),
                         mkXml('state_id', attrs={'val': str(one.py)}))
        return None

    def route_id(self):
        one = self.one()
        if self.xi.versions >= (8, 7, 0):
            return PyXml(self.xi.RouteId(one.py),
                         mkXml('route_id', attrs={'val': str(one.py)}))
        return None


# Test Fixtures #
@pytest.fixture(scope='module')
def xmlInt():
    """Return an XmlInterface for each version."""
    return XmlInterface(VERSION)


@pytest.fixture(scope='module', params=ToFromTests.all_tests())
def py_xml(xmlInt, request):
    """Return PyXml objects from ToFromTests."""
    return getattr(ToFromTests(xmlInt), request.param)()


# Test Cases #
def test_tofrom_value(xmlInt, py_xml):
    """Test whether _to_value() and _from_value() convert correctly."""
    if py_xml is None:
        pytest.skip('No tests for this version')
    py = py_xml.py
    xml = py_xml.xml

    assert xmlInt._to_value(xml) == py
    try:
        # TODO: parse message and feedback back correctly
        if xml.tag in ('message', 'feedback'):
            return
        assert (tostring(xmlInt._from_value(py))
                == tostring(xml).replace(b'richpp', b'string'))
    except KeyError:
        pass
