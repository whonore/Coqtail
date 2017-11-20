# -*- coding: utf8 -*-
"""
File: test_xmlInterface.py
Author: Wolf Honore

Description: Unit tests for xmlInterface.py.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

from xml.etree.ElementTree import fromstring, tostring
import pytest

from xmlInterface import XmlInterface

# Test Values #
VERSIONS = ('8.4.0', '8.5.0', '8.6.0', '8.7.0')
TO_FROM_CASE = ('unit', 'true', 'false', 'int', 'str', 'list', 'pair', 'some',
                'none', 'inl', 'inr', 'goal', 'goals', 'evar', 'option_value',
                'option_state', 'status', 'coq_info', 'message', 'feedback',
                'state_id', 'route_id')


# Test Fixtures #
@pytest.fixture(scope='module', params=VERSIONS)
def xmlInt(request):
    """Return an XmlInterface for each version."""
    return XmlInterface(request.param)


@pytest.fixture(scope='module', params=TO_FROM_CASE)
def py_xml(xmlInt, request):
    """Return a triple of Python type, xml value, and whether to convert to and
    from or only to. The specific test values depend on the version.
    """
    # Same for all versions
    all_case = {
        'unit': ((), b'<unit />', False),
        'true': (True, b'<bool val="true" />', False),
        'false': (False, b'<bool val="false" />', False),
        'int': (1, b'<int>1</int>', False),
        'str': ('abc', b'<string>abc</string>', False),
        'list':
            ([1, [()]],
             b'<list><int>1</int><list><unit /></list></list>',
             False),
        'pair':
            ((1, 'a'),
             b'<pair><int>1</int><string>a</string></pair>',
             False),
        'some':
            (xmlInt.Option(False),
             b'<option val="some"><bool val="false" /></option>',
             False),
        'none': (None, b'<option val="none" />', False),
        'inl':
            (xmlInt.Inl(True),
             b'<union val="in_l"><bool val="true" /></union>',
             False),
        'inr':
            (xmlInt.Inr(None),
             b'<union val="in_r"><option val="none" /></union>',
             False),
        'evar': (xmlInt.Evar('x'), b'<evar><string>x</string></evar>', True),
        'option_value':
            (xmlInt.OptionValue(xmlInt.Option(1)),
             b'<option_value><option val="some">'
             b'<int>1</int></option></option_value>',
             True),
        'option_state':
            (xmlInt.OptionState(True, False, 'a', xmlInt.OptionValue('x')),
             b'<option_state>'
             b'<bool val="true" /><bool val="false" /><string>a</string>'
             b'<option_value><string>x</string></option_value></option_state>',
             True),
        'coq_info':
            (xmlInt.CoqInfo('8.0', '123', 'x', 'y'),
             b'<coq_info><string>8.0</string><string>123</string>'
             b'<string>x</string><string>y</string></coq_info>',
             True),
    }

    # Message, feedback, and Goal changed after 8.5
    if xmlInt.versions <= (8, 5, 0):
        all_case.update({
            'message':
                ('a', b'<message><fake /><string>a</string></message>', True),
            'feedback':
                ('a',
                 b'<feedback object="_" route="1">'
                 b'<feedback_content val="errormsg"><fake />'
                 b'<string>a</string></feedback_content></feedback>',
                 True),
            'goal':
                (xmlInt.Goal('1', ['P: Prop', 'H: P -> Q'], 'Q'),
                 b'<goal><string>1</string><list><string>P: Prop</string>'
                 b'<string>H: P -> Q</string></list><string>Q</string></goal>',
                 True)
        })
    else:
        all_case.update({
            'message':
                ('a',
                 b'<message><fake1 /><fake2 /><richpp>a</richpp></message>',
                 True),
            'feedback':
                ('a',
                 b'<feedback object="_" route="1">'
                 b'<fake1 /><feedback_content val="message">'
                 b'<message><fake1 /><fake2 /><richpp>a</richpp></message>'
                 b'</feedback_content></feedback>',
                 True),
            'goal':
                (xmlInt.Goal('1', ['P: Prop', 'H: P -> Q'], 'Q'),
                 b'<goal><string>1</string><list><richpp>P: Prop</richpp>'
                 b'<richpp>H: P -> Q</richpp></list><richpp>Q</richpp></goal>',
                 True),
        })

    if xmlInt.versions == (8, 4, 0):
        all_case.update({
            'goals':
                (xmlInt.Goals([xmlInt.Goal('1', ['True'], 'True')],
                              [xmlInt.Goal('2', ['False'], 'False')]),
                 b'<goals><list><goal><string>1</string>'
                 b'<list><string>True</string></list>'
                 b'<string>True</string></goal></list>'
                 b'<list><goal><string>2</string>'
                 b'<list><string>False</string></list>'
                 b'<string>False</string></goal>'
                 b'</list></goals>',
                 True),
            'status':
                (xmlInt.Status(['a', 'b'], None, ['c'], 1, 2),
                 b'<status><list><string>a</string><string>b</string></list>'
                 b'<option val="none" /><list><string>c</string></list>'
                 b'<int>1</int><int>2</int></status>',
                 True),
        })
    elif xmlInt.versions >= (8, 5, 0):
        # Goal changed after 8.5
        if xmlInt.versions == (8, 5, 0):
            all_case.update({
                'goals':
                    (xmlInt.Goals([xmlInt.Goal('1', ['P'], 'Q')],
                                  [([xmlInt.Goal('2', ['R'], 'S')],
                                    [xmlInt.Goal('3', ['S'], 'R')])],
                                  [], []),
                     b'<goals><list><goal><string>1</string>'
                     b'<list><string>P</string></list>'
                     b'<string>Q</string></goal></list>'
                     b'<list><pair><list><goal><string>2</string>'
                     b'<list><string>R</string></list>'
                     b'<string>S</string></goal></list>'
                     b'<list><goal><string>3</string>'
                     b'<list><string>S</string></list><string>R</string>'
                     b'</goal></list></pair></list><list /><list /></goals>',
                     True)
            })
        else:
            all_case.update({
                'goals':
                    (xmlInt.Goals([xmlInt.Goal('1', ['P'], 'Q')],
                                  [([xmlInt.Goal('2', ['R'], 'S')],
                                    [xmlInt.Goal('3', ['S'], 'R')])],
                                  [], []),
                     b'<goals><list><goal><string>1</string>'
                     b'<list><richpp>P</richpp></list>'
                     b'<richpp>Q</richpp></goal></list>'
                     b'<list><pair><list><goal><string>2</string>'
                     b'<list><richpp>R</richpp></list>'
                     b'<richpp>S</richpp></goal></list>'
                     b'<list><goal><string>3</string>'
                     b'<list><richpp>S</richpp></list><richpp>R</richpp>'
                     b'</goal></list></pair></list><list /><list /></goals>',
                     True)
            })

        all_case.update({
            'status':
                (xmlInt.Status(['a', 'b'], None, ['c'], 1),
                 b'<status><list><string>a</string><string>b</string></list>'
                 b'<option val="none" /><list><string>c</string></list>'
                 b'<int>1</int></status>',
                 True),
            'state_id': (xmlInt.StateId(1), b'<state_id val="1" />', False)
        })

    if xmlInt.versions == (8, 7, 0):
        all_case.update({
            'route_id': (xmlInt.RouteId(1), b'<route_id val="1" />', False)
        })

    # Some versions may not have a test case for a given tag
    return all_case.get(request.param, None)


# Test Cases #
def test_tofrom_value(xmlInt, py_xml):
    """Test whether _to_value() and _from_value() convert correctly."""
    if py_xml is None:
        pytest.skip('No tests for this version')

    py, xml, only_to = py_xml

    assert xmlInt._to_value(fromstring(xml)) == py

    if not only_to:
        assert tostring(xmlInt._from_value(py)) == xml
