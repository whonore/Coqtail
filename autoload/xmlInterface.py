# -*- coding: utf8 -*-
"""
File: xmlInterface.py
Author: Wolf Honore

Description: Handles differences in the Coqtop XML interface across versions
and provides a uniform interface.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import re
import sys
import xml.etree.ElementTree as ET
from abc import ABCMeta, abstractmethod
from collections import namedtuple

# For Mypy
# TODO: Replace some of the 'Any's with more specific types. But in order
# to use type aliases while still avoiding requiring mypy/typing as a
# requirement need to define dummy replacements for some of the below
try:
    from typing import (Any, Callable, Dict, Iterable, List, Optional, Text,
                        Tuple, Type, Union)
except ImportError:
    pass

if sys.version_info[0] >= 3:
    # If in python 3 make unicode an alias for str
    unicode = str

str_tys = (str, unicode)


# Coqtop Response Types #
class Ok(object):
    """A response representing success."""

    def __init__(self, val, msg=''):
        # type: (Any, Text) -> None
        """Initialize values."""
        self.val = val
        self.msg = msg


class Err(object):
    """A response representing failure."""

    def __init__(self, msg, loc=(-1, -1)):
        # type: (Text, Tuple[int, int]) -> None
        """Initialize values."""
        self.msg = msg
        self.loc = loc


# The error in case of a user interrupt
STOPPED_ERR = Err('Coq interrupted.')


# The error in case of a timeout
TIMEOUT_ERR = Err('Coq timed out. You can change the timeout with '
                  '<leader>ct and try again.')


# Helpers #
def unexpected(expected, got, error=ValueError):
    # type: (Iterable[Any], Any, Type[Exception]) -> Exception
    """Return an exception with a message showing what was expected."""
    expect = ' or '.join(map(str, expected))
    return error("Expected {}, but got {}".format(expect, str(got)))


class XmlInterfaceBase(object):
    """Provide methods and types common to all XML interface versions."""
    __metaclass__ = ABCMeta

    # Coqtop Types #
    # Empty Type
    Void = namedtuple('Void', [])

    # Option Type
    Option = namedtuple('Option', ['val'])

    # Union type
    Inl = namedtuple('Inl', ['val'])
    Inr = namedtuple('Inr', ['val'])

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Initialize maps for converting between XML and Python values."""
        self.versions = versions

        self.launch_args = ['-ideslave']

        # Valid query commands
        self.queries = ['Search', 'SearchAbout', 'SearchPattern',
                        'SearchRewrite', 'Check', 'Print', 'About',
                        'Locate']

        self._to_value_funcs = {
            'unit': self._to_unit,
            'bool': self._to_bool,
            'int': self._to_int,
            'string': self._to_string,
            'list': self._to_list,
            'pair': self._to_pair,
            'option': self._to_option,
            'union': self._to_union
        }  # type: Dict[Text, Callable[[ET.Element], object]]

        self._from_value_funcs = {
            # Special case for tuple, must distinguish between 'unit' and
            # 'pair' by checking for '()'
            'tuple': lambda v: self._from_pair(v) if v else self._from_unit(v),
            'bool': self._from_bool,
            'int': self._from_int,
            'str': self._from_string, 'unicode': self._from_string,
            'list': self._from_list,
            'Option': self._from_option, 'NoneType': self._from_option,
            'Inl': self._from_union, 'Inr': self._from_union
        }  # type: Dict[Text, Callable[[Any], ET.Element]]

        self._standardize_funcs = {}  # type: Dict[Text, Callable[[Union[Ok, Err]], Union[Ok, Err]]]

    # XML Parsing and Marshalling #
    def _to_unit(self, _xml):
        # type: (ET.Element) -> Tuple[()]
        """XML: <unit />"""
        return ()

    def _from_unit(self, _val):
        # type: (Tuple[()]) -> ET.Element
        """()"""
        return self._build_xml('unit')

    def _to_bool(self, xml):
        # type: (ET.Element) -> bool
        """<bool val="true|false" />"""
        val = xml.get('val')

        if val == 'true':
            return True
        elif val == 'false':
            return False
        else:
            raise unexpected(('true', 'false'), val)

    def _from_bool(self, val):
        # type: (bool) -> ET.Element
        """True|False"""
        return self._build_xml('bool', str(val).lower())

    def _to_int(self, xml):
        # type: (ET.Element) -> int
        """<int>int</int>"""
        if xml.text is not None:
            return int(xml.text)
        else:
            raise unexpected((str_tys), None)

    def _from_int(self, val):
        # type: (int) -> ET.Element
        """[0-9]+"""
        xml = self._build_xml('int')
        xml.text = str(val)
        return xml

    def _to_string(self, xml):
        # type: (ET.Element) -> Text
        """<string>str</string>"""
        # In Python 2 itertext returns Generator[Any, None, None] instead
        # of Generator[str, None, None]
        return ''.join(xml.itertext())  # type: ignore

    def _from_string(self, val):
        # type: (Text) -> ET.Element
        """'_..._'"""
        xml = self._build_xml('string')
        xml.text = val
        return xml

    def _to_list(self, xml):
        # type: (ET.Element) -> List[Any]
        """<list>(val)*</list>"""
        return list(map(self._to_value, xml))

    def _from_list(self, val):
        # type: (List[Any]) -> (ET.Element)
        """[_, ..., _]"""
        return self._build_xml('list', None, val)

    def _to_pair(self, xml):
        # type: (ET.Element) -> Tuple[Any, Any]
        """<pair>val1 val2</pair>"""
        return (self._to_value(xml[0]), self._to_value(xml[1]))

    def _from_pair(self, val):
        # type: (Tuple[Any, Any]) -> ET.Element
        """(_, _)"""
        return self._build_xml('pair', None, [val[0], val[1]])

    def _to_option(self, xml):
        # type: (ET.Element) -> Union[None, Option]
        """<option val="some">val</option> | <option val="none" />"""
        val = xml.get('val')

        if val == 'none':
            return None
        elif val == 'some':
            return self.Option(self._to_value(xml[0]))
        else:
            raise unexpected(('none', 'some'), val)

    def _from_option(self, val):
        # type: (Union[None, Option]) -> ET.Element
        """Option(val=_)|None"""
        if val is not None:
            return self._build_xml('option', 'some', val.val)
        else:
            return self._build_xml('option', 'none')

    def _to_union(self, xml):
        # type: (ET.Element) -> Union[Inl, Inr]
        """<union val="in_l|in_r">val</union>"""
        val = xml.get('val')

        if val == 'in_l':
            return self.Inl(self._to_value(xml[0]))
        elif val == 'in_r':
            return self.Inr(self._to_value(xml[0]))
        else:
            raise unexpected(('in_l', 'in_r'), val)

    def _from_union(self, val):
        # type: (Union[Inl, Inr]) -> ET.Element
        """Inl(val=_)|Inr(val=_)"""
        if isinstance(val, self.Inl):
            return self._build_xml('union', 'in_l', val.val)
        elif isinstance(val, self.Inr):
            return self._build_xml('union', 'in_r', val.val)
        else:
            raise unexpected((self.Inl, self.Inr), val)

    def _to_value(self, xml):
        # type: (ET.Element) -> object
        """Parse an xml value into a corresponding Python type."""
        try:
            return self._to_value_funcs[xml.tag](xml)
        except KeyError:
            raise unexpected(tuple(self._to_value_funcs), xml.tag, KeyError)

    def _from_value(self, val):
        # type: (Any) -> ET.Element
        """Construct an xml element from a corresponding Python type."""
        try:
            return self._from_value_funcs[type(val).__name__](val)
        except KeyError:
            raise unexpected(tuple(self._from_value_funcs), type(val).__name__,
                             KeyError)

    def _build_xml(self, tag, val=None, children=Void()):
        # type: (Text, Optional[Text], Any) -> ET.Element
        """Construct an xml element with a given tag, value, and children."""
        if val is None:
            attribs = {}  # type: Dict[Text, Text]
        else:
            attribs = {'val': val}

        # If children is a list then convert each element separately, if it is
        # a tuple, treat it as a single element
        if isinstance(children, self.Void):
            children = ()
        elif isinstance(children, list):
            children = [self._from_value(child) for child in children]
        else:
            children = (self._from_value(children),)

        xml = ET.Element(tag, attribs)
        xml.extend(children)

        return xml

    def _to_response(self, xml):
        # type: (ET.Element) -> Union[Ok, Err]
        """Parse an xml response into an Ok or Err."""
        assert xml.tag == 'value'

        val = xml.get('val')
        if val == 'good':
            return Ok(self._to_value(xml[0]))
        elif val == 'fail':
            loc_s = int(xml.get('loc_s', -1))
            loc_e = int(xml.get('loc_e', -1))

            msg = ''.join(xml.itertext())

            return Err(msg, (loc_s, loc_e))
        else:
            raise unexpected(('good', 'fail'), val)

    def worth_parsing(self, data):
        # type: (bytes) -> bool
        """Check if data contains a complete value node yet."""
        return b'</value>' in data

    def raw_response(self, data):
        # type: (bytes) -> Optional[Union[Ok, Err]]
        """Try to parse an XML response from Coqtop into an Ok or Err."""
        res = None
        msgs = []  # type: List[Text]

        try:
            xmls = ET.fromstring(b'<coqtoproot>' +
                                 self._unescape(data) +
                                 b'</coqtoproot>')
        except ET.ParseError:
            # If not all data has been read, the XML might not be well-formed
            return None

        # Wait for a 'value' node and store any 'message' nodes
        for xml in xmls:
            if xml.tag == 'value':
                res = self._to_response(xml)
            elif xml.tag in ('message', 'feedback'):
                msgs.append(self._to_value(xml))  # type: ignore
            else:
                raise unexpected(('value', 'message', 'feedback'), xml.tag)

        if res is not None:
            # Use set() because error messages might have been duplicated by
            # 'feedback' and 'value' tags
            msgs.insert(0, res.msg)
            res.msg = '\n\n'.join(set(msg.strip()
                                      for msg in msgs if msg != ''))

        return res

    def standardize(self, cmd, res):
        # type: (Text, Union[Ok, Err]) -> Union[Ok, Err]
        """Put the information in 'res' into a version-independent form."""
        # By default return unchanged
        try:
            return self._standardize_funcs[cmd](res)
        except KeyError:
            return res

    # Coqtop Commands #
    @abstractmethod
    def init(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to initialize Coqtop."""
        pass

    @abstractmethod
    def add(self, cmd, state, encoding='utf-8'):
        # type: (Text, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to advance Coqtop."""
        pass

    @abstractmethod
    def edit_at(self, state, steps, encoding='utf-8'):
        # type: (int, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to move Coqtop to a specific location."""
        pass

    @abstractmethod
    def query(self, cmd, state, encoding='utf-8'):
        # type: (Text, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to pose a query to Coqtop."""
        pass

    @abstractmethod
    def goal(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to check the current goal state."""
        pass

    @abstractmethod
    def status(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to check Coqtop's status."""
        pass

    @abstractmethod
    def mk_cases(self, ty, encoding='utf-8'):
        # type: (Text, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to construct a match statement for ty."""
        pass

    @abstractmethod
    def get_options(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to check the state of Coqtop's options."""
        pass

    @abstractmethod
    def set_options(self, option, val, encoding='utf-8'):
        # type: (Text, bool, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string to set one of Coqtop's options."""
        pass

    # Helpers #
    @staticmethod
    def _unescape(cmd):
        # type: (bytes) -> bytes
        """Replace escaped characters with the unescaped version."""
        charmap = {
            b'&nbsp;': b' ',
            b'&apos;': b'\'',
            b'&#40;': b'(',
            b'&#41;': b')'
        }

        for escape, unescape in charmap.items():
            cmd = cmd.replace(escape, unescape)

        return cmd

    def is_option(self, cmd):
        # type: (Text) -> bool
        """Check if 'cmd' is trying to set/get/check an option."""
        # Starts with Set, Unset, Test
        # N.B. 'cmd' could be split over multiple lines. We just want to know
        # if any start with an option keyword
        return any(re.match('(Uns|S)et|Test', line.strip()) is not None
                   for line in cmd.split('\n'))

    def is_query(self, cmd):
        # type: (Text) -> bool
        """Check if 'cmd' is a query."""
        re_str = '|'.join(self.queries)
        # N.B. see is_option()
        return any(re.match(re_str, line) is not None
                   for line in cmd.split('\n'))

    def parse_option(self, cmd):
        # type: (Text) -> Tuple[Text, Text]
        """Parse what option is being set/get/checked."""
        # Assumes cmd is of the form 'Set|Unset|Test {option_name}'
        allowed = ('Set', 'Unset', 'Test')
        opts = cmd.strip('.').split()
        ty = opts[0]
        opt = ' '.join(opts[1:])

        if ty not in allowed:
            unexpected(allowed, ty)

        return ty, opt


class XmlInterface84(XmlInterfaceBase):
    """The version 8.4.* XML interface."""

    # TODO: give types to namedtuple fields
    # Coqtop Types #
    Goal = namedtuple('Goal', ['id', 'hyp', 'ccl'])
    Goals = namedtuple('Goals', ['fg', 'bg'])
    Evar = namedtuple('Evar', ['info'])

    OptionValue = namedtuple('OptionValue', ['val'])
    OptionState = namedtuple('OptionState', ['sync', 'depr', 'name', 'value'])

    Status = namedtuple('Status',
                        ['path', 'proofname', 'allproofs', 'statenum',
                         'proofnum'])
    CoqInfo = namedtuple('CoqInfo', ['coq_version',
                                     'protocol_version',
                                     'release_data',
                                     'compile_data'])

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Add to conversion maps."""
        super(XmlInterface84, self).__init__(versions)

        self._to_value_funcs.update({
            'goal': self._to_goal,
            'goals': self._to_goals,
            'evar': self._to_evar,
            'option_value': self._to_option_value,
            'option_state': self._to_option_state,
            'status': self._to_status,
            'coq_info': self._to_coq_info,
            'message': self._to_message,
            'feedback': self._to_feedback
        })

        self._from_value_funcs.update({
            'OptionValue': self._from_option_value
        })

        self._standardize_funcs.update({
            'Init': self._standardize_init,
            'Add': self._standardize_add,
            'Query': self._standardize_query,
            'Goal': self._standardize_goal,
            'GetOptions': self._standardize_get_options
        })

    # XML Parsing and Marshalling #
    def _to_goal(self, xml):
        # type: (ET.Element) -> Goal
        """<goal>string (list string) string</goal>"""
        return self.Goal(*map(self._to_value, xml))

    def _to_goals(self, xml):
        # type: (ET.Element) -> Goals
        """<goals>(list goal) (list (list goal * list goal))</goals>"""
        return self.Goals(*map(self._to_value, xml))

    def _to_evar(self, xml):
        # type: (ET.Element) -> Evar
        """<evar>string</evar>"""
        return self.Evar(self._to_value(xml[0]))

    def _to_option_value(self, xml):
        # type: (ET.Element) -> OptionValue
        """<option_value>bool|option int|string</option_value>"""
        return self.OptionValue(self._to_value(xml[0]))

    def _from_option_value(self, val):
        # type: (OptionValue) -> ET.Element
        """OptionValue(val=_)"""
        opt = val.val

        if isinstance(opt, bool):
            opt_ty = 'boolvalue'
        elif isinstance(opt, self.Option) and isinstance(opt.val, int):
            opt_ty = 'intvalue'
        elif isinstance(opt, str_tys):
            opt_ty = 'stringvalue'
        else:
            raise unexpected((bool, self.Option) + str_tys, type(opt))

        return self._build_xml('option_value', opt_ty, opt)

    def _to_option_state(self, xml):
        # type: (ET.Element) -> OptionState
        """<option_state>bool bool string option_value</option_state>"""
        return self.OptionState(*map(self._to_value, xml))

    def _to_status(self, xml):
        # type: (ET.Element) -> Status
        """<status>(list string) (option string) (list string) int int</string>"""
        return self.Status(*map(self._to_value, xml))

    def _to_coq_info(self, xml):
        # type: (ET.Element) -> CoqInfo
        """<coq_info>string string string string</coq_info>"""
        return self.CoqInfo(*map(self._to_value, xml))

    def _to_message(self, xml):
        # type: (ET.Element) -> Text
        """<message>message_level string</message>"""
        return self._to_value(xml[1])  # type: ignore

    def _to_feedback(self, xml):
        # type: (ET.Element) -> Text
        """<feedback object="?" route="int">feedback_content</feedback>
        <feedback_content val="errormsg">loc string</feedback_content>
        """
        content = xml[0]

        if content.get('val') == 'errormsg':
            return self._to_value(content[1])  # type: ignore
        else:
            # TODO: maybe make use of this info?
            return ''

    # TODO: specify arg and ret types for all commands
    # Coqtop Commands #
    def init(self, _encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Fake the 'Init' command."""
        return ('Init', None)

    def _standardize_init(self, _res):
        # type: (Union[Ok, Err]) -> Ok
        """Standardize the info returned by 'Init'."""
        # state_id (0): The current state id
        return Ok(0)

    def add(self, cmd, state, encoding='utf-8'):
        # type: (Text, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'interp' command."""
        # Attrs:
        #   bool - Verbose output
        #   int - The current state id
        # Args:
        #   string - The command to evaluate
        elt = ET.Element('call', {'val': 'interp',
                                  'verbose': 'true',
                                  'id': str(state)})
        elt.text = cmd
        return ('Add', ET.tostring(elt, encoding))

    def _standardize_add(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Add'."""
        # res_msg: Messages produced by 'Add'
        # state_id (0): The new state id
        if isinstance(res, Ok):
            res_msg = res.val  # type: Text
            res.val = {'res_msg': res_msg, 'state_id': 0}
        return res

    def edit_at(self, _state, steps, encoding='utf-8'):
        # type: (int, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'rewind' command."""
        # Attrs:
        #   int - The number of steps to rewind
        elt = ET.Element('call', {'val': 'rewind',
                                  'steps': str(steps)})
        return ('Edit_at', ET.tostring(elt, encoding))

    def query(self, cmd, state, encoding='utf-8'):
        # type: (Text, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'interp' command."""
        # Attrs:
        #   raw - ?
        #   bool - Verbose output
        #   int - The current state id
        # Args:
        #   string - The query to evaluate
        elt = ET.Element('call', {'val': 'interp',
                                  'raw': 'true',
                                  'verbose': 'true',
                                  'id': str(state)})
        elt.text = cmd
        return ('Query', ET.tostring(elt, encoding))

    def _standardize_query(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Query'."""
        # msg: Messages produced by 'Add'
        if isinstance(res, Ok):
            msg = res.val  # type: Text
            res.msg = msg
        return res

    def goal(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'goal' command."""
        # Args:
        #   unit - Empty arg
        return ('Goal',
                ET.tostring(self._build_xml('call', 'goal', ()), encoding))

    def _standardize_goal(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Goal'."""
        # fg: A list of the current goals
        if isinstance(res, Ok):
            opt_goals = res.val  # type: Union[None, XmlInterfaceBase.Option]
            if opt_goals is not None:
                goals = opt_goals.val  # type: XmlInterface84.Goals
                fg = goals.fg  # type: List[XmlInterface84.Goal]
                res.val = fg
        return res

    def status(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'status' command."""
        # Args:
        #   unit - Empty arg
        return ('Status',
                ET.tostring(self._build_xml('call', 'status', ()), encoding))

    def mk_cases(self, ty, encoding='utf-8'):
        # type: (Text, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'MkCases' command."""
        # Args:
        #   str - The inductive type to make cases for
        elt = ET.Element('call', {'val': 'mkcases'})
        elt.text = ty
        return ('MkCases', ET.tostring(elt, encoding))

    def get_options(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'GetOptions' command."""
        # Args:
        #   unit - Empty arg
        return ('GetOptions',
                ET.tostring(self._build_xml('call', 'getoptions', ()),
                            encoding))

    def _standardize_get_options(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'GetOptions'."""
        # opts: A list of all the options, a short description, and the current
        #       value
        if isinstance(res, Ok):
            raw_opts = res.val  # type: List[Tuple[Text, XmlInterface84.OptionState]]
            opts = [(' '.join(name), state.name, state.value.val)
                    for name, state in raw_opts]  # type: List[Tuple[Text, Text, Any]]
            res.val = opts
        return res

    # TODO: allow non-boolean arguments
    def set_options(self, option, val, encoding='utf-8'):
        # type: (Text, bool, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'SetOptions' command."""
        # Args:
        #   list (option_name * option_value) - The options to update and the
        #                                       values to set
        # TODO: Coq source (toplevel/interface.mli) looks like the argument
        # should be a list like in version 8.5 and on, but it only seems to
        # work if it is a single element
        return ('SetOptions',
                ET.tostring(self._build_xml('call', 'setoptions',
                                            (option.split(),
                                             self.OptionValue(val))),
                            encoding))


# The XML interface is different enough between 8.4 and > 8.4 that the
# following interfaces will not inherit from XmlInterface84
class XmlInterface85(XmlInterfaceBase):
    """The version 8.5.* XML interface."""

    # Coqtop Types #
    Goal = namedtuple('Goal', ['id', 'hyp', 'ccl'])
    Goals = namedtuple('Goals', ['fg', 'bg', 'shelved', 'given_up'])
    Evar = namedtuple('Evar', ['info'])

    OptionValue = namedtuple('OptionValue', ['val'])
    OptionState = namedtuple('OptionState', ['sync', 'depr', 'name', 'value'])

    StateId = namedtuple('StateId', ['id'])
    Status = namedtuple('Status',
                        ['path', 'proofname', 'allproofs', 'proofnum'])
    CoqInfo = namedtuple('CoqInfo', ['coq_version',
                                     'protocol_version',
                                     'release_data',
                                     'compile_data'])

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Add to conversion maps."""
        super(XmlInterface85, self).__init__(versions)

        self.launch_args += ['-main-channel', 'stdfds',
                             '-async-proofs', 'on']

        self.queries += ['SearchHead']

        self._to_value_funcs.update({
            'goal': self._to_goal,
            'goals': self._to_goals,
            'evar': self._to_evar,
            'option_value': self._to_option_value,
            'option_state': self._to_option_state,
            'state_id': self._to_state_id,
            'status': self._to_status,
            'coq_info': self._to_coq_info,
            'message': self._to_message,
            'feedback': self._to_feedback
        })

        self._from_value_funcs.update({
            'OptionValue': self._from_option_value,
            'StateId': self._from_state_id
        })

        self._standardize_funcs.update({
            'Init': self._standardize_init,
            'Add': self._standardize_add,
            'Edit_at': self._standardize_edit_at,
            'Goal': self._standardize_goal,
            'GetOptions': self._standardize_get_options
        })

    # XML Parsing and Marshalling #
    def _to_goal(self, xml):
        # type: (ET.Element) -> Goal
        """<goal>string (list Pp) Pp</goal>"""
        return self.Goal(*map(self._to_value, xml))

    def _to_goals(self, xml):
        # type: (ET.Element) -> Goals
        """<goals>(list goal) (list (list goal * list goal)) (list goal) (list goal)</goals>"""
        return self.Goals(*map(self._to_value, xml))

    def _to_evar(self, xml):
        # type: (ET.Element) -> Evar
        """<evar>string</evar>"""
        return self.Evar(self._to_value(xml[0]))

    def _to_option_value(self, xml):
        # type: (ET.Element) -> OptionValue
        """<option_value>bool|option int|string|option string</option_value>"""
        return self.OptionValue(self._to_value(xml[0]))

    def _from_option_value(self, val):
        # type: (OptionValue) -> ET.Element
        """OptionValue(val=_)"""
        opt = val.val

        if isinstance(opt, bool):
            opt_ty = 'boolvalue'
        elif isinstance(opt, self.Option) and isinstance(opt.val, int):
            opt_ty = 'intvalue'
        elif isinstance(opt, str_tys):
            opt_ty = 'stringvalue'
        elif isinstance(opt, self.Option) and isinstance(opt.val, str_tys):
            opt_ty = 'stringoptvalue'
        else:
            raise unexpected((bool, self.Option) + str_tys, type(opt))

        return self._build_xml('option_value', opt_ty, opt)

    def _to_option_state(self, xml):
        # type: (ET.Element) -> OptionState
        """<option_state>bool bool string option_value</option_state>"""
        return self.OptionState(*map(self._to_value, xml))

    def _to_state_id(self, xml):
        # type: (ET.Element) -> StateId
        """<state_id val="int" />"""
        return self.StateId(int(xml.get('val')))

    def _from_state_id(self, val):
        # type: (StateId) -> ET.Element
        """StateId(id=_)"""
        return self._build_xml('state_id', str(val.id))

    def _to_status(self, xml):
        # type: (ET.Element) -> Status
        """<status>(list string) (option string) (list string) int</string>"""
        return self.Status(*map(self._to_value, xml))

    def _to_coq_info(self, xml):
        # type: (ET.Element) -> CoqInfo
        """<coq_info>string string string string</coq_info>"""
        return self.CoqInfo(*map(self._to_value, xml))

    def _to_message(self, xml):
        # type: (ET.Element) -> Text
        """<message>message_level string</message>"""
        return self._to_value(xml[1])  # type: ignore

    def _to_feedback(self, xml):
        # type: (ET.Element) -> Text
        """<feedback object="?" route="int">feedback_content</feedback>
        <feedback_content val="errormsg">loc string</feedback_content>
        """
        content = xml[0]

        if content.get('val') == 'errormsg':
            return self._to_value(content[1])  # type: ignore
        else:
            # TODO: maybe make use of this info?
            return ''

    # Coqtop Commands #
    def init(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'Init' command."""
        # Args:
        #   option string - A Coq file to add to the LoadPath to do ?
        return ('Init',
                ET.tostring(self._build_xml('call', 'Init', None), encoding))

    def _standardize_init(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Init'."""
        # state_id: The current state id
        if isinstance(res, Ok):
            val = res.val  # type: XmlInterface85.StateId
            res.val = val.id
        return res

    def add(self, cmd, state, encoding='utf-8'):
        # type: (Text, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'Add' command."""
        # Args:
        #   string - The command to evaluate
        #   int - The editId ?
        #   state_id - The current state_id
        #   bool - Verbose output
        return ('Add',
                ET.tostring(self._build_xml('call', 'Add',
                                            ((cmd, -1),
                                             (self.StateId(state), True))),
                            encoding))

    def _standardize_add(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Add'."""
        # res_msg: Messages produced by 'Add'
        # state_id: The new state id
        if isinstance(res, Ok):
            val = res.val  # type: Tuple[XmlInterface85.StateId, Tuple[Any, Text]]
            res.val = {'res_msg': val[1][1], 'state_id': val[0].id}
        return res

    def edit_at(self, state, _steps, encoding='utf-8'):
        # type: (int, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'Edit_at' command."""
        # Args:
        #   state_id - The state_id to move to
        return ('Edit_at',
                ET.tostring(self._build_xml('call', 'Edit_at',
                                            self.StateId(state)),
                            encoding))

    def _standardize_edit_at(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Edit_at'."""
        # extra_steps (0): The additional steps rewound
        if isinstance(res, Ok):
            res.val = 0
        return res

    def query(self, cmd, state, encoding='utf-8'):
        # type: (Text, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'Query' command."""
        # Args:
        #   string - The command to query
        #   state_id - The current state_id
        return ('Query',
                ET.tostring(self._build_xml('call', 'Query',
                                            (cmd, self.StateId(state))),
                            encoding))

    def goal(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'Goal' command."""
        # Args:
        #   unit - Empty arg
        return ('Goal',
                ET.tostring(self._build_xml('call', 'Goal', ()),
                            encoding))

    def _standardize_goal(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Goal'."""
        # fg: A list of the current goals
        if isinstance(res, Ok):
            opt_goals = res.val  # type: Union[None, XmlInterfaceBase.Option]
            if opt_goals is not None:
                goals = opt_goals.val  # type: XmlInterface85.Goals
                fg = goals.fg  # type: List[XmlInterface85.Goal]
                res.val = fg
        return res

    def status(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'Status' command."""
        # Args:
        #   bool - Force all pending evaluations
        return ('Status',
                ET.tostring(self._build_xml('call', 'Status', True), encoding))

    def mk_cases(self, ty, encoding='utf-8'):
        # type: (Text, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'MkCases' command."""
        # Args:
        #   str - The inductive type to make cases for
        return ('MkCases',
                ET.tostring(self._build_xml('call', 'MkCases', ty), encoding))

    def get_options(self, encoding='utf-8'):
        # type: (str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'GetOptions' command."""
        # Args:
        #   unit - Empty arg
        return ('GetOptions',
                ET.tostring(self._build_xml('call', 'GetOptions', ()),
                            encoding))

    def _standardize_get_options(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'GetOptions'."""
        # opts: A list of all the options, a short description, and the current
        #       value
        if isinstance(res, Ok):
            raw_opts = res.val  # type: List[Tuple[Text, XmlInterface85.OptionState]]
            opts = [(' '.join(name), state.name, state.value.val)
                    for name, state in raw_opts]  # type: List[Tuple[Text, Text, Any]]
            res.val = opts
        return res

    # TODO: allow non-boolean arguments
    def set_options(self, option, val, encoding='utf-8'):
        # type: (Text, bool, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'SetOptions' command."""
        # Args:
        #   list (option_name * option_value) - The options to update and the
        #                                       values to set
        # extra '[]' needed so _build_xml treats it as one list instead
        # of several children to convert
        return ('SetOptions',
                ET.tostring(self._build_xml('call', 'SetOptions',
                                            [[(option.split(),
                                               self.OptionValue(val))]]),
                            encoding))


class XmlInterface86(XmlInterface85):
    """The version 8.6.* XML interface."""

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Add to conversion maps."""
        super(XmlInterface86, self).__init__(versions)

        self._to_value_funcs.update({
            'richpp': self._to_string
        })

    # XML Parsing and Marshalling #
    # Overrides _to_message() from 8.5
    def _to_message(self, xml):
        # type: (ET.Element) -> Text
        """<message>message_level (option ?) richpp</message>"""
        # TODO: see if option or message_level are useful
        return self._to_value(xml[2])  # type: ignore

    # Overrides _to_feedback() from 8.5
    def _to_feedback(self, xml):
        # type: (ET.Element) -> Text
        """<feedback object="?" route="int">state_id feedback_content</feedback>
        <feedback_content val="message">message</feedback_content>
        """
        content = xml[1]

        if content.get('val') == 'message':
            return self._to_value(content[0])  # type: ignore
        else:
            # TODO: maybe make use of this info?
            return ''


class XmlInterface87(XmlInterface86):
    """The version 8.7.* XML interface."""

    RouteId = namedtuple('RouteId', ['id'])

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Add to conversion maps."""
        super(XmlInterface87, self).__init__(versions)

        self._to_value_funcs.update({
            'route_id': self._to_route_id
        })

        self._from_value_funcs.update({
            'RouteId': self._from_route_id
        })

    # XML Parsing and Marshalling #
    def _to_route_id(self, xml):
        # type: (ET.Element) -> RouteId
        """<route_id val="int" />"""
        return self.RouteId(int(xml.get('val')))

    def _from_route_id(self, val):
        # type: (RouteId) -> ET.Element
        """StateId(id=_)"""
        return self._build_xml('route_id', str(val.id))

    # Coqtop Commands #
    # Overrides query() from 8.6
    def query(self, cmd, state, encoding='utf-8'):
        # type: (Text, int, str) -> Tuple[Text, Optional[Text]]
        """Create an XML string for the 'Query' command."""
        # Args:
        #   route_id - The routeId ?
        #   string - The command to query
        #   state_id - The current state_id
        return ('Query',
                ET.tostring(self._build_xml('call', 'Query',
                                            (self.RouteId(0),
                                             (cmd, self.StateId(state)))),
                            encoding))


class XmlInterface88(XmlInterface87):
    """The version 8.8.* XML interface."""

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Add to conversion maps."""
        super(XmlInterface88, self).__init__(versions)


def XmlInterface(version):
    # type: (Text) -> XmlInterfaceBase
    """Return the appropriate XmlInterface class for the given version."""
    str_versions = version.replace('pl', '.').split('.')

    # Strip any trailing text (e.g. '+beta1')
    versions = ()  # type: Tuple[int, ...]
    for ver in (re.match('[0-9]+', v) for v in str_versions):
        if ver is None:
            raise ValueError("Invalid version: {}".format(version))
        versions += (int(ver.group(0)),)

    # Pad to at least 3 digits
    versions += (0,) * (3 - len(versions))

    if (8, 4, 0) <= versions < (8, 5, 0):
        return XmlInterface84(versions)
    elif (8, 5, 0) <= versions < (8, 6, 0):
        return XmlInterface85(versions)
    elif (8, 6, 0) <= versions < (8, 7, 0):
        return XmlInterface86(versions)
    elif (8, 7, 0) <= versions < (8, 8, 0):
        return XmlInterface87(versions)
    elif (8, 8, 0) <= versions < (8, 9, 0):
        return XmlInterface88(versions)
    else:
        raise ValueError("Unsupported version: {}".format(version))
