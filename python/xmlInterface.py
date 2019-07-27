# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Classes to handle differences in the Coqtop XML interface across versions
and provide a uniform interface.
"""

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

# xml.dom.minidom only needed for pretty printing. No stubs for xml.dom.minidom
import re
import xml.etree.ElementTree as ET
from abc import ABCMeta, abstractmethod
from collections import namedtuple
from xml.dom.minidom import parseString  # type: ignore

from six import add_metaclass, string_types

# For Mypy
# TODO: Replace some of the 'Any's with more specific types. But in order
# to use type aliases while still avoiding requiring mypy/typing as a
# requirement need to define dummy replacements for some of the below
try:
    from typing import Any, Callable, Dict, Iterable, List, Optional, Text, Tuple, Union
except ImportError:
    pass


# Coqtop Response Types #
class Ok(object):
    """A response representing success."""

    def __init__(self, val, msg=""):
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
STOPPED_ERR = Err("Coq interrupted.")


# The error in case of a timeout
TIMEOUT_ERR = Err(
    "Coq timed out. You can change the timeout with <leader>ct and try again."
)


# Helpers #
def unexpected(expected, got):
    # type: (Iterable[Any], Any) -> TypeError
    """Return an exception with a message showing what was expected."""
    expect = " or ".join(map(str, expected))
    return TypeError("Expected {}, but got {}".format(expect, str(got)))


def _unescape(cmd):
    # type: (bytes) -> bytes
    """Replace escaped characters with the unescaped version."""
    charmap = {b"&nbsp;": b" ", b"&apos;": b"'", b"&#40;": b"(", b"&#41;": b")"}

    for escape, unescape in charmap.items():
        cmd = cmd.replace(escape, unescape)

    return cmd


# Debugging #
def prettyxml(xml):
    # type: (bytes) -> Text
    """Pretty print XML for debugging."""
    xml = _unescape(xml)
    # No stubs for xml.dom.minidom
    return parseString(xml).toprettyxml()  # type: ignore


# Mypy doesn't know the type of add_metaclass since it comes from the local six.py
@add_metaclass(ABCMeta)  # type: ignore
class XMLInterfaceBase(object):
    """Provide methods and types common to all XML interface versions."""

    # Coqtop Types #
    # Empty Type
    Void = namedtuple("Void", [])()

    # Option Type
    Option = namedtuple("Option", ["val"])

    # Union type
    Inl = namedtuple("Inl", ["val"])
    Inr = namedtuple("Inr", ["val"])

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Initialize maps for converting between XML and Python values."""
        self.versions = versions

        # Coqtop launch arguments
        self.coqtop = "coqtop"
        self.launch_args = ["-ideslave"]

        # Valid query commands
        self.queries = [
            "Search",
            "SearchAbout",
            "SearchPattern",
            "SearchRewrite",
            "Check",
            "Print",
            "About",
            "Locate",
            "Show",
        ]

        # Map from Python types to appropriate XML marshalling function
        self._to_py_funcs = {
            "unit": self._to_unit,
            "bool": self._to_bool,
            "int": self._to_int,
            "string": self._to_string,
            "list": self._to_list,
            "pair": self._to_pair,
            "option": self._to_option,
            "union": self._to_union,
        }  # type: Dict[Text, Callable[[ET.Element], object]]

        # Inverse map
        self._of_py_funcs = {
            # Special case for tuple, must distinguish between 'unit' and
            # 'pair' by checking for '()'
            "tuple": lambda v: self._of_pair(v) if v else self._of_unit(v),
            "bool": self._of_bool,
            "int": self._of_int,
            "str": self._of_string,
            "unicode": self._of_string,
            "list": self._of_list,
            "Option": self._of_option,
            "NoneType": self._of_option,
            "Inl": self._of_union,
            "Inr": self._of_union,
        }  # type: Dict[Text, Callable[[Any], ET.Element]]

        # Map from coqtop command to standardization function
        self._standardize_funcs = (
            {}
        )  # type: Dict[Text, Callable[[Union[Ok, Err]], Union[Ok, Err]]]

        # A command that can safely and quickly be executed just to get a new state id
        self.noop = "Eval lazy in forall x, x."

    @property
    def launch(self):
        # type: () -> Tuple[Text, ...]
        """The command to launch coqtop with the appropriate arguments."""
        return (self.coqtop,) + tuple(self.launch_args)

    # XML Parsing and Marshalling #
    def _to_unit(self, _xml):
        # type: (ET.Element) -> Tuple[()]
        """Expect: <unit />"""
        return ()

    def _of_unit(self, _val):
        # type: (Tuple[()]) -> ET.Element
        """Expect: ()"""
        return self._build_xml("unit")

    def _to_bool(self, xml):
        # type: (ET.Element) -> bool
        """Expect: <bool val="true | false" />"""
        val = xml.get("val")

        if val == "true":
            return True
        elif val == "false":
            return False
        raise unexpected(("true", "false"), val)

    def _of_bool(self, val):
        # type: (bool) -> ET.Element
        """Expect: True | False"""
        return self._build_xml("bool", str(val).lower())

    def _to_int(self, xml):
        # type: (ET.Element) -> int
        """Expect: <int>int</int>"""
        if xml.text is not None:
            return int(xml.text)
        raise unexpected(string_types, None)

    def _of_int(self, val):
        # type: (int) -> ET.Element
        """Expect: int"""
        return self._build_xml("int", text=str(val))

    def _to_string(self, xml):
        # type: (ET.Element) -> Text
        """Expect: <string>str</string>"""
        # In Python 2 itertext returns Generator[Any, None, None] instead
        # of Generator[str, None, None]
        return "".join(xml.itertext())  # type: ignore

    def _of_string(self, val):
        # type: (Text) -> ET.Element
        """Expect: str"""
        return self._build_xml("string", text=val)

    def _to_list(self, xml):
        # type: (ET.Element) -> List[Any]
        """Expect: <list>val val ...</list>"""
        return [self._to_py(val) for val in xml]

    def _of_list(self, val):
        # type: (List[Any]) -> (ET.Element)
        """Expect: [val, val, ...]"""
        return self._build_xml("list", children=val)

    def _to_pair(self, xml):
        # type: (ET.Element) -> Tuple[Any, Any]
        """Expect: <pair>val1 val2</pair>"""
        return (self._to_py(xml[0]), self._to_py(xml[1]))

    def _of_pair(self, val):
        # type: (Tuple[Any, Any]) -> ET.Element
        """Expect: (val1, val2)"""
        return self._build_xml("pair", children=[val[0], val[1]])

    def _to_option(self, xml):
        # type: (ET.Element) -> Union[None, Option]
        """Expect: <option val="some">val</option> | <option val="none" />"""
        val = xml.get("val")

        if val == "none":
            return None
        elif val == "some":
            return self.Option(self._to_py(xml[0]))
        raise unexpected(("none", "some"), val)

    def _of_option(self, val):
        # type: (Union[None, Option]) -> ET.Element
        """Expect: Option(val) | None"""
        if val is not None:
            return self._build_xml("option", "some", val.val)
        else:
            return self._build_xml("option", "none")

    def _to_union(self, xml):
        # type: (ET.Element) -> Union[Inl, Inr]
        """Expect: <union val="in_l | in_r">val</union>"""
        val = xml.get("val")

        if val == "in_l":
            return self.Inl(self._to_py(xml[0]))
        elif val == "in_r":
            return self.Inr(self._to_py(xml[0]))
        raise unexpected(("in_l", "in_r"), val)

    def _of_union(self, val):
        # type: (Union[Inl, Inr]) -> ET.Element
        """Expect: Inl(val) | Inr(val)"""
        if isinstance(val, self.Inl):
            return self._build_xml("union", "in_l", val.val)
        elif isinstance(val, self.Inr):
            return self._build_xml("union", "in_r", val.val)
        raise unexpected((self.Inl, self.Inr), val)

    def _to_py(self, xml):
        # type: (ET.Element) -> object
        """Parse an XML value into a corresponding Python type."""
        try:
            return self._to_py_funcs[xml.tag](xml)
        except KeyError:
            raise unexpected(tuple(self._to_py_funcs), xml.tag)

    def _of_py(self, val):
        # type: (Any) -> ET.Element
        """Construct an XML element from a corresponding Python type."""
        try:
            return self._of_py_funcs[type(val).__name__](val)
        except KeyError:
            raise unexpected(tuple(self._of_py_funcs), type(val).__name__)

    def _build_xml(
        self,
        tag,  # type: Text
        val=None,  # type: Optional[Text]
        children=Void,  # type: Any
        text=None,  # type: Optional[Text]
        attrs=None,  # type: Optional[Dict[Text, Text]]
    ):
        # type: (...) -> ET.Element
        """Construct an XML element with a given tag, value, and children."""
        if attrs is None:
            attrs = {}
        if val is not None:
            attrs.update({"val": val})

        # If children is a list then convert each element separately, if it is
        # a tuple, treat it as a single element
        if children is self.Void:
            children = ()
        elif isinstance(children, list):
            children = [self._of_py(child) for child in children]
        else:
            children = (self._of_py(children),)

        xml = ET.Element(tag, attrs)
        xml.extend(children)
        xml.text = text

        return xml

    def _make_call(
        self,
        encoding,  # type: str
        cmd,  # type: Text
        children=Void,  # type: Any
        arg=None,  # type: Optional[Text]
        attrs=None,  # type: Optional[Dict[Text, Text]]
    ):
        # type: (...) -> bytes
        """Create a <call> node."""
        elt = self._build_xml("call", val=cmd, children=children, text=arg, attrs=attrs)
        # In Python 3 tostring returns Any instead of bytes
        return ET.tostring(elt, encoding)  # type: ignore

    def _to_response(self, xml):
        # type: (ET.Element) -> Union[Ok, Err]
        """Expect:
        <value val="good">val</value> |
        <value val="fail" (loc_s="int")? (loc_e="int")?>msg</value>
        """
        val = xml.get("val")

        if val == "good":
            return Ok(self._to_py(xml[0]))
        elif val == "fail":
            loc_s = int(xml.get("loc_s", -1))
            loc_e = int(xml.get("loc_e", -1))

            msg = "".join(xml.itertext())

            return Err(msg, (loc_s, loc_e))
        raise unexpected(("good", "fail"), val)

    @staticmethod
    def worth_parsing(data):
        # type: (bytes) -> bool
        """Check if data contains a complete value node yet."""
        return b"</value>" in data

    def raw_response(self, data):
        # type: (bytes) -> Optional[Union[Ok, Err]]
        """Try to parse an XML response from Coqtop into an Ok or Err."""
        res = None
        msgs = []  # type: List[Text]

        try:
            xmls = ET.fromstring(b"<coqtoproot>" + _unescape(data) + b"</coqtoproot>")
        except ET.ParseError:
            # If not all data has been read, the XML might not be well-formed
            return None

        # Wait for a 'value' node and store any 'message' nodes
        for xml in xmls:
            if xml.tag == "value":
                res = self._to_response(xml)
            elif xml.tag in ("message", "feedback"):
                # _to_py guaranteed to return Text for message or feedback
                msgs.append(self._to_py(xml))  # type: ignore
            else:
                raise unexpected(("value", "message", "feedback"), xml.tag)

        if res is not None:
            # Use set() because error messages might have been duplicated by
            # 'feedback' and 'value' tags
            msgs.insert(0, res.msg)
            res.msg = "\n\n".join(set(msg.strip() for msg in msgs if msg.strip() != ""))

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
    def init(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to initialize Coqtop."""

    @abstractmethod
    def add(self, cmd, state, encoding="utf-8"):
        # type: (Text, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to advance Coqtop."""

    @abstractmethod
    def edit_at(self, state, steps, encoding="utf-8"):
        # type: (int, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to move Coqtop to a specific location."""

    @abstractmethod
    def query(self, query, state, encoding="utf-8"):
        # type: (Text, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to pose a query to Coqtop."""

    @abstractmethod
    def goal(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check the current goal state."""

    @abstractmethod
    def status(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check Coqtop's status."""

    @abstractmethod
    def mk_cases(self, ty, encoding="utf-8"):
        # type: (Text, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to construct a match statement for ty."""

    @abstractmethod
    def get_options(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check the state of Coqtop's options."""

    @abstractmethod
    def set_options(self, option, val, encoding="utf-8"):
        # type: (Text, bool, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to set one of Coqtop's options."""

    # Helpers #
    def is_option(self, cmd):
        # type: (Text) -> bool
        """Check if 'cmd' is trying to set/get/check an option."""
        # Starts with Set, Unset, Test
        # N.B. 'cmd' has been stripped of comments and leading whitespace so
        # just check for option commands at the start
        return re.match("((Uns|S)et|Test)$", cmd.split()[0]) is not None

    def is_query(self, cmd):
        # type: (Text) -> bool
        """Check if 'cmd' is a query."""
        re_str = "(" + "|".join(self.queries) + ")$"
        # N.B. see is_option()
        return re.match(re_str, cmd.split()[0].rstrip(".")) is not None

    def parse_option(self, cmd):
        # type: (Text) -> Tuple[Text, Text]
        """Parse what option is being set/get/checked."""
        # Assumes cmd is of the form 'Set|Unset|Test {option_name}'
        allowed = ("Set", "Unset", "Test")
        opts = cmd.strip(".").split()
        ty = opts[0]
        opt = " ".join(opts[1:])

        if ty not in allowed:
            raise unexpected(allowed, ty)

        return ty, opt


class XMLInterface84(XMLInterfaceBase):
    """The version 8.4.* XML interface."""

    # TODO: give types to namedtuple fields
    # Coqtop Types #
    Goal = namedtuple("Goal", ["id", "hyp", "ccl"])
    Goals = namedtuple("Goals", ["fg", "bg"])
    Evar = namedtuple("Evar", ["info"])

    OptionValue = namedtuple("OptionValue", ["val"])
    OptionState = namedtuple("OptionState", ["sync", "depr", "name", "value"])

    Status = namedtuple(
        "Status", ["path", "proofname", "allproofs", "statenum", "proofnum"]
    )
    CoqInfo = namedtuple(
        "CoqInfo", ["coq_version", "protocol_version", "release_data", "compile_data"]
    )

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Update conversion maps with new types."""
        super(XMLInterface84, self).__init__(versions)

        self._to_py_funcs.update(
            {
                "goal": self._to_goal,
                "goals": self._to_goals,
                "evar": self._to_evar,
                "option_value": self._to_option_value,
                "option_state": self._to_option_state,
                "status": self._to_status,
                "coq_info": self._to_coq_info,
                "message": self._to_message,
                "feedback": self._to_feedback,
            }
        )

        self._of_py_funcs.update({"OptionValue": self._of_option_value})

        self._standardize_funcs.update(
            {
                "Init": self._standardize_init,
                "Add": self._standardize_add,
                "Query": self._standardize_query,
                "Goal": self._standardize_goal,
                "GetOptions": self._standardize_get_options,
            }
        )

    # XML Parsing and Marshalling #
    def _to_goal(self, xml):
        # type: (ET.Element) -> Goal
        """Expect: <goal>string (list string) string</goal>"""
        return self.Goal(*map(self._to_py, xml))

    def _to_goals(self, xml):
        # type: (ET.Element) -> Goals
        """Expect: <goals>(list goal) (list (list goal * list goal))</goals>"""
        return self.Goals(*map(self._to_py, xml))

    def _to_evar(self, xml):
        # type: (ET.Element) -> Evar
        """Expect: <evar>string</evar>"""
        return self.Evar(self._to_py(xml[0]))

    def _to_option_value(self, xml):
        # type: (ET.Element) -> OptionValue
        """Expect: <option_value>bool | option int | string</option_value>"""
        return self.OptionValue(self._to_py(xml[0]))

    def _of_option_value(self, val):
        # type: (OptionValue) -> ET.Element
        """Expect: OptionValue(bool) | OptionValue(int | None) | OptionValue(str)"""
        opt = val.val

        if isinstance(opt, bool):
            opt_ty = "boolvalue"
        elif isinstance(opt, self.Option) and isinstance(opt.val, int):
            opt_ty = "intvalue"
        elif isinstance(opt, string_types):
            opt_ty = "stringvalue"
        else:
            raise unexpected((bool, self.Option) + string_types, type(opt))

        return self._build_xml("option_value", opt_ty, opt)

    def _to_option_state(self, xml):
        # type: (ET.Element) -> OptionState
        """Expect: <option_state>bool bool string option_value</option_state>"""
        return self.OptionState(*map(self._to_py, xml))

    def _to_status(self, xml):
        # type: (ET.Element) -> Status
        """Expect:
        <status>(list string) (option string) (list string) int int</status>
        """
        return self.Status(*map(self._to_py, xml))

    def _to_coq_info(self, xml):
        # type: (ET.Element) -> CoqInfo
        """Expect: <coq_info>string string string string</coq_info>"""
        return self.CoqInfo(*map(self._to_py, xml))

    def _to_message(self, xml):
        # type: (ET.Element) -> Text
        """Expect: <message>message_level string</message>"""
        # xml[1] is a string
        return self._to_py(xml[1])  # type: ignore

    def _to_feedback(self, xml):
        # type: (ET.Element) -> Text
        """Expect:
        <feedback object="?" route="int">feedback_content</feedback>
        <feedback_content val="errormsg">loc string</feedback_content>
        """
        content = xml[0]

        if content.get("val") == "errormsg":
            # content[1] is a string
            return self._to_py(content[1])  # type: ignore
        else:
            # TODO: maybe make use of this info?
            return ""

    # Coqtop Commands #
    def init(self, _encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to initialize Coqtop.
        Not a command in 8.4 so return dummy command.
        """
        return ("Init", None)

    def _standardize_init(self, _res):
        # type: (Union[Ok, Err]) -> Ok
        """Standardize the info returned by 'Init'.
        Return:
          state_id: int - The current state id (ignored in 8.4)
        """
        return Ok(0)

    def add(self, cmd, state, encoding="utf-8"):
        # type: (Text, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to advance Coqtop.
        Attrs:
          verbose: bool - Verbose output
          id: int - The current state id
        Args:
          cmd: string - The command to evaluate
        """
        return (
            "Add",
            self._make_call(
                encoding, "interp", attrs={"verbose": "true", "id": str(state)}, arg=cmd
            ),
        )

    def _standardize_add(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Add'.
        Return:
          res_msg: str - Messages produced by 'Add'
          state_id: int - The new state id (ignored in 8.4)
        """
        if isinstance(res, Ok):
            res_msg = res.val  # type: Text
            res.val = {"res_msg": res_msg, "state_id": 0}
        return res

    def edit_at(self, _state, steps, encoding="utf-8"):
        # type: (int, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to move Coqtop to a specific location.
        Attrs:
          steps: int - The number of steps to rewind
        """
        return (
            "Edit_at",
            self._make_call(encoding, "rewind", attrs={"steps": str(steps)}),
        )

    def query(self, query, state, encoding="utf-8"):
        # type: (Text, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to pose a query to Coqtop.
        Attrs:
          raw: bool - ?
          verbose: bool - Verbose output
          id: int - The current state id
        Args:
          query: string - The query to evaluate
        """
        return (
            "Query",
            self._make_call(
                encoding,
                "interp",
                attrs={"raw": "true", "verbose": "true", "id": str(state)},
                arg=query,
            ),
        )

    def _standardize_query(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Query'.
        Return:
          msg: str - Messages produced by 'Query'
        """
        if isinstance(res, Ok):
            msg = res.val  # type: Text
            res.msg = msg
        return res

    def goal(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check the current goal state.
        Args:
          _: unit - Empty arg
        """
        return ("Goal", self._make_call(encoding, "goal", children=()))

    def _standardize_goal(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Goal'.
        Return:
          fg: list Goals - The current goals
          bg: list (list Goals * list Goals) - Unfocused goals
          shelved: list Goals - Shelved goals (dummy value in 8.4)
          given_up: list Goals - Admitted goals (dummy value in 8.4)
        """
        if isinstance(res, Ok):
            opt_goals = res.val  # type: Union[None, XMLInterfaceBase.Option]
            if opt_goals is not None:
                goals = opt_goals.val  # type: XMLInterface84.Goals
                fg = goals.fg  # type: List[XMLInterface84.Goal]
                bg = (
                    goals.bg
                )  # type: List[Tuple[List[XMLInterface84.Goal], List[XMLInterface84.Goal]]]
                res.val = (fg, bg, [], [])
        return res

    def status(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check Coqtop's status.
        Args:
          _: unit - Empty arg
        """
        return ("Status", self._make_call(encoding, "status", children=()))

    def mk_cases(self, ty, encoding="utf-8"):
        # type: (Text, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to construct a match statement for ty.
        Args:
          ty: string - The inductive type to make cases for
        """
        return ("MkCases", self._make_call(encoding, "mkcases", arg=ty))

    def get_options(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check the state of Coqtop's options.
        Args:
          _: unit - Empty arg
        """
        return ("GetOptions", self._make_call(encoding, "getoptions", children=()))

    def _standardize_get_options(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'GetOptions'.
        Return:
          opts: list (string * string * ?) - Triples of all option names,
                                             descriptions, and current values
        """
        if isinstance(res, Ok):
            raw_opts = res.val  # type: List[Tuple[Text, XMLInterface84.OptionState]]
            opts = [
                (" ".join(name), state.name, state.value.val)
                for name, state in raw_opts
            ]  # type: List[Tuple[Text, Text, Any]]
            res.val = opts
        return res

    # TODO: allow non-boolean arguments
    def set_options(self, option, val, encoding="utf-8"):
        # type: (Text, bool, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to set one of Coqtop's options.
        Args:
          options: list (option_name * option_value) - The options to update and
                                                       the values to set them to
        """
        # TODO: Coq source (toplevel/interface.mli) looks like the argument
        # should be a list like in version 8.5 and on, but it only seems to
        # work if it is a single element
        return (
            "SetOptions",
            self._make_call(
                encoding, "setoptions", children=(option.split(), self.OptionValue(val))
            ),
        )


# The XML interface is different enough between 8.4 and > 8.4 that the
# following interfaces will not inherit from XMLInterface84
class XMLInterface85(XMLInterfaceBase):
    """The version 8.5.* XML interface."""

    # Coqtop Types #
    Goal = namedtuple("Goal", ["id", "hyp", "ccl"])
    Goals = namedtuple("Goals", ["fg", "bg", "shelved", "given_up"])
    Evar = namedtuple("Evar", ["info"])

    OptionValue = namedtuple("OptionValue", ["val"])
    OptionState = namedtuple("OptionState", ["sync", "depr", "name", "value"])

    StateId = namedtuple("StateId", ["id"])
    Status = namedtuple("Status", ["path", "proofname", "allproofs", "proofnum"])
    CoqInfo = namedtuple(
        "CoqInfo", ["coq_version", "protocol_version", "release_data", "compile_data"]
    )

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Update conversion maps with new types."""
        super(XMLInterface85, self).__init__(versions)

        self.launch_args += ["-main-channel", "stdfds", "-async-proofs", "on"]
        self.queries += ["SearchHead"]

        self._to_py_funcs.update(
            {
                "goal": self._to_goal,
                "goals": self._to_goals,
                "evar": self._to_evar,
                "option_value": self._to_option_value,
                "option_state": self._to_option_state,
                "state_id": self._to_state_id,
                "status": self._to_status,
                "coq_info": self._to_coq_info,
                "message": self._to_message,
                "feedback": self._to_feedback,
            }
        )

        # Need to declare separately or Mypy infers the type as
        # Dict[Text, Callable[[OptionValue], ET.Element]]
        new_of = {
            "OptionValue": self._of_option_value,
            "StateId": self._of_state_id,
        }  # type: Dict[Text, Callable[[Any], ET.Element]]
        self._of_py_funcs.update(new_of)

        self._standardize_funcs.update(
            {
                "Init": self._standardize_init,
                "Add": self._standardize_add,
                "Edit_at": self._standardize_edit_at,
                "Goal": self._standardize_goal,
                "GetOptions": self._standardize_get_options,
            }
        )

    # XML Parsing and Marshalling #
    def _to_goal(self, xml):
        # type: (ET.Element) -> Goal
        """Expect: <goal>string (list Pp) Pp</goal>"""
        return self.Goal(*map(self._to_py, xml))

    def _to_goals(self, xml):
        # type: (ET.Element) -> Goals
        """Expect:
        <goals>
          (list goal) (list (list goal * list goal))
          (list goal) (list goal)
        </goals>
        """
        return self.Goals(*map(self._to_py, xml))

    def _to_evar(self, xml):
        # type: (ET.Element) -> Evar
        """Expect: <evar>string</evar>"""
        return self.Evar(self._to_py(xml[0]))

    def _to_option_value(self, xml):
        # type: (ET.Element) -> OptionValue
        """Expect:
        <option_value>bool | option int | string | option string</option_value>
        """
        return self.OptionValue(self._to_py(xml[0]))

    def _of_option_value(self, val):
        # type: (OptionValue) -> ET.Element
        """Expect:
        OptionValue(bool) | OptionValue(int | None) | OptionValue(str) |
        OptionValue(str | None)
        """
        opt = val.val

        if isinstance(opt, bool):
            opt_ty = "boolvalue"
        elif isinstance(opt, self.Option) and isinstance(opt.val, int):
            opt_ty = "intvalue"
        elif isinstance(opt, string_types):
            opt_ty = "stringvalue"
        elif isinstance(opt, self.Option) and isinstance(opt.val, string_types):
            opt_ty = "stringoptvalue"
        else:
            raise unexpected((bool, self.Option) + string_types, type(opt))

        return self._build_xml("option_value", opt_ty, opt)

    def _to_option_state(self, xml):
        # type: (ET.Element) -> OptionState
        """Expect: <option_state>bool bool string option_value</option_state>"""
        return self.OptionState(*map(self._to_py, xml))

    def _to_state_id(self, xml):
        # type: (ET.Element) -> StateId
        """Expect: <state_id val="int" />"""
        return self.StateId(int(xml.get("val", 0)))

    def _of_state_id(self, val):
        # type: (StateId) -> ET.Element
        """Expect: StateId(int)"""
        return self._build_xml("state_id", str(val.id))

    def _to_status(self, xml):
        # type: (ET.Element) -> Status
        """Expect:
        <status>(list string) (option string) (list string) int</status>
        """
        return self.Status(*map(self._to_py, xml))

    def _to_coq_info(self, xml):
        # type: (ET.Element) -> CoqInfo
        """Expect: <coq_info>string string string string</coq_info>"""
        return self.CoqInfo(*map(self._to_py, xml))

    def _to_message(self, xml):
        # type: (ET.Element) -> Text
        """Expect: <message>message_level string</message>"""
        # xml[1] is a string
        return self._to_py(xml[1])  # type: ignore

    def _to_feedback(self, xml):
        # type: (ET.Element) -> Text
        """Expect:
        <feedback object="?" route="int">feedback_content</feedback>
        <feedback_content val="errormsg">loc string</feedback_content>
        """
        content = xml[0]

        if content.get("val") == "errormsg":
            # content[1] is a string
            return self._to_py(content[1])  # type: ignore
        else:
            # TODO: maybe make use of this info?
            return ""

    # Coqtop Commands #
    def init(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to initialize Coqtop.
        Args:
          option string - A Coq file to add to the LoadPath to do ?
        """
        return ("Init", self._make_call(encoding, "Init", children=None))

    def _standardize_init(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Init'.
        Return:
          state_id: int - The current state id
        """
        if isinstance(res, Ok):
            val = res.val  # type: XMLInterface85.StateId
            res.val = val.id
        return res

    def add(self, cmd, state, encoding="utf-8"):
        # type: (Text, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to advance Coqtop.
        Args:
          cmd: string - The command to evaluate
          edit_id: int - The current edit id ?
          state_id: StateId - The current state id
          verbose: bool - Verbose output
        """
        return (
            "Add",
            self._make_call(
                encoding, "Add", children=((cmd, -1), (self.StateId(state), True))
            ),
        )

    def _standardize_add(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Add'.
        Return:
          res_msg: str - Messages produced by 'Add'
          state_id: int - The new state id
        """
        if isinstance(res, Ok):
            val = res.val  # type: Tuple[XMLInterface85.StateId, Tuple[Any, Text]]
            res.val = {"res_msg": val[1][1], "state_id": val[0].id}
        return res

    def edit_at(self, state, _steps, encoding="utf-8"):
        # type: (int, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to move Coqtop to a specific location.
        Args:
          state_id: StateId - The state id to move to
        """
        return (
            "Edit_at",
            self._make_call(encoding, "Edit_at", children=self.StateId(state)),
        )

    def _standardize_edit_at(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Edit_at'.
        Return:
          extra_steps: int - The number of additional steps rewound (ignored in >8.4)
        """
        if isinstance(res, Ok):
            res.val = 0
        return res

    def query(self, query, state, encoding="utf-8"):
        # type: (Text, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to pose a query to Coqtop.
        Args:
          query: string - The query to evaluate
          state_id: StateId - The current state id
        """
        return (
            "Query",
            self._make_call(encoding, "Query", children=(query, self.StateId(state))),
        )

    def goal(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check the current goal state.
        Args:
          _: unit - Empty arg
        """
        return ("Goal", self._make_call(encoding, "Goal", children=()))

    def _standardize_goal(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'Goal'.
        Return:
          fg: list Goals - The current goals
          bg: list (list Goals * list Goals) - Unfocused goals
          shelved: list Goals - Shelved goals
          given_up: list Goals - Admitted goals
        """
        if isinstance(res, Ok):
            opt_goals = res.val  # type: Union[None, XMLInterfaceBase.Option]
            if opt_goals is not None:
                goals = opt_goals.val  # type: XMLInterface85.Goals
                fg = goals.fg  # type: List[XMLInterface85.Goal]
                bg = (
                    goals.bg
                )  # type: List[Tuple[List[XMLInterface85.Goal], List[XMLInterface85.Goal]]]
                shelved = goals.shelved  # type: List[XMLInterface85.Goal]
                given_up = goals.given_up  # type: List[XMLInterface85.Goal]
                res.val = (fg, bg, shelved, given_up)
        return res

    def status(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check Coqtop's status.
        Args:
          force: bool - Force all pending evaluations
        """
        return ("Status", self._make_call(encoding, "Status", children=True))

    def mk_cases(self, ty, encoding="utf-8"):
        # type: (Text, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to construct a match statement for ty.
        Args:
          ty: string - The inductive type to make cases for
        """
        return ("MkCases", self._make_call(encoding, "MkCases", children=ty))

    def get_options(self, encoding="utf-8"):
        # type: (str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to check the state of Coqtop's options.
        Args:
          _: unit - Empty arg
        """
        return ("GetOptions", self._make_call(encoding, "GetOptions", children=()))

    def _standardize_get_options(self, res):
        # type: (Union[Ok, Err]) -> Union[Ok, Err]
        """Standardize the info returned by 'GetOptions'.
        Return:
          opts: list (string * string * ?) - Triples of all option names,
                                             descriptions, and current values
        """
        if isinstance(res, Ok):
            raw_opts = res.val  # type: List[Tuple[Text, XMLInterface85.OptionState]]
            opts = [
                (" ".join(name), state.name, state.value.val)
                for name, state in raw_opts
            ]  # type: List[Tuple[Text, Text, Any]]
            res.val = opts
        return res

    # TODO: allow non-boolean arguments
    def set_options(self, option, val, encoding="utf-8"):
        # type: (Text, bool, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to set one of Coqtop's options.
        Args:
          options: list (option_name * option_value) - The options to update and
                                                       the values to set them to
        """
        # extra '[]' needed so _build_xml treats it as one list instead
        # of several children to convert
        return (
            "SetOptions",
            self._make_call(
                encoding,
                "SetOptions",
                children=[[(option.split(), self.OptionValue(val))]],
            ),
        )


class XMLInterface86(XMLInterface85):
    """The version 8.6.* XML interface."""

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Update conversion maps with new types."""
        super(XMLInterface86, self).__init__(versions)

        self.launch_args += [
            "-async-proofs-command-error-resilience",
            "off",
            "-async-proofs-tactic-error-resilience",
            "off",
        ]

        self._to_py_funcs.update({"richpp": self._to_string})

    # XML Parsing and Marshalling #
    # Overrides _to_message() from 8.5
    def _to_message(self, xml):
        # type: (ET.Element) -> Text
        """Expect: <message>message_level (option ?) richpp</message>"""
        # TODO: see if option or message_level are useful
        # xml[2] is a string
        return self._to_py(xml[2])  # type: ignore

    # Overrides _to_feedback() from 8.5
    def _to_feedback(self, xml):
        # type: (ET.Element) -> Text
        """Expect:
        <feedback object="?" route="int">state_id feedback_content</feedback>
        <feedback_content val="message">message</feedback_content>
        """
        content = xml[1]

        if content.get("val") == "message":
            # content[0] is a string
            return self._to_py(content[0])  # type: ignore
        else:
            # TODO: maybe make use of this info?
            return ""


class XMLInterface87(XMLInterface86):
    """The version 8.7.* XML interface."""

    RouteId = namedtuple("RouteId", ["id"])

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Update conversion maps with new types."""
        super(XMLInterface87, self).__init__(versions)

        self._to_py_funcs.update({"route_id": self._to_route_id})

        self._of_py_funcs.update({"RouteId": self._of_route_id})

    # XML Parsing and Marshalling #
    def _to_route_id(self, xml):
        # type: (ET.Element) -> RouteId
        """Expect: <route_id val="int" />"""
        return self.RouteId(int(xml.get("val", 0)))

    def _of_route_id(self, val):
        # type: (RouteId) -> ET.Element
        """Expect: RouteId(int)"""
        return self._build_xml("route_id", str(val.id))

    # Coqtop Commands #
    # Overrides query() from 8.6
    def query(self, query, state, encoding="utf-8"):
        # type: (Text, int, str) -> Tuple[Text, Optional[bytes]]
        """Create an XML string to pose a query to Coqtop.
        Args:
          route_id: RouteId - The route id ?
          query: string - The query to evaluate
          state_id: StateId - The current state id
        """
        return (
            "Query",
            self._make_call(
                encoding, "Query", (self.RouteId(0), (query, self.StateId(state)))
            ),
        )


class XMLInterface88(XMLInterface87):
    """The version 8.8.* XML interface."""


class XMLInterface89(XMLInterface88):
    """The version 8.9.* XML interface."""

    def __init__(self, versions):
        # type: (Tuple[int, ...]) -> None
        """Update launch arguments."""
        super(XMLInterface89, self).__init__(versions)

        # Coq 8.9 split 'coqtop -ideslave' into a separate coqidetop binary
        self.coqtop = "coqidetop"
        self.launch_args.remove("-ideslave")


def XMLInterface(version):
    # type: (Text) -> XMLInterfaceBase
    """Return the appropriate XMLInterface class for the given version."""
    str_versions = version.replace("pl", ".").split(".")

    # Strip any trailing text (e.g. '+beta1')
    versions = ()  # type: Tuple[int, ...]
    for ver in (re.match("[0-9]+", v) for v in str_versions):
        if ver is None:
            raise ValueError("Invalid version: {}".format(version))
        versions += (int(ver.group(0)),)

    # Pad to at least 3 digits
    versions += (0,) * (3 - len(versions))

    if (8, 4, 0) <= versions < (8, 5, 0):
        return XMLInterface84(versions)
    elif (8, 5, 0) <= versions < (8, 6, 0):
        return XMLInterface85(versions)
    elif (8, 6, 0) <= versions < (8, 7, 0):
        return XMLInterface86(versions)
    elif (8, 7, 0) <= versions < (8, 8, 0):
        return XMLInterface87(versions)
    elif (8, 8, 0) <= versions < (8, 9, 0):
        return XMLInterface88(versions)
    elif (8, 9, 0) <= versions < (8, 10, 0):
        return XMLInterface89(versions)
    raise ValueError("Unsupported version: {}".format(version))
