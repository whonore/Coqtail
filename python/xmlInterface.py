# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Classes to handle differences in the Rocq XML interface across versions
and provide a uniform interface.

https://github.com/coq/coq/blob/master/dev/doc/xml-protocol.md
"""

# xml.dom.minidom only needed for pretty printing.
import re
import subprocess
import xml.etree.ElementTree as ET
from abc import ABCMeta, abstractmethod
from enum import Enum
from pathlib import Path
from shutil import which
from typing import (
    Any,
    Callable,
    Container,
    Dict,
    Iterable,
    Iterator,
    List,
    NamedTuple,
    Optional,
    Sequence,
    Tuple,
    Union,
    cast,
)
from xml.dom.minidom import parseString
from xml.parsers.expat import ExpatError, errors

PPTag = str
TaggedToken = Tuple[str, Optional[PPTag]]
Goal = NamedTuple(
    "Goal",
    [
        ("hyp", Sequence[Union[str, Sequence[TaggedToken]]]),
        ("ccl", Union[str, Sequence[TaggedToken]]),
        ("name", Optional[str]),
    ],
)
Goals = NamedTuple(
    "Goals",
    [
        ("fg", List[Goal]),
        ("bg", List[List[Goal]]),
        ("shelved", List[Goal]),
        ("given_up", List[Goal]),
    ],
)


class GoalMode(Enum):
    """Control the information returned by the Subgoals command."""

    # Get the goal and hypotheses
    FULL = "full"
    # Get only the goal
    SHORT = "short"


WARNING_RE = re.compile("^(Warning:[^]]+])$", flags=re.MULTILINE)


class FindCoqtopError(Exception):
    """An exception for when a Rocq executable could not be found."""


# Rocq Response Types #
class Ok:
    """A response representing success."""

    def __init__(self, val: Any, msg: str = "") -> None:
        """Initialize values."""
        self.val = val
        self.msg = msg


class Err:
    """A response representing failure."""

    def __init__(self, msg: str, loc: Tuple[int, int] = (-1, -1)) -> None:
        """Initialize values."""
        self.msg = msg
        self.loc = loc


Result = Union[Ok, Err]

# The error in case of a timeout
TIMEOUT_ERR = Err(
    "Rocq timed out. You can change the timeout with <leader>ct and try again."
)

# The error in case of a message on stderr
STDERR_ERR = Err(
    "Coqtail received an unexpected error message on stderr. "
    "Please report at https://github.com/whonore/Coqtail/issues."
    "\n\n"
    "This can sometimes happen if the message is actually a warning, but is not "
    "formatted in a way that Coqtail recognizes. "
    "If you wish to ignore this error and try to proceed past it, set "
    "g:coqtail_treat_stderr_as_warning = 1."
)


# Helpers #
def unexpected(expected: Iterable[Any], got: Any) -> TypeError:
    """Return an exception with a message showing what was expected."""
    expect = " or ".join(map(str, expected))
    return TypeError(f"Expected {expect}, but got {str(got)}")


CHARMAP = {b"&nbsp;": b" ", b"&apos;": b"'", b"&#40;": b"(", b"&#41;": b")"}
BAD_BYTE = errors.codes[errors.XML_ERROR_INVALID_TOKEN]  # pylint: disable=no-member


def _unescape(cmd: bytes) -> bytes:
    """Replace escaped characters with the unescaped version."""
    for escape, unescape in CHARMAP.items():
        cmd = cmd.replace(escape, unescape)
    return cmd


def _escape_byte(data: bytes, line: int, col: int) -> bytes:
    """Escape an unprintable byte."""
    lines = data.splitlines()
    bad = lines[line - 1][col]
    pre = lines[line - 1][:col]
    post = lines[line - 1][col + 1 :]
    lines[line - 1] = pre + f"\\x{bad:02x}".encode("utf-8") + post
    return b"\n".join(lines)


def _parse_tagged_tokens(
    tags: Container[PPTag],
    xml: ET.Element,
    stack: Optional[List[PPTag]] = None,
    inner: bool = False,
) -> Iterator[Tuple[str, List[PPTag]]]:
    """Scrape an XML element into a stream of text tokens and stack of tags.

    Helper function to parse_tagged_tokens.

    Written to support richpp tags, and thus supports .start and .end tags
    used by Rocq to highlight ranges that are not properly nested
    (i.e., <start.a/>...<start.b/>...<end.a/>...<end.b/> is allowed).
    This is somewhat documented here: https://github.com/coq/coq/blob/master/dev/doc/xml-protocol.md#highlighting-text
    Documentation neglects to mention the semantics of start. and end. tags
    that are not self-closing.

    Until we get clarification, we will interpret
    <start.a>foo</start.a>bar as <start.a/>foobar and
    <end.b>foo</end.b>bar as foobar<end.b/>.
    """
    pop_after = None
    if stack is None:
        stack = []

    # Check tag, see if we should modify stack
    if xml.tag.startswith("start."):
        _, _, tag = xml.tag.rpartition("start.")  # assert(tag != "")
        if tag in tags:
            # start. tag: push onto stack
            stack.insert(0, tag)

    elif xml.tag.startswith("end."):
        _, _, tag = xml.tag.rpartition("end.")  # assert(tag != "")
        if tag in tags:
            # end. tag: remove from stack (even if it's not at the top)
            pop_after = tag

    elif xml.tag in tags:
        # regular tag: push onto stack, but remember to pop it before xml.tail
        stack.insert(0, xml.tag)
        pop_after = xml.tag

    # Get text before first inner child
    if xml.text is not None:
        yield (xml.text, stack[:])

    # Recurse on children, with modified stack
    for child in xml:
        yield from _parse_tagged_tokens(tags, child, stack, True)

    if pop_after is not None:
        stack.remove(pop_after)

    # Get trailing text up to start of next tag, unless this is the outermost tag
    if inner and xml.tail is not None:
        yield (xml.tail, stack[:])


def parse_tagged_tokens(
    tags: Container[PPTag],
    xml: ET.Element,
) -> Iterator[TaggedToken]:
    """Scrape an XML element into a stream of text tokens and accompanying tags.

    Written to support richpp markup.
    Only considers tags specified by the tags parameter.
    """
    token_acc, last_tag = "", None

    # Recursive helper _parse_tagged_tokens gives us tag stacks
    for token, tag_list in _parse_tagged_tokens(tags, xml):
        # Take top tag from tag stack, if any
        top_tag = tag_list[0] if tag_list != [] else None

        if top_tag == last_tag:
            # Join tokens whose top tag is the same
            token_acc += token
        else:
            yield (token_acc, last_tag)
            token_acc, last_tag = token, top_tag

    yield (token_acc, last_tag)


def join_tagged_tokens(tagged_tokens: Iterable[TaggedToken]) -> str:
    """Join tokens from tagged token stream.

    NOTE:
      forall xml tags,
        join_tagged_tokens(parse_tagged_token(tags, xml)) = "".join(xml.itertext())
    """
    return "".join(s for s, _ in tagged_tokens)


def partition_warnings(stderr: str) -> Tuple[str, str]:
    """Partition Rocq stderr messages into warnings and errors.

    Warnings are assumed to have the following form:
    Warning: message_with_newlines [warning_type]\n
    Everything else is treated as an error message.
    """
    warns: List[str] = []
    errs: List[str] = []
    # Strip whitespace and drop empty strings
    for msg in filter(None, map(str.strip, WARNING_RE.split(stderr))):
        (warns if WARNING_RE.fullmatch(msg) else errs).append(msg)
    return "\n".join(warns), "\n".join(errs)


# Debugging #
def prettyxml(xml: bytes) -> str:
    """Pretty print XML for debugging."""
    xml = _unescape(xml)
    # See `XMLInterfaceBase.raw_response`.
    err_pos = (-1, -1)
    while True:
        try:
            return parseString(xml).toprettyxml()
        except ExpatError as e:
            if e.code != BAD_BYTE or (e.lineno, e.offset) <= err_pos:
                raise e
            err_pos = (e.lineno, e.offset)
            xml = _escape_byte(xml, *err_pos)


class XMLInterfaceBase(metaclass=ABCMeta):
    """Provide methods and types common to all XML interface versions."""

    # Rocq Types #
    sentinel = object()

    # Option Type
    Some = NamedTuple("Some", [("val", Any)])
    CoqOption = Union[Some, None]

    # Union type
    Inl = NamedTuple("Inl", [("val", Any)])
    Inr = NamedTuple("Inr", [("val", Any)])
    CoqUnion = Union[Inl, Inr]

    # Types accepted by 'Set {option} {val}'
    OptionArg = Union[bool, int, str, Tuple[None, str]]

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Initialize maps for converting between XML and Python values."""
        self.version = version
        self.str_version = str_version

        # Rocq launch arguments
        self.coq_path = coq_path
        assert coq_prog is not None
        self.coq_prog = coq_prog
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
        self._to_py_funcs: Dict[str, Callable[[ET.Element], Any]] = {
            "unit": self._to_unit,
            "bool": self._to_bool,
            "int": self._to_int,
            "string": self._to_string,
            "list": self._to_list,
            "pair": self._to_pair,
            "option": self._to_option,
            "union": self._to_union,
        }

        # Inverse map
        self._of_py_funcs: Dict[str, Callable[[Any], ET.Element]] = {
            # Special case for tuple, must distinguish between 'unit' and
            # 'pair' by checking for '()'
            "tuple": lambda v: self._of_pair(v) if v else self._of_unit(v),
            "bool": self._of_bool,
            "int": self._of_int,
            "str": self._of_string,
            "list": self._of_list,
            "Some": self._of_option,
            "NoneType": self._of_option,
            "Inl": self._of_union,
            "Inr": self._of_union,
        }

        # Map from Rocq command to standardization function
        self._standardize_funcs: Dict[str, Callable[[Result], Result]] = {}

        # A command that can safely and quickly be executed just to get a new state id
        self.noop = "Check Prop."

        # A flag indicating whether warnings printed to stderr are formatted in
        # the manner expected by partition_warnings
        self.warnings_wf = False

    def launch(self, filename: str, args: Iterable[str]) -> Tuple[str, ...]:
        """The command to launch Rocq with the appropriate arguments."""
        # Find the executable
        try:
            coqs = (
                p
                for p in (
                    which(pre + self.coq_prog + ext, path=self.coq_path)
                    for pre in ("", "coq-prover.")
                    for ext in ("", ".opt")
                )
                if p is not None
            )
            coq = next(coqs)
        except StopIteration as e:
            path = "$PATH" if self.coq_path is None else self.coq_path
            raise FindCoqtopError(
                f"Could not find {self.coq_prog} in {path}. Perhaps you need "
                "to set g:coqtail_coq_path or g:coqtail_coq_prog."
            ) from e

        # Confirm the version matches
        version = parse_version(extract_version(coq))
        if version != self.version:
            raise FindCoqtopError(
                f"{coq} version does not match version reported by coqc/rocq.\n"
                f"Expected: {self.version} Got: {version}"
            )

        return (
            (coq,)
            + tuple(self.launch_args)
            + self.topfile(filename, args)
            + tuple(args)
        )

    @staticmethod
    def topfile(filename: str, args: Iterable[str]) -> Tuple[str, ...]:
        """The command to set the top-level module name."""
        # pylint: disable=unused-argument
        # The arguments are only used in XMLInterface810 and greater.
        return ()

    @staticmethod
    def valid_module(filename: str) -> bool:
        """Check if a file name is a valid module name."""
        # Any string of word characters that doesn't start with a digit
        return re.fullmatch(r"(?=\D)\w+", Path(filename).stem) is not None

    # XML Parsing and Marshalling #
    def _to_unit(self, _xml: ET.Element) -> Tuple[()]:
        """Expect: <unit />"""
        return ()

    def _of_unit(self, _val: Tuple[()]) -> ET.Element:
        """Expect: ()"""
        return self._build_xml("unit")

    def _to_bool(self, xml: ET.Element) -> bool:
        """Expect: <bool val="true | false" />"""
        # pylint: disable=no-else-return
        val = xml.get("val")

        if val == "true":
            return True
        elif val == "false":
            return False
        raise unexpected(("true", "false"), val)

    def _of_bool(self, val: bool) -> ET.Element:
        """Expect: True | False"""
        return self._build_xml("bool", str(val).lower())

    def _to_int(self, xml: ET.Element) -> int:
        """Expect: <int>int</int>"""
        if xml.text is not None:
            return int(xml.text)
        raise unexpected((str,), None)

    def _of_int(self, val: int) -> ET.Element:
        """Expect: int"""
        return self._build_xml("int", text=str(val))

    def _to_string(self, xml: ET.Element) -> str:
        """Expect: <string>str</string>"""
        return "".join(xml.itertext())

    def _of_string(self, val: str) -> ET.Element:
        """Expect: str"""
        return self._build_xml("string", text=val)

    def _to_list(self, xml: ET.Element) -> List[Any]:
        """Expect: <list>val val ...</list>"""
        return [self._to_py(val) for val in xml]

    def _of_list(self, val: List[Any]) -> ET.Element:
        """Expect: [val, val, ...]"""
        return self._build_xml("list", children=val)

    def _to_pair(self, xml: ET.Element) -> Tuple[Any, Any]:
        """Expect: <pair>val1 val2</pair>"""
        return (self._to_py(xml[0]), self._to_py(xml[1]))

    def _of_pair(self, val: Tuple[Any, Any]) -> ET.Element:
        """Expect: (val1, val2)"""
        return self._build_xml("pair", children=[val[0], val[1]])

    def _to_option(self, xml: ET.Element) -> "CoqOption":
        """Expect: <option val="some">val</option> | <option val="none" />"""
        # pylint: disable=no-else-return
        val = xml.get("val")

        if val == "none":
            return None
        elif val == "some":
            return self.Some(self._to_py(xml[0]))
        raise unexpected(("none", "some"), val)

    def _of_option(self, val: CoqOption) -> ET.Element:
        """Expect: Some(val) | None"""
        # pylint: disable=no-else-return
        if val is not None:
            return self._build_xml("option", "some", val.val)
        else:
            return self._build_xml("option", "none")

    def _to_union(self, xml: ET.Element) -> "CoqUnion":
        """Expect: <union val="in_l | in_r">val</union>"""
        # pylint: disable=no-else-return
        val = xml.get("val")

        if val == "in_l":
            return self.Inl(self._to_py(xml[0]))
        elif val == "in_r":
            return self.Inr(self._to_py(xml[0]))
        raise unexpected(("in_l", "in_r"), val)

    def _of_union(self, val: CoqUnion) -> ET.Element:
        """Expect: Inl(val) | Inr(val)"""
        # pylint: disable=no-else-return
        if isinstance(val, self.Inl):
            return self._build_xml("union", "in_l", val.val)
        elif isinstance(val, self.Inr):
            return self._build_xml("union", "in_r", val.val)
        raise unexpected((self.Inl, self.Inr), val)

    def _to_py(self, xml: ET.Element) -> Any:
        """Parse an XML value into a corresponding Python type."""
        try:
            return self._to_py_funcs[xml.tag](xml)
        except KeyError as e:
            raise unexpected(tuple(self._to_py_funcs), xml.tag) from e

    def _of_py(self, val: Any) -> ET.Element:
        """Construct an XML element from a corresponding Python type."""
        try:
            return self._of_py_funcs[type(val).__name__](val)
        except KeyError as e:
            raise unexpected(tuple(self._of_py_funcs), type(val).__name__) from e

    def _build_xml(
        self,
        tag: str,
        val: Optional[str] = None,
        children: Any = sentinel,
        text: Optional[str] = None,
        attrs: Optional[Dict[str, str]] = None,
    ) -> ET.Element:
        """Construct an XML element with a given tag, value, and children."""
        if attrs is None:
            attrs = {}
        if val is not None:
            attrs.update({"val": val})

        # If children is a list then convert each element separately, if it is
        # a tuple, treat it as a single element
        if children is self.sentinel:
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
        encoding: str,
        cmd: str,
        children: Any = sentinel,
        arg: Optional[str] = None,
        attrs: Optional[Dict[str, str]] = None,
    ) -> bytes:
        """Create a <call> node."""
        elt = self._build_xml("call", val=cmd, children=children, text=arg, attrs=attrs)
        # In Python 3 tostring returns Any instead of bytes
        return cast(bytes, ET.tostring(elt, encoding))

    def _to_response(self, xml: ET.Element) -> Result:
        """Expect:
        <value val="good">val</value> |
        <value val="fail" (loc_s="int")? (loc_e="int")?>msg</value>
        """
        # pylint: disable=no-else-return
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
    def worth_parsing(data: bytes) -> bool:
        """Check if data contains a complete value node yet."""
        return b"</value>" in data

    def raw_response(self, data: bytes) -> Optional[Result]:
        """Try to parse an XML response from Rocq into an Ok or Err."""
        res = None
        msgs: List[str] = []

        err_pos = (-1, -1)
        data = b"<coqtoproot>" + _unescape(data) + b"</coqtoproot>"
        while True:
            try:
                xmls = ET.fromstring(data)
                break
            except ET.ParseError as e:
                # If not all data has been read, the XML might not be well-formed
                if e.code != BAD_BYTE or e.position <= err_pos:
                    return None
                # Found an invalid byte, try escaping it
                err_pos = e.position
                data = _escape_byte(data, *err_pos)

        # Wait for a 'value' node and store any 'message' nodes
        for xml in xmls:
            if xml.tag == "value":
                res = self._to_response(xml)
            elif xml.tag in {"message", "feedback"}:
                # _to_py is guaranteed to either return str or
                # a sequence of tagged tokens for message or feedback
                msg = self._to_py(xml)
                if isinstance(msg, list):
                    msg = join_tagged_tokens(msg)

                # Sanity check
                if not isinstance(msg, str):
                    raise unexpected((str,), type(msg))

                msgs.append(msg.strip())
            else:
                raise unexpected(("value", "message", "feedback"), xml.tag)

        if res is not None:
            # Error messages may be duplicated between the 'value' and
            # 'feedback' tags.
            # https://coq.discourse.group/t/avoiding-duplicate-error-messages-with-the-xml-protocol/411
            msg = res.msg.strip()
            if msg not in msgs:
                msgs.insert(0, msg)
            res.msg = "\n\n".join(msg for msg in msgs if msg != "")

        return res

    def standardize(self, cmd: str, res: Result) -> Result:
        """Put the information in 'res' into a version-independent form."""
        # By default return unchanged
        try:
            return self._standardize_funcs[cmd](res)
        except KeyError:
            return res

    # Rocq Commands #
    @abstractmethod
    def init(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to initialize Rocq."""

    @abstractmethod
    def add(
        self,
        cmd: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to advance Rocq."""

    @abstractmethod
    def edit_at(
        self,
        state: int,
        steps: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to move Rocq to a specific location."""

    @abstractmethod
    def query(
        self,
        query: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to pose a query to Rocq."""

    @abstractmethod
    def goal(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check the current goal state."""

    @abstractmethod
    def status(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check Rocq's status."""

    @abstractmethod
    def get_options(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check the state of Rocq's options."""

    @abstractmethod
    def set_options(
        self,
        option: str,
        val: OptionArg,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to set one of Rocq's options."""

    # Helpers #
    @staticmethod
    def is_option(cmd: str) -> bool:
        """Check if 'cmd' is trying to set/check an option."""
        # Starts with Set, Unset, Test
        # NOTE: 'cmd' has been stripped of comments and leading whitespace so
        # just check for option commands at the start
        return re.fullmatch("((Uns|S)et|Test)", cmd.split()[0]) is not None

    def is_query(self, cmd: str) -> bool:
        """Check if 'cmd' is a query."""
        re_str = "(" + "|".join(self.queries) + ")"
        # NOTE: see is_option()
        return re.fullmatch(re_str, cmd.split()[0].rstrip(".")) is not None

    @staticmethod
    def parse_option(cmd: str) -> Tuple[Optional[Sequence[OptionArg]], str]:
        """Parse what option is being set/checked."""
        # Assumes cmd is of the form 'Set|Unset|Test {option_name}'
        opts = cmd.strip(".").split()
        ty = opts[0]

        vals: Optional[Sequence[XMLInterfaceBase.OptionArg]]
        if ty == "Test":
            vals = None
        elif ty == "Set":
            val: XMLInterfaceBase.OptionArg
            if opts[-1][0].isdigit():
                val = int(opts[-1])
                opts = opts[:-1]
            elif opts[-1][-1] == '"':
                for idx, opt in enumerate(opts):
                    if opt[0] == '"':
                        val = " ".join(opts[idx:]).strip('"')
                        opts = opts[:idx]
            else:
                val = True
            vals = (val,)
        elif ty == "Unset":
            # Don't know if the option expects a bool, option int, or option
            # str, so try all
            vals = (False, (None, "int"), (None, "str"))
        else:
            raise unexpected(("Set", "Unset", "Test"), ty)

        return vals, " ".join(opts[1:])

    @staticmethod
    def unwrap_coq_option(opt: CoqOption) -> Optional[Any]:
        """Convert CoqOption to Optional."""
        return None if opt is None else opt.val


class XMLInterface84(XMLInterfaceBase):
    """The version 8.4.* XML interface."""

    # Rocq Types #
    CoqGoal = NamedTuple("CoqGoal", [("id", str), ("hyp", List[str]), ("ccl", str)])
    CoqGoals = NamedTuple(
        "CoqGoals",
        [("fg", List[CoqGoal]), ("bg", List[Tuple[List[CoqGoal], List[CoqGoal]]])],
    )
    CoqEvar = NamedTuple("CoqEvar", [("info", str)])

    CoqOptionValue = NamedTuple(
        "CoqOptionValue",
        [
            ("val", Union[bool, XMLInterfaceBase.CoqOption, str]),
            ("type", Optional[str]),
        ],
    )
    CoqOptionState = NamedTuple(
        "CoqOptionState",
        [("sync", bool), ("depr", bool), ("name", str), ("value", CoqOptionValue)],
    )

    CoqStatus = NamedTuple(
        "CoqStatus",
        [
            ("path", List[str]),
            ("proofname", XMLInterfaceBase.CoqOption),
            ("allproofs", List[str]),
            ("statenum", int),
            ("proofnum", int),
        ],
    )
    CoqInfo = NamedTuple(
        "CoqInfo",
        [
            ("coq_version", str),
            ("protocol_version", str),
            ("release_data", str),
            ("compile_data", str),
        ],
    )

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(
            version,
            str_version,
            coq_path,
            "coqtop" if coq_prog is None else coq_prog,
        )

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

        self._of_py_funcs.update({"CoqOptionValue": self._of_option_value})

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
    def _to_goal(self, xml: ET.Element) -> "CoqGoal":
        """Expect: <goal>string (list string) string</goal>"""
        return self.CoqGoal(*map(self._to_py, xml))

    def _to_goals(self, xml: ET.Element) -> "CoqGoals":
        """Expect: <goals>(list goal) (list (list goal * list goal))</goals>"""
        return self.CoqGoals(*map(self._to_py, xml))

    def _to_evar(self, xml: ET.Element) -> "CoqEvar":
        """Expect: <evar>string</evar>"""
        return self.CoqEvar(self._to_py(xml[0]))

    def _to_option_value(self, xml: ET.Element) -> "CoqOptionValue":
        """Expect: <option_value>bool | option int | string</option_value>"""
        ty = xml.get("val", None)
        if ty is not None:
            if ty.startswith("int"):
                ty = "int"
            elif ty.startswith("str"):
                ty = "str"
            else:
                ty = "bool"
        return self.CoqOptionValue(self._to_py(xml[0]), ty)

    def _of_option_value(self, val: CoqOptionValue) -> ET.Element:
        """Expect: CoqOptionValue(bool) | CoqOptionValue(int | None) | CoqOptionValue(str)"""
        opt = val.val

        if isinstance(opt, bool):
            opt_ty = "boolvalue"
        elif (isinstance(opt, self.Some) and isinstance(opt.val, int)) or opt is None:
            opt_ty = "intvalue"
        elif isinstance(opt, str):
            opt_ty = "stringvalue"
        else:
            raise unexpected((bool, self.Some, None, str), type(opt))

        return self._build_xml("option_value", opt_ty, opt)

    def _to_option_state(self, xml: ET.Element) -> "CoqOptionState":
        """Expect: <option_state>bool bool string option_value</option_state>"""
        return self.CoqOptionState(*map(self._to_py, xml))

    def _to_status(self, xml: ET.Element) -> "CoqStatus":
        """Expect:
        <status>(list string) (option string) (list string) int int</status>
        """
        return self.CoqStatus(*map(self._to_py, xml))

    def _to_coq_info(self, xml: ET.Element) -> "CoqInfo":
        """Expect: <coq_info>string string string string</coq_info>"""
        return self.CoqInfo(*map(self._to_py, xml))

    def _to_message(self, xml: ET.Element) -> str:
        """Expect: <message>message_level string</message>"""
        # xml[1] is a string
        return cast(str, self._to_py(xml[1]))

    def _to_feedback(self, xml: ET.Element) -> str:
        """Expect:
        <feedback object="?" route="int">feedback_content</feedback>
        <feedback_content val="errormsg">loc string</feedback_content>
        """
        # pylint: disable=no-else-return
        content = xml[0]

        if content.get("val") == "errormsg":
            # content[1] is a string
            return cast(str, self._to_py(content[1]))
        else:
            # TODO: maybe make use of this info?
            return ""

    # Rocq Commands #
    def init(self, _encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to initialize Rocq.
        Not a command in 8.4 so return dummy command.
        """
        return ("Init", None)

    def _standardize_init(self, _res: Result) -> Ok:
        """Standardize the info returned by 'Init'.
        Return:
          state_id: int - The current state id (ignored in 8.4)
        """
        return Ok(0)

    def add(
        self,
        cmd: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to advance Rocq.
        Attrs:
          verbose: bool - Verbose output
          id: int - The current state id
        Args:
          cmd: string - The command to evaluate
        """
        return (
            "Add",
            self._make_call(
                encoding,
                "interp",
                attrs={"verbose": "true", "id": str(state)},
                arg=cmd,
            ),
        )

    def _standardize_add(self, res: Result) -> Result:
        """Standardize the info returned by 'Add'.
        Return:
          res_msg: str - Messages produced by 'Add'
          state_id: int - The new state id (ignored in 8.4)
        """
        if isinstance(res, Ok):
            res_msg: str = res.val
            res.val = {"res_msg": res_msg, "state_id": 0}
        return res

    def edit_at(
        self,
        _state: int,
        steps: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to move Rocq to a specific location.
        Attrs:
          steps: int - The number of steps to rewind
        """
        return (
            "Edit_at",
            self._make_call(encoding, "rewind", attrs={"steps": str(steps)}),
        )

    def query(
        self,
        query: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to pose a query to Rocq.
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

    def _standardize_query(self, res: Result) -> Result:
        """Standardize the info returned by 'Query'.
        Return:
          msg: str - Messages produced by 'Query'
        """
        if isinstance(res, Ok):
            msg: str = res.val
            res.msg = msg
        return res

    def goal(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check the current goal state.
        Args:
          _: unit - Empty arg
        """
        return ("Goal", self._make_call(encoding, "goal", children=()))

    def _standardize_goal(self, res: Result) -> Result:
        """Standardize the info returned by 'Goal'.
        Return:
          fg: list Goal - The current goals
          bg: list (list Goal * list Goal) - Unfocused goals
          shelved: list Goal - Shelved goals (dummy value in 8.4)
          given_up: list Goal - Admitted goals (dummy value in 8.4)
        """

        def to_goal(g: XMLInterface84.CoqGoal) -> Goal:
            return Goal(g.hyp, g.ccl, None)

        if isinstance(res, Ok):
            goals: Optional[XMLInterface84.CoqGoals] = (
                XMLInterfaceBase.unwrap_coq_option(res.val)
            )
            if goals is not None:
                res.val = Goals(
                    [to_goal(g) for g in goals.fg],
                    [[to_goal(g) for g in pre + post] for pre, post in goals.bg],
                    [],
                    [],
                )
        return res

    def status(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check Rocq's status.
        Args:
          _: unit - Empty arg
        """
        return ("Status", self._make_call(encoding, "status", children=()))

    def get_options(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check the state of Rocq's options.
        Args:
          _: unit - Empty arg
        """
        return ("GetOptions", self._make_call(encoding, "getoptions", children=()))

    def _standardize_get_options(self, res: Result) -> Result:
        """Standardize the info returned by 'GetOptions'.
        Return:
          opts: list (string * string * ?) - Triples of all option names,
                                             descriptions, and current values
        """
        if isinstance(res, Ok):
            raw_opts: List[Tuple[str, "XMLInterface84.CoqOptionState"]] = res.val
            opts: List[Tuple[str, str, Any]] = [
                (" ".join(name), state.name, state.value.val)
                for name, state in raw_opts
            ]
            res.val = opts
        return res

    def set_options(
        self,
        option: str,
        val: XMLInterfaceBase.OptionArg,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to set one of Rocq's options.
        Args:
          options: list (option_name * option_value) - The options to update and
                                                       the values to set them to
        """
        optval: Optional[Union[bool, str, XMLInterfaceBase.Some]]
        if isinstance(val, int) and not isinstance(val, bool):
            optval = self.Some(val)
        elif isinstance(val, tuple):
            optval = None
        else:
            optval = val

        # TODO: Rocq source (toplevel/interface.mli) looks like the argument
        # should be a list like in version 8.5 and on, but it only seems to
        # work if it is a single element
        return (
            "SetOptions",
            self._make_call(
                encoding,
                "setoptions",
                children=(option.split(), self.CoqOptionValue(optval, None)),
            ),
        )


# The XML interface is different enough between 8.4 and > 8.4 that the
# following interfaces will not inherit from XMLInterface84
class XMLInterface85(XMLInterfaceBase):
    """The version 8.5.* XML interface."""

    # Rocq Types #
    CoqGoal = NamedTuple("CoqGoal", [("id", str), ("hyp", List[str]), ("ccl", str)])
    CoqGoals = NamedTuple(
        "CoqGoals",
        [
            ("fg", List[CoqGoal]),
            ("bg", List[Tuple[List[CoqGoal], List[CoqGoal]]]),
            ("shelved", List[CoqGoal]),
            ("given_up", List[CoqGoal]),
        ],
    )
    CoqEvar = NamedTuple("CoqEvar", [("info", str)])

    CoqOptionValue = NamedTuple(
        "CoqOptionValue",
        [
            ("val", Union[bool, XMLInterfaceBase.CoqOption, str]),
            ("type", Optional[str]),
        ],
    )
    CoqOptionState = NamedTuple(
        "CoqOptionState",
        [("sync", bool), ("depr", bool), ("name", str), ("value", CoqOptionValue)],
    )

    CoqStateId = NamedTuple("CoqStateId", [("id", int)])
    CoqStatus = NamedTuple(
        "CoqStatus",
        [
            ("path", List[str]),
            ("proofname", XMLInterfaceBase.CoqOption),
            ("allproofs", List[str]),
            ("proofnum", int),
        ],
    )
    CoqInfo = NamedTuple(
        "CoqInfo",
        [
            ("coq_version", str),
            ("protocol_version", str),
            ("release_data", str),
            ("compile_data", str),
        ],
    )

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(
            version,
            str_version,
            coq_path,
            "coqtop" if coq_prog is None else coq_prog,
        )

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

        self._of_py_funcs.update(
            {
                "CoqOptionValue": self._of_option_value,
                "CoqStateId": self._of_state_id,
            }
        )

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
    def _to_goal(self, xml: ET.Element) -> "CoqGoal":
        """Expect: <goal>string (list Pp) Pp</goal>"""
        return self.CoqGoal(*map(self._to_py, xml))

    def _to_goals(self, xml: ET.Element) -> "CoqGoals":
        """Expect:
        <goals>
          (list goal) (list (list goal * list goal))
          (list goal) (list goal)
        </goals>
        """
        return self.CoqGoals(*map(self._to_py, xml))

    def _to_evar(self, xml: ET.Element) -> "CoqEvar":
        """Expect: <evar>string</evar>"""
        return self.CoqEvar(self._to_py(xml[0]))

    def _to_option_value(self, xml: ET.Element) -> "CoqOptionValue":
        """Expect:
        <option_value>bool | option int | string | option string</option_value>
        """
        ty = xml.get("val", None)
        if ty is not None:
            if ty.startswith("int"):
                ty = "int"
            elif ty.startswith("str"):
                ty = "str"
            else:
                ty = "bool"
        return self.CoqOptionValue(self._to_py(xml[0]), ty)

    def _of_option_value(self, val: CoqOptionValue) -> ET.Element:
        """Expect:
        CoqOptionValue(bool) | CoqOptionValue(int | None) | CoqOptionValue(str) |
        CoqOptionValue(str | None)
        """
        opt = val.val

        if isinstance(opt, bool):
            opt_ty = "boolvalue"
        elif isinstance(opt, str):
            opt_ty = "stringvalue"
        elif (isinstance(opt, self.Some) and isinstance(opt.val, int)) or (
            opt is None and val.type == "int"
        ):
            opt_ty = "intvalue"
        elif (isinstance(opt, self.Some) and isinstance(opt.val, str)) or (
            opt is None and val.type == "str"
        ):
            opt_ty = "stringoptvalue"
        else:
            raise unexpected((bool, self.Some, None, str), type(opt))

        return self._build_xml("option_value", opt_ty, opt)

    def _to_option_state(self, xml: ET.Element) -> "CoqOptionState":
        """Expect: <option_state>bool bool string option_value</option_state>"""
        return self.CoqOptionState(*map(self._to_py, xml))

    def _to_state_id(self, xml: ET.Element) -> "CoqStateId":
        """Expect: <state_id val="int" />"""
        return self.CoqStateId(int(xml.get("val", 0)))

    def _of_state_id(self, val: CoqStateId) -> ET.Element:
        """Expect: CoqStateId(int)"""
        return self._build_xml("state_id", str(val.id))

    def _to_status(self, xml: ET.Element) -> "CoqStatus":
        """Expect:
        <status>(list string) (option string) (list string) int</status>
        """
        return self.CoqStatus(*map(self._to_py, xml))

    def _to_coq_info(self, xml: ET.Element) -> "CoqInfo":
        """Expect: <coq_info>string string string string</coq_info>"""
        return self.CoqInfo(*map(self._to_py, xml))

    def _to_message(self, xml: ET.Element) -> str:
        """Expect: <message>message_level string</message>"""
        # xml[1] is a string
        return cast(str, self._to_py(xml[1]))

    def _to_feedback(self, xml: ET.Element) -> str:
        """Expect:
        <feedback object="?" route="int">feedback_content</feedback>
        <feedback_content val="errormsg">loc string</feedback_content>
        """
        # pylint: disable=no-else-return
        content = xml[0]

        if content.get("val") == "errormsg":
            # content[1] is a string
            return cast(str, self._to_py(content[1]))
        else:
            # TODO: maybe make use of this info?
            return ""

    # Rocq Commands #
    def init(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to initialize Rocq.
        Args:
          option string - A Rocq file to add to the LoadPath to do ?
        """
        return ("Init", self._make_call(encoding, "Init", children=None))

    def _standardize_init(self, res: Result) -> Result:
        """Standardize the info returned by 'Init'.
        Return:
          state_id: int - The current state id
        """
        if isinstance(res, Ok):
            val: "XMLInterface85.CoqStateId" = res.val
            res.val = val.id
        return res

    def add(
        self,
        cmd: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to advance Rocq.
        Args:
          cmd: string - The command to evaluate
          edit_id: int - The current edit id ?
          state_id: CoqStateId - The current state id
          verbose: bool - Verbose output
        """
        return (
            "Add",
            self._make_call(
                encoding,
                "Add",
                children=((cmd, -1), (self.CoqStateId(state), True)),
            ),
        )

    def _standardize_add(self, res: Result) -> Result:
        """Standardize the info returned by 'Add'.
        Return:
          res_msg: str - Messages produced by 'Add'
          state_id: int - The new state id
        """
        if isinstance(res, Ok):
            val: Tuple["XMLInterface85.CoqStateId", Tuple[Any, str]] = res.val
            res.val = {"res_msg": val[1][1], "state_id": val[0].id}
        return res

    def edit_at(
        self,
        state: int,
        _steps: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to move Rocq to a specific location.
        Args:
          state_id: CoqStateId - The state id to move to
        """
        return (
            "Edit_at",
            self._make_call(encoding, "Edit_at", children=self.CoqStateId(state)),
        )

    def _standardize_edit_at(self, res: Result) -> Result:
        """Standardize the info returned by 'Edit_at'.
        Return:
          extra_steps: int - The number of additional steps rewound (ignored in >8.4)
        """
        if isinstance(res, Ok):
            res.val = 0
        return res

    def query(
        self,
        query: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to pose a query to Rocq.
        Args:
          query: string - The query to evaluate
          state_id: CoqStateId - The current state id
        """
        return (
            "Query",
            self._make_call(
                encoding,
                "Query",
                children=(query, self.CoqStateId(state)),
            ),
        )

    def goal(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check the current goal state.
        Args:
          _: unit - Empty arg
        """
        return ("Goal", self._make_call(encoding, "Goal", children=()))

    def _standardize_goal(self, res: Result) -> Result:
        """Standardize the info returned by 'Goal'.
        Return:
          fg: list Goal - The current goals
          bg: list (list Goal * list Goal) - Unfocused goals
          shelved: list Goal - Shelved goals
          given_up: list Goal - Admitted goals
        """

        def to_goal(g: XMLInterface85.CoqGoal) -> Goal:
            return Goal(g.hyp, g.ccl, None)

        if isinstance(res, Ok):
            goals: Optional[XMLInterface85.CoqGoals] = (
                XMLInterfaceBase.unwrap_coq_option(res.val)
            )
            if goals is not None:
                res.val = Goals(
                    [to_goal(g) for g in goals.fg],
                    [[to_goal(g) for g in pre + post] for pre, post in goals.bg],
                    [to_goal(g) for g in goals.shelved],
                    [to_goal(g) for g in goals.given_up],
                )
        return res

    def status(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check Rocq's status.
        Args:
          force: bool - Force all pending evaluations
        """
        return ("Status", self._make_call(encoding, "Status", children=True))

    def get_options(self, encoding: str = "utf-8") -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check the state of Rocq's options.
        Args:
          _: unit - Empty arg
        """
        return ("GetOptions", self._make_call(encoding, "GetOptions", children=()))

    def _standardize_get_options(self, res: Result) -> Result:
        """Standardize the info returned by 'GetOptions'.
        Return:
          opts: list (string * string * ?) - Triples of all option names,
                                             descriptions, and current values
        """
        if isinstance(res, Ok):
            raw_opts: List[Tuple[str, "XMLInterface85.CoqOptionState"]] = res.val
            opts: List[Tuple[str, str, Any]] = [
                (" ".join(name), state.name, state.value.val)
                for name, state in raw_opts
            ]
            res.val = opts
        return res

    def set_options(
        self,
        option: str,
        val: XMLInterfaceBase.OptionArg,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to set one of Rocq's options.
        Args:
          options: list (option_name * option_value) - The options to update and
                                                       the values to set them to
        """
        ty = None
        optval: Optional[Union[bool, str, XMLInterfaceBase.Some]]
        if isinstance(val, int) and not isinstance(val, bool):
            optval = self.Some(val)
        elif isinstance(val, tuple):
            optval, ty = val
        else:
            optval = val

        # extra '[]' needed so _build_xml treats it as one list instead
        # of several children to convert
        return (
            "SetOptions",
            self._make_call(
                encoding,
                "SetOptions",
                children=[[(option.split(), self.CoqOptionValue(optval, ty))]],
            ),
        )


class XMLInterface86(XMLInterface85):
    """The version 8.6.* XML interface."""

    # Tags to look for when parsing richpp
    richpp_tags = [
        "diff.added",
        "diff.removed",
        "diff.added.bg",
        "diff.removed.bg",
    ]

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(version, str_version, coq_path, coq_prog)

        self.launch_args += [
            "-async-proofs-command-error-resilience",
            "off",
            "-async-proofs-tactic-error-resilience",
            "off",
        ]

        self._to_py_funcs.update({"richpp": self._to_richpp})

        self.warnings_wf = True

    def _to_richpp(self, xml: ET.Element) -> List[Tuple[str, Optional[str]]]:
        """Expect: <richpp>richpp</richpp>"""
        return list(parse_tagged_tokens(self.richpp_tags, xml))

    # XML Parsing and Marshalling #
    # Overrides _to_message() from 8.5
    def _to_message(self, xml: ET.Element) -> str:
        """Expect: <message>message_level (option ?) richpp</message>"""
        # TODO: see if option or message_level are useful
        # xml[2] is a string
        return cast(str, self._to_py(xml[2]))

    # Overrides _to_feedback() from 8.5
    def _to_feedback(self, xml: ET.Element) -> str:
        """Expect:
        <feedback object="?" route="int">state_id feedback_content</feedback>
        <feedback_content val="message">message</feedback_content>
        """
        # pylint: disable=no-else-return
        content = xml[1]

        if content.get("val") == "message":
            # content[0] is a string
            return cast(str, self._to_py(content[0]))
        else:
            # TODO: maybe make use of this info?
            return ""


class XMLInterface87(XMLInterface86):
    """The version 8.7.* XML interface."""

    CoqRouteId = NamedTuple("CoqRouteId", [("id", int)])

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(version, str_version, coq_path, coq_prog)

        self._to_py_funcs.update({"route_id": self._to_route_id})

        self._of_py_funcs.update({"CoqRouteId": self._of_route_id})

    # XML Parsing and Marshalling #
    def _to_route_id(self, xml: ET.Element) -> "CoqRouteId":
        """Expect: <route_id val="int" />"""
        return self.CoqRouteId(int(xml.get("val", 0)))

    def _of_route_id(self, val: CoqRouteId) -> ET.Element:
        """Expect: CoqRouteId(int)"""
        return self._build_xml("route_id", str(val.id))

    # Rocq Commands #
    # Overrides query() from 8.6
    def query(
        self,
        query: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to pose a query to Rocq.
        Args:
          route_id: CoqRouteId - The route id ?
          query: string - The query to evaluate
          state_id: CoqStateId - The current state id
        """
        return (
            "Query",
            self._make_call(
                encoding,
                "Query",
                (self.CoqRouteId(0), (query, self.CoqStateId(state))),
            ),
        )


class XMLInterface88(XMLInterface87):
    """The version 8.8.* XML interface."""


class XMLInterface89(XMLInterface88):
    """The version 8.9.* XML interface."""

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update launch arguments."""
        # Rocq 8.9 split 'coqtop -ideslave' into a separate coqidetop binary
        super().__init__(
            version,
            str_version,
            coq_path,
            "coqidetop" if coq_prog is None else coq_prog,
        )

        self.launch_args.remove("-ideslave")

        # For some reason 8.9 includes extra text such as 'While loading
        # initial state:'.
        self.warnings_wf = False


class XMLInterface810(XMLInterface89):
    """The version 8.10.* XML interface."""

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update launch arguments."""
        super().__init__(version, str_version, coq_path, coq_prog)

        # Warnings are once again parseable by `partition_warnings`.
        self.warnings_wf = True

    @staticmethod
    def topfile(filename: str, args: Iterable[str]) -> Tuple[str, ...]:
        """The command to set the top-level module name."""
        return (
            ("-topfile", filename)
            if all(arg not in args for arg in ("-top", "-topfile"))
            and XMLInterfaceBase.valid_module(filename)
            else ()
        )


class XMLInterface811(XMLInterface810):
    """The version 8.11.* XML interface."""


class XMLInterface812(XMLInterface811):
    """The version 8.12.* XML interface."""

    CoqOptionState = NamedTuple(
        "CoqOptionState",
        [("sync", bool), ("depr", bool), ("value", "XMLInterface812.CoqOptionValue")],
    )

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(version, str_version, coq_path, coq_prog)

        self._standardize_funcs.update({"GetOptions": self._standardize_get_options})

    def _to_option_state(self, xml: ET.Element) -> "CoqOptionState":  # type: ignore[override]
        """Expect: <option_state>bool bool option_value</option_state>"""
        return self.CoqOptionState(*map(self._to_py, xml))

    def _standardize_get_options(self, res: Result) -> Result:
        """Standardize the info returned by 'GetOptions'.
        Return:
          opts: list (string * string * ?) - Triples of all option names,
                                             descriptions, and current values
        """
        if isinstance(res, Ok):
            raw_opts: List[Tuple[str, "XMLInterface812.CoqOptionState"]] = res.val
            opts: List[Tuple[str, str, Any]] = [
                (" ".join(name), " ".join(name), state.value.val)
                for name, state in raw_opts
            ]
            res.val = opts
        return res


class XMLInterface813(XMLInterface812):
    """The version 8.13.* XML interface."""


class XMLInterface814(XMLInterface813):
    """The version 8.14.* XML interface."""

    CoqGoal = NamedTuple(
        "CoqGoal",
        [
            ("id", str),
            ("hyp", List[str]),
            ("ccl", str),
            ("name", "XMLInterface814.CoqOption"),
        ],
    )
    CoqGoals = NamedTuple(
        "CoqGoals",
        [
            ("fg", List[CoqGoal]),
            ("bg", List[Tuple[List[CoqGoal], List[CoqGoal]]]),
            ("shelved", List[CoqGoal]),
            ("given_up", List[CoqGoal]),
        ],
    )

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(version, str_version, coq_path, coq_prog)

        # Starting with MyPy 0.920 it complains about the return type of
        # `_to_goals` without an explicit cast.
        self._to_py_funcs.update(
            cast(
                Dict[str, Callable[[ET.Element], Any]],
                {
                    "goal": self._to_goal,
                    "goals": self._to_goals,
                },
            )
        )
        self._standardize_funcs.update({"Goal": self._standardize_goal})

    def _to_goal(self, xml: ET.Element) -> "CoqGoal":  # type: ignore[override]
        """Expect: <goal>string (list Pp) Pp (option string)</goal>"""
        return self.CoqGoal(*map(self._to_py, xml))

    def _to_goals(self, xml: ET.Element) -> "CoqGoals":  # type: ignore[override]
        """Expect:
        <goals>
          (list goal) (list (list goal * list goal))
          (list goal) (list goal)
        </goals>
        """
        return self.CoqGoals(*map(self._to_py, xml))

    def _standardize_goal(self, res: Result) -> Result:
        """Standardize the info returned by 'Goal'.
        Return:
          fg: list Goal - The current goals
          bg: list (list Goal * list Goal) - Unfocused goals
          shelved: list Goal - Shelved goals
          given_up: list Goal - Admitted goals
        """

        def to_goal(g: XMLInterface814.CoqGoal) -> Goal:
            return Goal(g.hyp, g.ccl, XMLInterfaceBase.unwrap_coq_option(g.name))

        if isinstance(res, Ok):
            goals: Optional[XMLInterface814.CoqGoals] = (
                XMLInterfaceBase.unwrap_coq_option(res.val)
            )
            if goals is not None:
                res.val = Goals(
                    [to_goal(g) for g in goals.fg],
                    [[to_goal(g) for g in pre + post] for pre, post in goals.bg],
                    [to_goal(g) for g in goals.shelved],
                    [to_goal(g) for g in goals.given_up],
                )
        return res


class XMLInterface815(XMLInterface814):
    """The version 8.15.* XML interface."""

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(version, str_version, coq_path, coq_prog)

        self._standardize_funcs.update({"Add": self._standardize_add})

    # Overrides add() from 8.5
    def add(
        self,
        cmd: str,
        state: int,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to advance Rocq.
        Args:
          cmd: string - The command to evaluate
          edit_id: int - The current edit id ?
          state_id: CoqStateId - The current state id
          verbose: bool - Verbose output
          bp: int - Byte offset of phrase in script
          line_nb: int - Line number of phrase in script
          bol_pos: int - Byte offset for beginning of line
        """
        return (
            "Add",
            self._make_call(
                encoding,
                "Add",
                children=((((cmd, -1), (self.CoqStateId(state), True)), 0), (0, 0)),
            ),
        )

    def _standardize_add(self, res: Result) -> Result:
        """Standardize the info returned by 'Add'.
        Return:
          res_msg: str - Messages produced by 'Add' (removed in 8.14)
          state_id: int - The new state id
        """
        if isinstance(res, Ok):
            val: Tuple[XMLInterface85.CoqStateId, Any] = res.val
            res.val = {"res_msg": "", "state_id": val[0].id}
        return res


class XMLInterface816(XMLInterface815):
    """The version 8.16.* XML interface."""

    CoqGoalFlags = NamedTuple(
        "CoqGoalFlags",
        [
            ("mode", str),
            ("fg", bool),
            ("bg", bool),
            ("shelved", bool),
            ("given_up", bool),
        ],
    )

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(version, str_version, coq_path, coq_prog)

        self._of_py_funcs.update({"CoqGoalFlags": self._of_goal_flags})

        self._standardize_funcs.update({"Subgoals": self._standardize_goal})

    def _of_goal_flags(self, val: CoqGoalFlags) -> ET.Element:
        """Expect: CoqGoalFlags(str, bool, bool, bool, bool)"""
        return self._build_xml(
            "goal_flags",
            children=[val.mode, val.fg, val.bg, val.shelved, val.given_up],
        )

    def subgoal(
        self,
        mode: GoalMode,
        fg: bool = True,
        bg: bool = True,
        shelved: bool = True,
        given_up: bool = True,
        encoding: str = "utf-8",
    ) -> Tuple[str, Optional[bytes]]:
        """Create an XML string to check the state a specific set of goals.
        Args:
          flags: CoqGoalFlags - Which goals to return
        """
        return (
            "Subgoals",
            self._make_call(
                encoding,
                "Subgoals",
                children=self.CoqGoalFlags(mode.value, fg, bg, shelved, given_up),
            ),
        )


class XMLInterface817(XMLInterface816):
    """The version 8.17.* XML interface."""


class XMLInterface818(XMLInterface817):
    """The version 8.18.* XML interface."""


class XMLInterface819(XMLInterface818):
    """The version 8.19.* XML interface."""


class XMLInterface820(XMLInterface819):
    """The version 8.20.* XML interface."""

    Loc = NamedTuple(
        "Loc",
        [
            ("start", int),
            ("stop", int),
            ("line_nb", int),
            ("bol_pos", int),
            ("line_nb_last", int),
            ("bol_pos_last", int),
        ],
    )

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Update conversion maps with new types."""
        super().__init__(version, str_version, coq_path, coq_prog)

        self._to_py_funcs.update({"loc": self._to_loc})

    def _to_loc(self, xml: ET.Element) -> Loc:
        """Expect:
        <loc start="int" stop="int" line_nb="int" bol_pos="int"
             line_nb_last="int" bol_pos_last="int" />
        """

        def assert_int(v: Optional[str]) -> int:
            assert v is not None
            return int(v)

        return self.Loc(
            assert_int(xml.get("start")),
            assert_int(xml.get("stop")),
            assert_int(xml.get("line_nb")),
            assert_int(xml.get("bol_pos")),
            assert_int(xml.get("line_nb_last")),
            assert_int(xml.get("bol_pos_last")),
        )

    # Overrides _to_response from XMLInterfaceBase
    def _to_response(self, xml: ET.Element) -> Result:
        """Expect:
        <value val="good">val</value> |
        <value val="fail">state_id (option loc) msg</value>
        """
        # pylint: disable=no-else-return
        val = xml.get("val")

        if val == "good":
            return Ok(self._to_py(xml[0]))
        elif val == "fail":
            loc = self._to_py(xml[1])
            loc_s, loc_e = (
                (loc.val.start, loc.val.stop) if loc is not None else (-1, -1)
            )

            msg = "".join(xml.itertext())

            return Err(msg, (loc_s, loc_e))
        raise unexpected(("good", "fail"), val)


class XMLInterface90(XMLInterface820):
    """The version 9.0.* XML interface."""

    def __init__(
        self,
        version: Tuple[int, int, int],
        str_version: str,
        coq_path: str,
        coq_prog: Optional[str],
    ) -> None:
        """Add new queries."""
        super().__init__(version, str_version, coq_path, coq_prog)

        self.queries += ["Guarded", "Validate Proof"]


class XMLInterface91(XMLInterface90):
    """The version 9.1.* XML interface."""


XMLInterfaces = (
    ((8, 4, 0), (8, 5, 0), XMLInterface84),
    ((8, 5, 0), (8, 6, 0), XMLInterface85),
    ((8, 6, 0), (8, 7, 0), XMLInterface86),
    ((8, 7, 0), (8, 8, 0), XMLInterface87),
    ((8, 8, 0), (8, 9, 0), XMLInterface88),
    ((8, 9, 0), (8, 10, 0), XMLInterface89),
    ((8, 10, 0), (8, 11, 0), XMLInterface810),
    ((8, 11, 0), (8, 12, 0), XMLInterface811),
    ((8, 12, 0), (8, 13, 0), XMLInterface812),
    ((8, 13, 0), (8, 14, 0), XMLInterface813),
    ((8, 14, 0), (8, 15, 0), XMLInterface814),
    ((8, 15, 0), (8, 16, 0), XMLInterface815),
    ((8, 16, 0), (8, 17, 0), XMLInterface816),
    ((8, 17, 0), (8, 18, 0), XMLInterface817),
    ((8, 18, 0), (8, 19, 0), XMLInterface818),
    ((8, 19, 0), (8, 20, 0), XMLInterface819),
    ((8, 20, 0), (8, 21, 0), XMLInterface820),
    ((9, 0, 0), (9, 1, 0), XMLInterface90),
    ((9, 1, 0), (9, 2, 0), XMLInterface91),
)

XMLInterfaceLatest = XMLInterfaces[-1][2]


def find_coq(coq_path: Optional[str], coq_prog: Optional[str]) -> str:
    """Find the path to the Rocq executable."""
    coq_progs = ("coqc", "rocq") if coq_prog is None else (coq_prog,)
    for prog in coq_progs:
        coq = which(prog, path=coq_path)
        if coq is not None:
            return coq
    path = "$PATH" if coq_path is None else coq_path
    raise FindCoqtopError(
        f"Could not find {' or '.join(coq_progs)} in {path}. Perhaps you need "
        "to set g:coqtail_coq_path or g:coqtail_coq_prog."
    )


def extract_version(coq: str) -> str:
    """Parse the output of coq --version."""
    try:
        version = subprocess.run(
            [coq, "--version"],
            check=True,
            stdout=subprocess.PIPE,
        ).stdout.decode("utf-8")
        match = re.search(r"version (\S+)", version)
        if match is None:
            raise FindCoqtopError(f"Failed to parse '{coq} --version'.")
        return match.group(1)
    except subprocess.CalledProcessError as e:
        raise FindCoqtopError(f"Executing '{coq} --version' failed.") from e


def parse_version(version: str) -> Tuple[int, int, int]:
    """Parse a version string into a 3-tuple."""
    match = re.fullmatch(r"(\d+)\.(\d+)(?:(?:\.|pl)(\d+)|\+\w+\d*)?", version)
    if match is None:
        raise ValueError(f"Invalid version: {version}")
    major, minor, patch = match.groups()
    assert major is not None
    assert minor is not None
    patch = "0" if patch is None else patch
    return (int(major), int(minor), int(patch))


def XMLInterface(
    coq_path: Optional[str],
    coq_prog: Optional[str],
) -> Tuple[XMLInterfaceBase, Optional[str]]:
    """Return the appropriate XMLInterface class for the given version."""
    coq = find_coq(coq_path, coq_prog)
    coq_path = str(Path(coq).parent)
    str_version = extract_version(coq)
    version = parse_version(str_version)

    for minVer, maxVer, xmlInt in XMLInterfaces:
        if minVer <= version < maxVer:
            return xmlInt(version, str_version, coq_path, coq_prog), None
    return (
        XMLInterfaceLatest(version, str_version, coq_path, coq_prog),
        ".".join(map(str, XMLInterfaces[-1][0])),
    )
