# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Warning partitioning unit tests."""

from coqtop import partition_warnings


def test_partition_warnings():
    """partition_warnings separates warnings from error messages."""
    msg = """
Warning: message
continued
[type,?]
Warning: another one [type,?]
Not a warning,
just an error.
Warning: again [type, ?]
Final error.
    """.strip()

    warn = """
Warning: message
continued
[type,?]
Warning: another one [type,?]
Warning: again [type, ?]
    """.strip()

    err = """
Not a warning,
just an error.
Final error.
    """.strip()

    assert partition_warnings(msg) == (warn, err)
