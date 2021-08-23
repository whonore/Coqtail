# -*- coding: utf8 -*-
# Author: Wolf Honore
"""Warning partitioning unit tests."""

from coqtop import partition_warnings


def test_partition_warnings():
    """partition_warnings separates warnings from error messages."""
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
