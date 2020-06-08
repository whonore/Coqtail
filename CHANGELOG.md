# Change Log

## Unreleased [master]

## [1.0.0]

### Added
- Use `+channel` feature (Vim >=8.0 only) to enable non-blocking communication
  with Coq.
- Use a synchronous fallback for Vim 7.4.
- `CoqInterrupt` command that forwards `SIGINT` to the Coq process.
- `CoqRestorePanel` command that re-opens the Goal and Info panels in their
  original positions.
- Changelog, begin using semantic (more or less) versioning.

### Removed
- Dependency on `vim` module in Python code.
- Dependency on [vimbufsync].
- `CoqMakeMatch` command.
  It wasn't well thought out and didn't seem very useful.
  Please [open an issue](https://github.com/whonore/Coqtail/issues) if you'd
  like it to be re-added.

### Fixed
- No longer crash if Goal or Info panels are closed.

## [pre-1.0]

### Added
- Interactive Coq proofs similar to CoqIDE/Proof General.
- Support for Vim >=7.4.
- Support for Python 2 and 3.
- Support for Coq 8.4-8.11.
- Support simultaneous Coq sessions in different buffers.
- Locate and parse _CoqProject files.
- Coq syntax highlighting.
- Coq automatic indentation.
- Allow jumping to definitions.
- Allow following imports for autocompletion.
- Support for `:tag` commands (only with `+tagfunc`).
- Interoperability with [matchup] and [endwise].

[master]: https://github.com/whonore/Coqtail
[1.0.0]: https://github.com/whonore/Coqtail/tree/v1.0.0
[pre-1.0]: https://github.com/whonore/Coqtail/tree/pre-1.0
[vimbufsync]: https://github.com/let-def/vimbufsync
[matchup]: https://github.com/andymass/vim-matchup
[endwise]: https://github.com/tpope/vim-endwise
