# Change Log

## Unreleased ([master])

### Fixed
- Lowered priority of Coqtail-related highlighting (`CoqtailChecked`,
  `CoqtailSent`, `CoqtailError`) so they don't cover existing highlighting, e.g.
  from `'hlsearch'`.
- Only call `coqtail#stop` on `:quit` if it would close the last visible
  instance of the buffer.
- Coqtail highlighting correctly handles multibyte characters.
- All pending sentences waiting to be checked by Coq (`CoqtailSent`) are
  highlighted instead of just the next one.
- Made `:Coq` and `:CoqGotoDef` not treat arguments containing `"` as comments
  by removing `-bar` option.
- When choosing between `coq(ide)top` and `coq(ide)top.opt` respect the `$PATH` order.

## [1.0.0]

### Added
- Non-blocking communication with Coq using the `+channel` feature (Vim >=8.0 only).
- A synchronous fallback for Vim 7.4.
- `CoqInterrupt` command that forwards `SIGINT` to the Coq process.
- `CoqRestorePanels` command that re-opens the Goal and Info panels in their
  original positions.
- This changelog. Begin using semantic (more or less) versioning.

### Removed
- Dependency on `vim` module in Python code.
- Dependency on [vimbufsync].
- `CoqMakeMatch` command.
  It wasn't well thought out and didn't seem very useful.
  Please [open an issue](https://github.com/whonore/Coqtail/issues) if you'd
  like it to be re-added.

### Fixed
- Commands no longer crash when called while Goal or Info panels are closed.

### Deprecated
- Python 2 support. See [YouCompleteMe] for help building Vim with Python 3 support.

## [pre-1.0]

### Added
- Interactive Coq interface similar to CoqIDE/Proof General.
- Support for Vim >=7.4.
- Support for Python 2 and 3.
- Support for Coq 8.4-8.11.
- Support for simultaneous Coq sessions in different buffers.
- Locating and parsing of _CoqProject files.
- Coq syntax highlighting.
- Coq automatic indentation.
- `CoqGotoDef` command for jumping to definitions.
- `includeexpr` for following imports during autocompletion.
- Support for `:tag` commands (only with `+tagfunc`).
- Interoperability with [matchup] and [endwise].

[master]: https://github.com/whonore/Coqtail
[1.0.0]: https://github.com/whonore/Coqtail/tree/v1.0.0
[pre-1.0]: https://github.com/whonore/Coqtail/tree/pre-1.0
[vimbufsync]: https://github.com/let-def/vimbufsync
[matchup]: https://github.com/andymass/vim-matchup
[endwise]: https://github.com/tpope/vim-endwise
[YouCompleteMe]: https://github.com/ycm-core/YouCompleteMe/wiki/Building-Vim-from-source
