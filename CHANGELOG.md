# Change Log

## Unreleased ([master])

### Added
- Support for multiple `_CoqProject` files. **BREAKING**: renamed
  `g:coqtail_project_name` to `g:coqtail_project_names` and
  `b:coqtail_project_file` to `b:coqtail_project_files`.

### Fixed
- Recognize and highlight strings in more contexts. (PR #139)

## [1.2.0]

### Added
- Support for Coq 8.12. (PR #120)
- `g:coqtail_noimap`, `g:coqtail_map_prefix`, `g:coqtail_imap_prefix`
  configuration options to control insert-mode mappings. (PR #122)
- Mappings for query commands (`<leader>cs`, `<leader>ch`, etc) now work on the
  highlighted range in Visual mode. (PR #131)
- Commands and mappings now work when called in the Goal and Info panels. (PR #132)

### Fixed
- `g:coqtail_coq_path` is now checked on `:CoqStart` instead of on buffer load.
  (PR #123)
- `:CoqStart` no longer fails when the Coq executable is in the current directory.
  (PR #123)
- Various syntax highlighting/indentation improvements. (PRs #124, #126, #127)
- No longer crash when checking Coq version if `coqtop.opt` does not exist. (PR #129)
- No longer crash on `:CoqStart` when a buffer has no associated file. (PR #137)
- Improved interrupt-handling logic, which should reduce the frequency of the
  case where pending commands are not cleared and `nomodifiable` is set after
  every command. (PR #130)

## [1.1.0]

### Added
- Support for NeoVim >=0.3. (PR #103)
- `b:coqtail_coq_prog`/`g:coqtail_coq_prog` configuration option to override
  the name of the Coq executable. (PR #119)

### Fixed
- Lowered priority of Coqtail-related highlighting (`CoqtailChecked`,
  `CoqtailSent`, `CoqtailError`) so they don't cover existing highlighting, e.g.
  from `'hlsearch'`. (PR #104)
- Only call `coqtail#stop` on `:quit` if it would close the last visible
  instance of the buffer. (PR #105)
- Coqtail highlighting correctly handles multibyte characters. (PR #109)
- All pending sentences waiting to be checked by Coq (`CoqtailSent`) are
  highlighted instead of just the next one. (PR #109)
- `:Coq` and `:CoqGotoDef` do not treat arguments containing `"` as comments
  by removing `-bar` option. (PR #111)
- Respect the `$PATH` order when choosing between `coq(ide)top` and
  `coq(ide)top.opt`. (PR #114).
- No longer crash ("E803: ID not found") after `:split`ting the main Coq window.
  (PR #118)

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
[1.2.0]: https://github.com/whonore/Coqtail/tree/v1.2.0
[1.1.0]: https://github.com/whonore/Coqtail/tree/v1.1.0
[1.0.0]: https://github.com/whonore/Coqtail/tree/v1.0.0
[pre-1.0]: https://github.com/whonore/Coqtail/tree/pre-1.0
[vimbufsync]: https://github.com/let-def/vimbufsync
[matchup]: https://github.com/andymass/vim-matchup
[endwise]: https://github.com/tpope/vim-endwise
[YouCompleteMe]: https://github.com/ycm-core/YouCompleteMe/wiki/Building-Vim-from-source
