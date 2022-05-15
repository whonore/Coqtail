# Change Log

## Unreleased ([master])

### Fixed
- Incorrect parsing of bracketed goal selectors (`2:{`) with newlines.
  (PR #292)

## [1.6.3]

### Added
- Support for Elpi syntax highlighting and parsing inside `lp:{{ ... }}` blocks.
  (PR #278)
- `g:coqtail_tagfunc` option to enable/disable Coqtail's default `tagfunc`.
  (PR #272)
- Support for Coq 8.15.
  (PR #266)

### Fixed
- Incorrect highlighting of identifiers containing "exists" or "error".
  (PR #291)
- Highlight more query commands.
  (PR #291)
- Highlight `Typeclasses Opaque/Transparent`.
  (PR #286)
- Strip trailing whitespace from the splash screen to make it less ugly when
  `list` + `listchars=trail:` is set.
  (PR #284)
- Catch and report long warnings from Coqtop that line wrap (`Warning:\n`
  instead of `Warning: `) instead of aborting.
  (PR #274)
- Broken highlighting and indentation after `Fail Next Obligation`.
  (PR #268)
- Highlight many more tactics.
  (PR #269)

## [1.6.2]

### Added
- `g:coqtail_update_tagstack` option to update the tagstack on `:CoqGotoDef`
  (enabled by default).
  (PR #175)

### Fixed
- Avoid clearing the Info buffer when `:CoqToLine` advances 0 sentences.
  (PR #261)
- Suppress spurious `TextYankPost` autocmd while getting text selected in Visual mode.
  (PR #260)
- Avoid manually calling `redraw` in NeoVim.
  (PR #260)

## [1.6.1]

### Added
- Code folding for Sections, Modules, and Theorems.
  (PR #242)
- `g:coqtail_inductive_shift` option to control indentation of Inductive
  constructor branches.
  (PR #248)

### Fixed
- Highlight `Number Notation` and `Declare Custom Entry`.
  (PR #243)
- Crash with `Implicit Type (x : ...)`.
  (PR #253)
- Universe levels inconsistent with those shown by `coqc`.
  (PR #253)
- Indent the line after `Proof using` correctly.
  (PR #255)
- Crash when output contains unprintable characters.
  (PR #256)

## [1.6.0]

### Added
- `g:coqtail_version_compat` option to re-enable old behaviors after breaking changes.
  (PR #238)

### Fixed
- Change ambiguous default mappings to remove delay.
  **BREAKING**: The default mappings have changed for for `<Plug>CoqGotoDef`
  (`<leader>cg` -> `<leader>cgd`), `<Plug>CoqGotoGoalEnd` (`<leader>cGG` ->
  `<leader>cgG`), `<Plug>CoqGotoGoalNextStart` (`g]` -> `]g`),
  `<Plug>CoqGotoGoalNextEnd` (`G]` -> `]G`), `<Plug>CoqGotoGoalPrevStart` (`g[`
  -> `[g`), and `<Plug>CoqGotoGoalPrevEnd` (`G[` -> `[G`).
  Set `g:coqtail_version_compat = ['1.5']` to enable the old mappings, or see
  the [README](README.md#mappings) for help changing these defaults.
  (PR #238)

## [1.5.2]

### Added
- Preliminary support for Coq 8.15.
  (PR #209)
- Support for Coq 8.14.
  (PRs #211, #213, #240)

## [1.5.1]

### Fixed
- Recognize `.` followed by a tab as a sentence ending.
  (PR #234)
- Don't abort if only warnings are printed to `stderr`.
  Include Coqtop `stderr` in the error message for `coqtail#start`.
  (PR #226)

## [1.5.0]

### Added
- `g:coqtail_coq_path` defaults to `$COQBIN` if it is set.
  (PR #219)

### Fixed
- Jumping to a definition with `:CoqGotoDef` or `:tag` commands works correctly
  with identifiers that include `'` (a single quote).
  (PR #218)
- Coqtail chooses which `coq(ide)top(.opt)` to use in a more predictable way.
  It uses `$PATH` (or `g:coqtail_coq_path` if it is set) to find `coqc` (or
  `g:coqtail_coq_prog` if it is set) and check its version.
  It then looks for `coqtop` or `coqidetop` (or `g:coqtail_coq_path`) as
  appropriate in the same directory as `coqc`, taking possible prefixes (e.g.,
  `coq-prover.`) and extensions (e.g., `.opt`) into account.
  **BREAKING**: If you have multiple versions of Coq installed Coqtail may
  choose a different one than before.
  In particular, executables in the current directory are no longer considered
  by default.
  Set `g:coqtail_coq_path` explicitly if you rely on this behavior.
  (PR #216)

## [1.4.1]

### Added
- Spell checking in comments.
  (PR #215)

### Fixed
- Return when Coqtop prints to `stderr` instead of waiting on `stdout` indefinitely.
  (PR #214)
- Use case-sensitive search in indent function.
  (PR #210)
- Use `win_execute` when possible while refreshing highlighting to avoid
  changing windows, which broke certain plugins.
  (PR #208)
- Highlight `Existing Instances`.
  (PR #207)
- Detect when Coqtop crashes on `:CoqStart` and print the error message instead
  of hanging.
  (PR #205)
- Work around a NeoVim bug with `py3eval` that caused Coqtail to incorrectly
  detect a lack of Python 3 support.
  (PR #204)
- Display the "Requires Python 3" warning message even if `shortmess+=F` is set.
  (PR #204)

## [1.4.0]

### Removed
- Support for Python <3.6.
  See [YouCompleteMe] for help with building Vim with Python 3 support.
  If you are unable to upgrade to Python 3, use the [python2] branch.
  Nearly all of the changes to the code are internal cleanup so there should be
  no observable changes in behavior.
  Please [open an issue] to report any regressions.
  See [here](https://github.com/whonore/Coqtail/issues/159) for the full list of
  changes.
  (PR #188)

## [1.3.1]

### Added
- `:CoqJumpToError` command that moves the cursor to the location of the error
  reported by Coq, if any.
  (PR #196)

### Fixed
- Use `deletebufline` instead of `:delete` when possible to avoid leaving visual
  mode while updating the Goal and Info panels.
  (PR #198)
- Correctly ignore `(*` and `*)` inside strings.
  (PR #193)
- Print Coq error messages when checking goals or rewinding.
  (PR #187)
- Highlight `Module Import` and `Module Export`.
  (PRs #195, #202)
- Improve highlighting inside sections and modules.
  (PR #191)
- Correctly highlight `..` in recursive notations.
  (PR #190)
- Highlight attributes and skip them when splitting sentences.
  (PR #152)
- Highlight `admit` and `give_up` tactics.
  (PR #182)
- Match non-ASCII letters in identifier syntax highlighting.
  (PR #184)
- Improve syntax highlighting of binders in definitions, theorems, etc.
  (PR #185)

## [1.3.0]

### Added
- Support for highlighting proof diffs.
  `g:coqtail_auto_set_proof_diffs` can be used to automatically enable diffs on
  `:CoqStart`.
  (PR #169)
- Support for Coq 8.13.
  (PR #181)
- Support for Coq installed through Snap by checking for the `coq-prover.`
  prefix as a fallback when looking for `coqidetop`.
  (PR #180)
- Support for multiple `_CoqProject` files.
  **BREAKING**: renamed `g:coqtail_project_name` to `g:coqtail_project_names`
  and `b:coqtail_project_file` to `b:coqtail_project_files`.
  (PR #141)
- Match CoqIDE behavior and set the top-level module name based on the file name
  with `-topfile` (Coq >=8.10 only).
  (PR #145)
- Improved comment autoformatting.
  Disable with `g:coqtail_noindent_comment`.
  (PR #146)
- Debugging can be enabled with `:CoqToggleDebug` without calling `:CoqStart`.
  (PR #148)

### Fixed
- Correctly handle highlighting of multibyte characters (for real this time).
  (PR #177)
- Preserve jumplist and alternate file when opening Info and Goal panels.
  (PR #150)
- Don't list Info and Goal panel buffers.
  (PR #151)
- Catch exception in `CoqtailServer` when the connection is reset by the peer.
  (PR #155)
- Remember the cursor position in the jumplist before moving it with `:CoqJumpToEnd`.
  (PR #173)
- Various syntax highlighting improvements including basic support for Ltac2.
  (PRs #139, #143, #149, #153, #156, #172)

### Removed
- Dependency on `distutils` if `shutil.which` is available (Python >=3.3).
  (PR #161)

## [1.2.0]

### Added
- Support for Coq 8.12.
  (PR #120)
- `g:coqtail_noimap`, `g:coqtail_map_prefix`, `g:coqtail_imap_prefix`
  configuration options to control insert-mode mappings.
  (PR #122)
- Mappings for query commands (`<leader>cs`, `<leader>ch`, etc) now work on the
  highlighted range in Visual mode.
  (PR #131)
- Commands and mappings now work when called in the Goal and Info panels.
  (PR #132)

### Fixed
- `g:coqtail_coq_path` is now checked on `:CoqStart` instead of on buffer load.
  (PR #123)
- `:CoqStart` no longer fails when the Coq executable is in the current directory.
  (PR #123)
- Various syntax highlighting/indentation improvements.
  (PRs #124, #126, #127)
- No longer crash when checking Coq version if `coqtop.opt` does not exist.
  (PR #129)
- No longer crash on `:CoqStart` when a buffer has no associated file.
  (PR #137)
- Improved interrupt-handling logic, which should reduce the frequency of the
  case where pending commands are not cleared and `nomodifiable` is set after
  every command.
  (PR #130)

## [1.1.0]

### Added
- Support for NeoVim >=0.3.
  (PR #103)
- `b:coqtail_coq_prog`/`g:coqtail_coq_prog` configuration option to override the
  name of the Coq executable.
  (PR #119)

### Fixed
- Lowered priority of Coqtail-related highlighting (`CoqtailChecked`,
  `CoqtailSent`, `CoqtailError`) so they don't cover existing highlighting, e.g.
  from `'hlsearch'`.
  (PR #104)
- Only call `coqtail#stop` on `:quit` if it would close the last visible
  instance of the buffer.
  (PR #105)
- Coqtail highlighting correctly handles multibyte characters.
  (PR #109)
- All pending sentences waiting to be checked by Coq (`CoqtailSent`) are
  highlighted instead of just the next one.
  (PR #109)
- `:Coq` and `:CoqGotoDef` do not treat arguments containing `"` as comments by
  removing `-bar` option.
  (PR #111)
- Respect the `$PATH` order when choosing between `coq(ide)top` and `coq(ide)top.opt`.
  (PR #114)
- No longer crash ("E803: ID not found") after `:split`ting the main Coq window.
  (PR #118)

## [1.0.0]

### Added
- Non-blocking communication with Coq using the `+channel` feature (Vim >=8.0 only).
- A synchronous fallback for Vim 7.4.
- `CoqInterrupt` command that forwards `SIGINT` to the Coq process.
- `CoqRestorePanels` command that re-opens the Goal and Info panels in their
  original positions.
- This changelog.
  Begin using semantic (more or less) versioning.

### Removed
- Dependency on `vim` module in Python code.
- Dependency on [vimbufsync].
- `CoqMakeMatch` command.
  It wasn't well thought out and didn't seem very useful.
  Please [open an issue] if you'd like it to be re-added.

### Fixed
- Commands no longer crash when called while Goal or Info panels are closed.

### Deprecated
- Python 2 support.
  See [YouCompleteMe] for help building Vim with Python 3 support.

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
[python2]: https://github.com/whonore/Coqtail/tree/python2
[1.6.3]: https://github.com/whonore/Coqtail/tree/v1.6.3
[1.6.2]: https://github.com/whonore/Coqtail/tree/v1.6.2
[1.6.1]: https://github.com/whonore/Coqtail/tree/v1.6.1
[1.6.0]: https://github.com/whonore/Coqtail/tree/v1.6.0
[1.5.2]: https://github.com/whonore/Coqtail/tree/v1.5.2
[1.5.1]: https://github.com/whonore/Coqtail/tree/v1.5.1
[1.5.0]: https://github.com/whonore/Coqtail/tree/v1.5.0
[1.4.1]: https://github.com/whonore/Coqtail/tree/v1.4.1
[1.4.0]: https://github.com/whonore/Coqtail/tree/v1.4.0
[1.3.1]: https://github.com/whonore/Coqtail/tree/v1.3.1
[1.3.0]: https://github.com/whonore/Coqtail/tree/v1.3.0
[1.2.0]: https://github.com/whonore/Coqtail/tree/v1.2.0
[1.1.0]: https://github.com/whonore/Coqtail/tree/v1.1.0
[1.0.0]: https://github.com/whonore/Coqtail/tree/v1.0.0
[pre-1.0]: https://github.com/whonore/Coqtail/tree/pre-1.0
[open an issue]: https://github.com/whonore/Coqtail/issues
[vimbufsync]: https://github.com/let-def/vimbufsync
[matchup]: https://github.com/andymass/vim-matchup
[endwise]: https://github.com/tpope/vim-endwise
[YouCompleteMe]: https://github.com/ycm-core/YouCompleteMe/wiki/Building-Vim-from-source
