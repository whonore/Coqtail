# Change Log

## Unreleased [master]

## [1.0.0]

### Added
- Use '+channel' feature (Vim >=8.0 only) to enable asynchronous communication
  with Coq instead of blocking.
  See [README.md](https://github.com/whonore/Coqtail/blob/v1.0.0/README.md) for
  more information.
- Use a synchronous fallback for Vim 7.4.
- CoqInterrupt command that forwards SIGINT to the Coq process.
- CoqRestorePanel command that re-opens Goal and Info panels in their original
  positions.
- Changelog, begin using semantic (more or less) versioning.

### Changed
- No longer crash if Goal or Info panels are closed.
- Clean up and refactor Vim and Python scripts>

### Removed
- Dependency on `vim` Python module.
- Dependency on [vimbufsync].
- CoqMakeMatch command.
  It wasn't well thought out and didn't seem very useful.
  Please open an issue if you'd like it to be re-added.

### Fixed

## [pre-async]

### Added
- Support Vim >=7.4.
- Support Python 2 and 3.
- Support Coq 8.4-8.11.
- Interactive Coq proofs similar to CoqIDE/Proof General.
- Support multiple open Coq buffers simultaneously.
- Coq syntax highlighting.
- Coq automatic indentation.
- Interoperability with [matchup] and [endwise].

[master]: https://github.com/whonore/Coqtail
[1.0.0]: https://github.com/whonore/Coqtail/tree/v1.0.0
[pre-async]: https://github.com/whonore/Coqtail/tree/pre-async
[vimbufsync]: https://github.com/let-def/vimbufsync
[matchup]: https://github.com/andymass/vim-matchup
[endwise]: https://github.com/tpope/vim-endwise
