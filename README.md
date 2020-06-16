# Coqtail

[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/ambv/black)
[![Build Status](https://travis-ci.com/whonore/Coqtail.svg?branch=master)](https://travis-ci.com/whonore/Coqtail)

## Interactive Coq Proofs in Vim

Coqtail enables interactive Coq proof development in Vim similar to [CoqIDE] or
[ProofGeneral].

It supports:
- [Coq 8.4 - 8.11]
- Python 2<sup>[1](#python2)</sup> and 3
- Vim >=7.4 (Neovim coming soon)
- Simultaneous Coq sessions in different buffers
- Non-blocking communication between Vim and Coq (Vim >=8.0 only)

## Installation and Requirements

As a [vim package]:
```sh
mkdir -p ~/.vim/pack/coq/start
git clone https://github.com/whonore/Coqtail.git ~/.vim/pack/coq/start/Coqtail
vim +helptags\ ~/.vim/pack/coq/start/Coqtail/doc +q
```

Using [pathogen]:
```sh
git clone https://github.com/whonore/Coqtail.git ~/.vim/bundle/Coqtail
vim +Helptags +q
```

Using [Vundle]:
```sh
Plugin 'whonore/Coqtail' (add this line in .vimrc)
vim +PluginInstall +qa
```

Using [VimPlug]:
```sh
Plug 'whonore/Coqtail' (add this line in .vimrc)
vim +PlugInstall +qa
```

Requirements:
- Vim compiled with either `+python`<sup>[1](#python2)</sup> or `+python3`
- Vim configuration options `filetype plugin on`, and optionally
  `filetype indent on` and `syntax on` (e.g. in `.vimrc`)
- [Coq 8.4 - 8.11]

Newer versions of Coq have not yet been tested, but should still work as long
as there are no major changes made to the XML protocol Coqtail uses to
communicate with `coqtop`.

## Usage

Coqtail provides the following commands (see `:help coqtail` for more details):

| Command | Mapping | Description |
|---|---|---|
| **Starting and Stopping** | |
| `CoqStart` | `<leader>cc` | Launch Coqtail in the current buffer. |
| `CoqStop` | `<leader>cq` | Quit Coqtail in the current buffer. |
| `CoqInterrupt` | `CTRL-C` | Send SIGINT to `coqtop`. |
| **Movement** | |
| `{n}CoqNext` | `<leader>cj` | Send the next `n` (1 by default) sentences to Coq. |
| `{n}CoqUndo` | `<leader>ck` | Step back `n` (1 by default) sentences. |
| `{n}CoqToLine` | `<leader>cl` | Send/rewind all sentences up to line `n` (cursor position by default). `n` can also be `$` to check the entire buffer. |
| `CoqToTop` | `<leader>cT` | Rewind to the beginning of the file. |
| `CoqJumpToEnd` | `<leader>cG` | Move the cursor to the end of the checked region. |
| `CoqGotoDef[!] <arg>` | `<leader>cg` | Populate the quickfix list with possible locations of the definition of `<arg>` and try to jump to the first one. If your Vim supports `'tagfunc'` you can also use `CTRL-]`, `:tag`, and friends. |
| **Queries** | |
| `Coq <args>` | | Send arbitrary queries to Coq (e.g. `Check`, `About`, `Print`, etc.). |
| `Coq Check <arg>` | `<leader>ch` | Show the type of `<arg>` (the mapping will use the term under the cursor). |
| `Coq About <arg>` | `<leader>ca` | Show information about `<arg>`. |
| `Coq Print <arg>` | `<leader>cp` | Show the definition of `<arg>`. |
| `Coq Locate <arg>` | `<leader>cf` | Show where `<arg>` is defined. |
| `Coq Search <args>` | `<leader>cs` | Show theorems about `<args>`. |
| **Panel Management** | |
| `CoqRestorePanels` | `<leader>cr` | Re-open the Goal and Info panels. |
| `{n}CoqGotoGoal` | `<leader>cgg` | Scroll the Goal panel to the start of the `n`th goal (defaults to 1). Number of lines shown is controlled by `g:coqtail_goal_lines`. |
| `{n}CoqGotoGoal!` | `<leader>cGG` | Scroll the Goal panel to the end of the `n`th goal. |
| `CoqGotoGoalNext` | `g]` | Scroll the Goal panel to the start of the next goal. |
| `CoqGotoGoalNext!` | `G]` | Scroll the Goal panel to the end of the next goal. |
| `CoqGotoGoalPrev` | `g[` | Scroll the Goal panel to the start of the previous goal. |
| `CoqGotoGoalPrev!` | `G[` | Scroll the Goal panel to the end of the previous goal. |

## Configuration

The mappings above are set by default, but you can disable them all and define
your own by setting `g:coqtail_nomap = 1` in your `.vimrc`.
Alternatively, you can keep the defaults but remap specific commands.
For example, use `map <leader>ci <Plug>CoqInterrupt` to avoid hijacking `CTRL-C`.

By default Coqtail uses the `coq(ide)top(.opt)` found on your `PATH`.
You can tell it to instead search in a directory by setting
`b:coqtail_coq_path` before calling `CoqStart`.
Use `g:coqtail_coq_path` to set this option globally.

Coqtail also comes with an ftdetect script for Coq, as well as modified
versions of Vincent Aravantinos' [syntax] and [indent] scripts for Coq.
These scripts are used by default but can be disabled by setting
`g:coqtail_nosyntax = 1` and `g:coqtail_noindent = 1` respectively.

See `:help coqtail-configuration` for more configuration variables.

## Vim Plugin Interoperability

### Jumping between matches

Coqtail defines `b:match_words` patterns to support jumping between matched
text with `%` using the [matchup] or [matchit] plugins.

### Automatically closing blocks

Coqtail defines patterns to enable automatic insertion of the appropriate `End`
command for code blocks such as `Section`s, `Module`s, and `match` expressions
with [endwise].

## Thanks

Parts of Coqtail were originally inspired by/adapted from [Coquille] (MIT
License, Copyright (c) 2013, Thomas Refis).

---

#### <a name="python2">Python 2 Support</a>
Because Python 2 has reached its [end-of-life](https://pythonclock.org/) and
supporting it alongside Python 3 makes it difficult to improve and maintain the
code, Coqtail will drop support for Python 2 in the near future.
At that time a stable version will be tagged and all future versions will be
Python 3-only.
See [YouCompleteMe] for help building Vim with Python 3 support.

[Coq 8.4 - 8.11]: https://coq.inria.fr/download
[CoqIDE]: https://coq.inria.fr/refman/practical-tools/coqide.html
[ProofGeneral]: https://proofgeneral.github.io/
[vim package]: https://vimhelp.org/repeat.txt.html#packages
[pathogen]: https://github.com/tpope/vim-pathogen
[Vundle]: https://github.com/VundleVim/Vundle.vim
[VimPlug]: https://github.com/junegunn/vim-plug
[syntax]: http://www.vim.org/scripts/script.php?script_id=2063
[indent]: http://www.vim.org/scripts/script.php?script_id=2079
[matchup]: https://github.com/andymass/vim-matchup
[matchit]: http://ftp.vim.org/pub/vim/runtime/macros/matchit.txt
[endwise]: https://github.com/tpope/vim-endwise
[Coquille]: https://github.com/the-lambda-church/coquille
[YouCompleteMe]: https://github.com/ycm-core/YouCompleteMe/wiki/Building-Vim-from-source
