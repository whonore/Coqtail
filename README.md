# Coqtail

[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/ambv/black)
[![Build Status](https://travis-ci.com/whonore/Coqtail.svg?branch=master)](https://travis-ci.com/whonore/Coqtail)

## Interactive Coq Proofs in Vim

Coqtail enables interactive Coq proof development in Vim similar to
[CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html)
or [ProofGeneral](https://proofgeneral.github.io/).

It supports:
- [Coq 8.4 - 8.11](https://coq.inria.fr/download)
- Python 2<sup>[1](#python2)</sup> and 3
- Vim 7.4 - 8.2
- Multiple Coq sessions in different buffers

## Installation and Requirements

As a
[vim package](https://vimhelp.org/repeat.txt.html#packages):
```sh
mkdir -p ~/.vim/pack/coq/start
git clone https://github.com/let-def/vimbufsync.git ~/.vim/pack/coq/start/vimbufsync
git clone https://github.com/whonore/Coqtail.git ~/.vim/pack/coq/start/Coqtail
vim +helptags\ ~/.vim/pack/coq/start/Coqtail/doc +q
```

Using
[pathogen](https://github.com/tpope/vim-pathogen):
```sh
git clone https://github.com/let-def/vimbufsync.git ~/.vim/bundle/vimbufsync
git clone https://github.com/whonore/Coqtail.git ~/.vim/bundle/Coqtail
vim +Helptags +q
```

Using
[Vundle](https://github.com/VundleVim/Vundle.vim):
```sh
Plugin 'whonore/Coqtail' | Plugin 'let-def/vimbufsync' (add this line in .vimrc)
vim +PluginInstall +qa
```

Using
[VimPlug](https://github.com/junegunn/vim-plug):
```sh
Plug 'whonore/Coqtail' | Plug 'let-def/vimbufsync' (add this line in .vimrc)
vim +PlugInstall +qa
```

Requirements:
- Vim compiled with either `+python`<sup>[1](#python2)</sup> or `+python3`
- For syntax highlighting, Vim configuration options `filetype plugin indent on` and `syntax on` (e.g. in `.vimrc`)
- [Coq 8.4 - 8.11](https://coq.inria.fr/download)

Newer versions of Coq have not yet been tested, but should still work as long as
there are no major changes made to the XML protocol Coqtail uses to communicate
with `coqtop`.

## Usage

Coqtail provides the following commands (see `:help coqtail` for more details):

| Command | Mapping | Description |
|---|---|---|
| **Starting and Stopping** | |
| `CoqStart` | `<leader>cc` | Launch Coqtail for the current buffer. |
| `CoqStop` | `<leader>cq` | Quit Coqtail for the current buffer. |
| `CoqInterrupt` | `CTRL-C` | Send SIGINT to `coqtop`. |
| **Movement** | |
| `{n}CoqNext` | `<leader>cj` | Check the next `n` (1 by default) sentences with Coq. |
| `{n}CoqUndo` | `<leader>ck` | Step back `n` (1 by default) sentences. |
| `{n}CoqToLine` | `<leader>cl` | Check/rewind all sentences up to line `n` (cursor position by default). `n` can also be `$` to check the entire buffer.|
| `CoqToTop` | `<leader>cT` | Rewind to the beginning of the file. Similar to `1CoqToLine`, but `CoqToLine` only rewinds to the end of the line. |
| `CoqJumpToEnd` | `<leader>cG` | Move the cursor to the end of the checked region. |
| `CoqGotoDef[!] <arg>` | `<leader>cg` | Populate the quickfix list with possible locations of the definition of `<arg>` and try to jump to the first one. If your Vim supports `'tagfunc'` you can just use `CTRL-]`, `:tag`, and friends instead. |
| **Queries** | |
| `Coq <args>` | | Send arbitrary queries to Coq (e.g. `Check`, `About`, `Print`, etc.). |
| `Coq Check <arg>` | `<leader>ch` | Show the type of `<arg>` (the mapping will use the term under the cursor). |
| `Coq About <arg>` | `<leader>ca` | Show information about `<arg>`. |
| `Coq Print <arg>` | `<leader>cp` | Show the definition of `<arg>`. |
| `Coq Locate <arg>` | `<leader>cf` | Show where `<arg>` is defined. |
| `Coq Search <args>` | `<leader>cs` | Show theorems about `<args>`. |
| **Panel Management** | |
| `CoqRestorePanels` | `<leader>cr` | Re-open the goal and info panels. |
| `{n}CoqGotoGoal` | `<leader>cgg` | Scroll the goal panel to the start of the `n`th goal (defaults to 1). Number of lines shown is controlled by `g:coqtail_goal_lines`. |
| `{n}CoqGotoGoal!` | `<leader>cGG` | Scroll the goal panel to the end of the `n`th goal. |
| `CoqGotoGoalNext` | `g]` | Scroll the goal panel to the start of the next goal. |
| `CoqGotoGoalNext!` | `G]` | Scroll the goal panel to the end of the next goal. |
| `CoqGotoGoalPrev` | `g[` | Scroll the goal panel to the start of the previous goal. |
| `CoqGotoGoalPrev!` | `G[` | Scroll the goal panel to the end of the previous goal. |


## Configuration

The mappings shown above are set by default, but you can disable them all and
define your own by setting `g:coqtail_nomap = 1` in your `.vimrc`.
Alternatively, you can remap specific commands and the defaults will still be
used for the rest.
For example, set `map <leader>ci <Plug>CoqInterrupt` in your `.vimrc` to not
hijack `CTRL-C`.

By default Coqtail will use the `coqtop` or `coqtop.opt` on your `PATH`.
You can tell it to search instead in a specific directory by setting
`b:coqtail_coq_path` before calling `CoqStart`. To set this option globally use
`g:coqtail_coq_path`.

Coqtail also comes with an ftdetect script for Coq, as well as modified
versions of Vincent Aravantinos'
[syntax](http://www.vim.org/scripts/script.php?script_id=2063) and
[indent](http://www.vim.org/scripts/script.php?script_id=2079) scripts for Coq.
These scripts are used by default but can be disabled by setting
`g:coqtail_nosyntax = 1` and `g:coqtail_noindent = 1` respectively.

## Interoperability

### Jumping between matches

Coqtail defines `b:match_words` patterns to support jumping between matched
text with `%` using the
[matchup](https://github.com/andymass/vim-matchup) or
[matchit](http://ftp.vim.org/pub/vim/runtime/macros/matchit.txt) plugins.

### Automatically closing blocks

Coqtail defines patterns to enable automatic insertion of the appropriate
`End` command for code blocks such as `Section`s, `Module`s, and `match`
expressions with [endwise](https://github.com/tpope/vim-endwise).

## Thanks

Parts of Coqtail were originally inspired by/adapted from
[Coquille](https://github.com/the-lambda-church/coquille)
(MIT License, Copyright (c) 2013, Thomas Refis).

---

#### <a name="python2">Python 2 Support</a>
Because Python 2 has reached its [end-of-life](https://pythonclock.org/) and supporting it alongside Python 3 makes it difficult to improve and maintain the code, Coqtail will drop support for Python 2 in the near future. At that time a stable version will be tagged and all future versions will be Python 3-only.
