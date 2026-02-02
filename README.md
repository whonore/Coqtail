# Coqtail

[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/ambv/black)
[![Vim Tests](https://github.com/whonore/Coqtail/actions/workflows/vim-tests.yml/badge.svg?branch=main)](https://github.com/whonore/Coqtail/actions/workflows/vim-tests.yml)
[![Python Tests](https://github.com/whonore/Coqtail/actions/workflows/python-tests.yml/badge.svg?branch=main)](https://github.com/whonore/Coqtail/actions/workflows/python-tests.yml)
[![Rocq Tests](https://github.com/whonore/Coqtail/actions/workflows/coq-tests.yml/badge.svg?branch=main)](https://github.com/whonore/Coqtail/actions/workflows/coq-tests.yml)

## Interactive Rocq Proofs in Vim

Coqtail enables interactive Rocq (née Coq) proof development in Vim similar to
[RocqIDE] or [ProofGeneral].

It supports:
- [Rocq 8.4 - 9.1]
- Python >=3.6 (see [here](#python-2-support) for older versions)
- Vim >=7.4 and Neovim >=0.3
- Simultaneous Rocq sessions in different buffers
- Non-blocking communication between Vim and Rocq (Vim >=8.0 and NeoVim only)

## Installation

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

### Requirements

- Vim compiled with `+python3` (3.6 or later) or the `pynvim` Python package for Neovim
- Vim configuration options `filetype plugin on`, and optionally `filetype
  indent on` and `syntax on` (e.g. in `.vimrc`)
- [Rocq 8.4 - 9.1]

Newer versions of Rocq have not yet been tested, but should still work as long
as there are no major changes made to the [XML protocol].
Note that for Rocq >=8.9, the `coqidetop` executable must be available, which
may require additionally installing RocqIDE depending on the installation method.
See [here](#rocq-executable) for help with pointing Coqtail to the appropriate location.

## Usage

Coqtail provides the following commands and mappings, which are available in any
buffer with the `coq` filetype (set automatically for files with a `.v`
extension, or manually with `:setfiletype coq`).
All commands with a `Rocq` prefix also have an alias beginning with `Coq`.
See `:help coqtail` for more details.

| Command | Mapping | Description |
|---|---|---|
| **Starting and Stopping** | |
| `RocqStart` | `<leader>cc` | Launch Coqtail in the current buffer. |
| `RocqStop` | `<leader>cq` | Quit Coqtail in the current buffer. |
| `RocqInterrupt` | `CTRL-C` | Send SIGINT to Rocq. |
| **Movement** | |
| `{n}RocqNext` | `<leader>cj` | Send the next `n` (1 by default) sentences to Rocq. |
| `{n}RocqUndo` | `<leader>ck` | Step back `n` (1 by default) sentences. |
| `{n}RocqToLine` | `<leader>cl` | Send/rewind all sentences up to line `n` (cursor position by default). `n` can also be `$` to check the entire buffer. |
| `{n}RocqOmitToLine` | No default (see [Mappings](#mappings)) | Same as `RocqToLine`, but skip processing of and admit all opaque proofs. Similar to Proof General's [`proof-omit-proofs-option`](https://proofgeneral.github.io/doc/master/userman/Coq-Proof-General/#Omitting-proofs-for-speed). See `:help RocqOmitToLine` for more information. |
| `RocqToTop` | `<leader>cT` | Rewind to the beginning of the file. |
| `RocqJumpToEnd` | `<leader>cG` | Move the cursor to the end of the checked region. |
| `RocqJumpToError` | `<leader>cE` | Move the cursor to the start of the error region. |
| `RocqGotoDef[!] <arg>` | `<leader>cgd` | Populate the quickfix list with possible locations of the definition of `<arg>` and try to jump to the first one. If your Vim supports `'tagfunc'` you can also use `CTRL-]`, `:tag`, and friends. |
| **Queries** | |
| `Rocq <args>` | | Send arbitrary queries to Rocq (e.g. `Check`, `About`, `Print`, etc.). |
| `Rocq Check <arg>` | `<leader>ch` | Show the type of `<arg>` (the mapping will use the term under the cursor or the highlighted range in visual mode). |
| `Rocq About <arg>` | `<leader>ca` | Show information about `<arg>`. |
| `Rocq Print <arg>` | `<leader>cp` | Show the definition of `<arg>`. |
| `Rocq Locate <arg>` | `<leader>cf` | Show where `<arg>` is defined. |
| `Rocq Search <args>` | `<leader>cs` | Show theorems about `<args>`. |
| **Panel Management** | |
| `RocqRestorePanels` | `<leader>cr` | Re-open the Goal and Info panels. |
| `{n}RocqGotoGoal` | `<leader>cgg` | Scroll the Goal panel to the start of the `n`th goal (defaults to 1). Number of lines shown is controlled by `g:coqtail_goal_lines`. |
| `{n}RocqGotoGoal!` | `<leader>cgG` | Scroll the Goal panel to the end of the `n`th goal. |
| `RocqGotoGoalNext` | `]g` | Scroll the Goal panel to the start of the next goal. |
| `RocqGotoGoalNext!` | `]G` | Scroll the Goal panel to the end of the next goal. |
| `RocqGotoGoalPrev` | `[g` | Scroll the Goal panel to the start of the previous goal. |
| `RocqGotoGoalPrev!` | `[G` | Scroll the Goal panel to the end of the previous goal. |

## Configuration

### Mappings

The mappings above are set by default, but you can disable them all and define
your own by setting `g:coqtail_nomap = 1` in your `.vimrc`.
Some of the commands, such as `RocqNext`, also have insert-mode mappings by
default, which can be disabled with `g:coqtail_noimap`.

Alternatively, you can keep the defaults but remap specific commands.
For example, use `map <leader>ci <Plug>RocqInterrupt` to avoid hijacking `CTRL-C`.
If a mapping for a command already exists when Coqtail is loaded, the default
mapping for that command won't be defined.

The `<leader>c` prefix may be inconvenient depending on your `mapleader` setting.
In that case you can set a custom prefix with `g:coqtail_map_prefix` (or
`g:coqtail_imap_prefix` for just insert-mode mappings).

Finally, after defining the standard keybindings, Coqtail will call a vim
function named `CoqtailHookDefineMappings` (if one is defined). This makes it
easy to add additional mappings without removing the standard mappings, and
to add mappings which are only active in Coqtail-managed buffers. One way to
use this hook is to make bindings for commands which augment the standard
Coqtail bindings instead of replacing them. One concrete example is:

```vim
function CoqtailHookDefineMappings()
  imap <buffer> <S-Down> <Plug>RocqNext
  imap <buffer> <S-Left> <Plug>RocqToLine
  imap <buffer> <S-Up> <Plug>RocqUndo
  nmap <buffer> <S-Down> <Plug>RocqNext
  nmap <buffer> <S-Left> <Plug>RocqToLine
  nmap <buffer> <S-Up> <Plug>RocqUndo
endfunction
```

Adding that snippet to your `.vimrc` would create new bindings for `RocqNext`,
`RocqToLine`, and `RocqUndo`.
Those bindings would be active in all Rocq buffers, including Coqtail panels,
but inactive in other buffers.
The standard Coqtail bindings (`<leader>cj`, etc) would remain active.

### Rocq Executable

By default Coqtail uses the first `coq(ide)top(.opt)` found in your `PATH`.
Use `b:coqtail_coq_path` (or `g:coqtail_coq_path`) to specify a different
directory to search in (these are automatically set if the `$COQBIN` environment
variable is set).
You can also override the name of the Rocq executable to use with
`b:coqtail_coq_prog` (or `g:coqtail_coq_prog`).
For example, to use the [HoTT library](https://github.com/HoTT/HoTT):

```vim
let b:coqtail_coq_path = '/path/to/HoTT'
let b:coqtail_coq_prog = 'hoqidetop'
```

### Project Files

There are two standard methods for configuring Rocq project settings:
[`_CoqProject` files](https://rocq-prover.org/doc/master/refman/practical-tools/utilities.html#building-a-project-with-coqproject-overview),
and
[dune projects](https://rocq-prover.org/doc/master/refman/practical-tools/utilities.html#building-a-rocq-project-with-dune).
Coqtail supports both, and while it should usually do the right thing by
default, its behavior can be controlled by setting the `g:coqtail_build_system`
option to one of `'prefer-dune'` (default), `'prefer-coqproject'`, `'dune'`, or
`'coqproject'`.
Additional arguments can also be passed to the Rocq executable through
`:RocqStart` (e.g., `:RocqStart -w all`).

#### Dune Settings

Dune projects can be configured to automatically compile the dependencies for
the current file on `:RocqStart` by setting `g:coqtail_dune_compile_deps = 1`.

#### _CoqProject Settings

By default, Coqtail searches the current and parent directories for a
`_CoqProject` or `_RocqProject` file, but additional or different project files can be specified
with `g:coqtail_project_names`.
If multiple files are found, their argument lists will be concatenated.
For example, to include arguments from both `_CoqProject` and `_CoqProject.local`:

```vim
let g:coqtail_project_names = ['_CoqProject', '_CoqProject.local']
```

### Syntax Highlighting and Indentation

Coqtail also comes with an ftdetect script for Rocq, as well as modified
versions of Vincent Aravantinos' [syntax] and [indent] scripts for Rocq.
These scripts are used by default but can be disabled by setting
`g:coqtail_nosyntax = 1` and `g:coqtail_noindent = 1` respectively.
Formatting of comments can be disabled with `g:coqtail_noindent_comment`.

In addition to the Rocq syntax, Coqtail defines highlighting groups for the
sentences that are currently or have already been checked by Rocq (`CoqtailSent`
and `CoqtailChecked`), any lines that raised an error (`CoqtailError`), and the
beginnings and ends of omitted proofs (`CoqtailOmitted`).
By default these are defined as:

```vim
if &t_Co > 16
  if &background ==# 'dark'
    hi def CoqtailChecked ctermbg=17 guibg=#113311
    hi def CoqtailSent ctermbg=60 guibg=#007630
  else
    hi def CoqtailChecked ctermbg=157 guibg=LightGreen
    hi def CoqtailSent ctermbg=40 guibg=LimeGreen
  endif
else
  hi def CoqtailChecked ctermbg=4 guibg=LightGreen
  hi def CoqtailSent ctermbg=7 guibg=LimeGreen
endif
hi def link CoqtailError Error
hi def link CoqtailOmitted coqProofAdmit
```

To override these defaults simply set your own highlighting (`:help :hi`) before
`syntax/coq.vim` is sourced (e.g., in your `.vimrc`).
Note, however, that many colorschemes call `syntax clear`, which clears
user-defined highlighting, so it is recommended to place your settings in a
`ColorScheme` autocommand.
For example:

```vim
augroup CoqtailHighlight
  autocmd!
  autocmd ColorScheme *
    \  hi def CoqtailChecked ctermbg=236
    \| hi def CoqtailSent    ctermbg=237
augroup END
```

If you feel distracted by the error highlighting while editing a failed
sentence, you can use the sequence `<leader>cl` (`:RocqToLine`) while the cursor
is inside that sentence.
If it isn't, you can use `<leader>cE` (`:RocqJumpToError`) to move it to an
appropriate position.

### Proof Diffs

Since 8.9, Rocq can generate [proof diffs] to highlight the differences in the
proof context between successive steps.
To enable proof diffs manually, use `:Rocq Set Diffs "on"` or `:Rocq Set Diffs
"removed"`.
To automatically enable proof diffs on every `:RocqStart`, set
`g:coqtail_auto_set_proof_diffs = 'on'` (or `= 'removed'`).
By default, Coqtail highlights these diffs as follows:

```vim
hi def link CoqtailDiffAdded DiffText
hi def link CoqtailDiffAddedBg DiffChange
hi def link CoqtailDiffRemoved DiffDelete
hi def link CoqtailDiffRemovedBg DiffDelete
```

See the [above instructions](#syntax-highlighting-and-indentation) on how to
override these defaults.

### More Options

See `:help coqtail-configuration` for a description of all the configuration options.

## Vim Plugin Interoperability

### Jumping between matches

Coqtail defines `b:match_words` patterns to support jumping between matched text
with `%` using the [matchup] or [matchit] plugins.

### Automatically closing blocks

Coqtail defines patterns to enable automatic insertion of the appropriate `End`
command for code blocks such as `Section`s, `Module`s, and `match` expressions
with [endwise].

### Tags

Coqtail supports the `:tag` family of commands by locating a term on the fly
with `tagfunc`.
However, as this relies on Rocq's `Locate` command, it only works if the point
where the term is defined has already been evaluated by Rocq.
An alternative is to disable Coqtail's default `tagfunc` (`let g:coqtail_tagfunc
= 0`) and instead use [universal-ctags] in conjunction with [coq.ctags], to
statically generate a `tags` file.
This works especially well with something like the [gutentags] plugin to
automatically keep the `tags` file in sync with the Rocq source.

### Latex/Unicode input

Coqtail and Rocq can handle non-ASCII characters in identifiers, notations,
etc., but Coqtail does not provide a method for inputting these characters itself.
Instead one can use one of the native Vim options (e.g.,
[`i_CTRL-K`](https://vimhelp.org/insert.txt.html#i_CTRL-K) or
[`i_CTRL-V_digit`](https://vimhelp.org/insert.txt.html#i_CTRL-V_digit)) or a
plugin like [latex-unicoder] or [unicode.vim].

## Thanks

Parts of Coqtail were originally inspired by/adapted from [Coquille] (MIT
License, Copyright (c) 2013, Thomas Refis).

---

#### Python 2 Support

Python 2 and 3.5 have reached their [end-of-life](https://pythonclock.org/) so
Coqtail no longer supports them in order to simplify the code and take advantage
of newer features.
See [YouCompleteMe] for help building Vim with Python 3 support.
If you cannot upgrade Vim, the [python2] branch still supports older Pythons.

[python2]: https://github.com/whonore/Coqtail/tree/python2
[Rocq 8.4 - 9.1]: https://rocq-prover.org/install
[RocqIDE]: https://rocq-prover.org/doc/master/refman/practical-tools/coqide.html
[ProofGeneral]: https://proofgeneral.github.io/
[XML protocol]: https://github.com/coq/coq/blob/master/dev/doc/xml-protocol.md
[vim package]: https://vimhelp.org/repeat.txt.html#packages
[pathogen]: https://github.com/tpope/vim-pathogen
[Vundle]: https://github.com/VundleVim/Vundle.vim
[VimPlug]: https://github.com/junegunn/vim-plug
[syntax]: http://www.vim.org/scripts/script.php?script_id=2063
[indent]: http://www.vim.org/scripts/script.php?script_id=2079
[matchup]: https://github.com/andymass/vim-matchup
[matchit]: http://ftp.vim.org/pub/vim/runtime/macros/matchit.txt
[endwise]: https://github.com/tpope/vim-endwise
[proof diffs]: https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/proof-mode.html#coq:opt.Diffs
[Coquille]: https://github.com/the-lambda-church/coquille
[YouCompleteMe]: https://github.com/ycm-core/YouCompleteMe/wiki/Building-Vim-from-source
[universal-ctags]: https://github.com/universal-ctags/ctags
[coq.ctags]: https://github.com/tomtomjhj/coq.ctags
[gutentags]: https://github.com/ludovicchabant/vim-gutentags
[latex-unicoder]: https://github.com/joom/latex-unicoder.vim
[unicode.vim]: https://github.com/chrisbra/unicode.vim
