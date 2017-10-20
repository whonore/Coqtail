# Coqtail
## A Vim Plugin for Interactive Theorem Proving in Coq

Coqtail is a rewrite of [Coquille](https://github.com/the-lambda-church/coquille).
The main improvements are better support for editing multiple files simultaneously,
and support for both Python 2 and 3.

Installation and Requirements
----------------
Coqtail can be installed using [pathogen](https://github.com/tpope/vim-pathogen).
Follow the setup instructions and then:

    cd ~/.vim/bundle && git clone https://github.com/whonore/Coqtail.git

Coqtail requires:
- vim compiled with either +python or +python3
- [vimbufsync](https://github.com/let-def/vimbufsync)
- [Coq 8.6](https://coq.inria.fr/coq-86) (support for 8.7 (and maybe 8.5) coming soon)

Usage
---
Coqtail provides the following commands:
- CoqStart - Launches Coq
- CoqStop - Quits Coq
- CoqNext - Submits the next line to Coq for checking
- CoqUndo - Steps back
- CoqToCursor - Submits all lines up to the cursor
- CoqToTop - Resets the checked part to the beginning of the file
- Coq \<arg> - Sends arbitrary commands to Coq (such as Check, About, Print, etc)
- JumpToEnd - Moves the cursor to the end of the checked region
- FindDef - Searches the LoadPath for the definition of the word under the cursor and
opens it in another file if possible

Coqtail does not set any mappings by default but provides some in the function `coqtail#Mapping()`,
which could be called in your .vimrc.

Coqtail also comes with an ftdetect script for Coq, as well as Vincent Aravantinos'
[syntax](http://www.vim.org/scripts/script.php?script_id=2063) and
[index](http://www.vim.org/scripts/script.php?script_id=2079) scripts for Coq.
