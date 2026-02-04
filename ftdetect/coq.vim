" Use built-in filetype detection unless Vim doesn't support it or we are
" editing an empty file
au BufRead,BufNewFile *.v
      \ if !has('patch-9.0.1478') || (line('$') == 1 && getline(1) =~ '^\s*$')
      \ |   set filetype=coq
      \ | endif
