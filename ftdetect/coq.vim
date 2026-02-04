" Default to coq when editing a file that doesn't exists
au BufNewFile *.v set filetype=coq

" Rely on filetype detection for existing files except in old verions of Vim
if !has('patch-9.0.1478')
  au BufRead *.v set filetype=coq
endif
