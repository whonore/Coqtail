" Author: Wolf Honore
" Python and Vim compatibility definitions.

" Vim compatibility.
let g:coqtail#compat#t_dict = type({})
let g:coqtail#compat#t_list = type([])
let g:coqtail#compat#nvim = has('nvim')
let g:coqtail#compat#has_channel = (has('channel') && has('patch-8.0.0001')) || g:coqtail#compat#nvim

" Python compatibility.
if has('python3')
  command! -nargs=1 Py py3 <args>
  function! coqtail#compat#pyeval(expr) abort
    return py3eval(a:expr)
  endfunction
elseif has('python')
  command! -nargs=1 Py py <args>
  function! coqtail#compat#pyeval(expr) abort
    return pyeval(a:expr)
  endfunction
endif

function! coqtail#compat#init(python_dir) abort
  if !exists('*coqtail#compat#pyeval')
    return 0
  endif

  " Add python directory to path so Python functions can be called.
  Py import sys, vim
  Py if not vim.eval('a:python_dir') in sys.path:
    \    sys.path.insert(0, vim.eval('a:python_dir'))
  return 1
endfunction
