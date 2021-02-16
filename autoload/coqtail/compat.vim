" Author: Wolf Honore
" Python and Vim compatibility definitions.

" Vim compatibility.
let g:coqtail#compat#t_dict = type({})
let g:coqtail#compat#t_list = type([])
let g:coqtail#compat#nvim = has('nvim')
let g:coqtail#compat#has_channel = (has('channel') && has('patch-8.0.0001')) || g:coqtail#compat#nvim

" Use `deletebufline` when available because `:delete` forces vim to exit visual mode.
if exists('*deletebufline')
  function! coqtail#compat#deleteline(first, last) abort
    call deletebufline('%', a:first, a:last)
  endfunction
else
  function! coqtail#compat#deleteline(first, last) abort
    execute 'silent' a:first ',' a:last 'delete _'
  endfunction
endif

function! coqtail#compat#init(python_dir) abort
  if !(has('python3') && py3eval('sys.version_info[:2] >= (3, 6)'))
    return 0
  endif

  " Add python directory to path so Python functions can be called.
  py3 import vim
  py3 if not vim.eval('a:python_dir') in sys.path:
    \    sys.path.insert(0, vim.eval('a:python_dir'))
  return 1
endfunction
