" Author: Wolf Honore
" Python and Vim compatibility definitions.

" Vim compatibility.
let g:coqtail#compat#t_dict = type({})
let g:coqtail#compat#t_list = type([])
let g:coqtail#compat#t_string = type('')
let g:coqtail#compat#nvim = has('nvim')
let g:coqtail#compat#has_channel = (has('channel') && has('patch-8.0.0001')) || g:coqtail#compat#nvim
let g:coqtail#compat#has_tagstack = exists('*gettagstack') && exists('*settagstack')
let g:coqtail#compat#has_tagstack_truncate = has('patch-8.2.0077')

" Has a stable version of `win_execute`.
" If `return` is true then the function must jump back to original window
" before returning. It can be set to false to avoid unnecessary jumps in the
" compatibility fallback (e.g., if `win_execute` is called in a loop).
let g:coqtail#compat#has_win_execute = has('patch-8.2.0137') || has('nvim-0.5')
if g:coqtail#compat#has_win_execute
  function! s:win_execute(id, cmd, return) abort
    call win_execute(a:id, a:cmd, '')
  endfunction
else
  function! s:win_execute(id, cmd, return) abort
    if a:return
      let l:cur_winid = win_getid()
    endif
    call win_gotoid(a:id)
    call execute(a:cmd, '')
    if a:return
      call win_gotoid(l:cur_winid)
    endif
  endfunction
endif

" Call a function using a compatible version of `win_execute`. Calling
" `s:win_execute` directly doesn't work because variables are expanded in the
" function rather than at the call site.
" E.g., `call s:win_execute(1000, 'call s:f(l:x)', 0)` would fail because `s:f`
" and `l:x` don't exist.
function! coqtail#compat#win_call(id, func, args, return) abort
  let l:cmd = printf('call call(%s, %s)', string(a:func), a:args)
  call s:win_execute(a:id, l:cmd, a:return)
endfunction

" Use `deletebufline` when available because `:delete` forces vim to exit visual mode.
if exists('*deletebufline')
  function! coqtail#compat#deleteline(first, last) abort
    silent call deletebufline('%', a:first, a:last)
  endfunction
else
  function! coqtail#compat#deleteline(first, last) abort
    execute 'silent' a:first ',' a:last 'delete _'
  endfunction
endif

function! coqtail#compat#init(python_dir) abort
  " Workaround for a NeoVim bug where py3eval returns v:null the first time
  " it's called.
  " See: https://github.com/neovim/neovim/issues/14438
  silent! call py3eval('0')
  if !(has('python3') && py3eval('sys.version_info[:2] >= (3, 6)'))
    return 0
  endif

  " Add python directory to path so Python functions can be called.
  py3 import vim
  py3 if not vim.eval('a:python_dir') in sys.path:
    \    sys.path.insert(0, vim.eval('a:python_dir'))
  return 1
endfunction
