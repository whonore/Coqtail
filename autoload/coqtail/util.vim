" Author: Wolf Honore
" Utility functions.

" Print a message with warning highlighting.
function! coqtail#util#warn(msg) abort
  echohl WarningMsg | echom a:msg | echohl None
endfunction

" Print a message with error highlighting.
function! coqtail#util#err(msg) abort
  echohl ErrorMsg | echom a:msg | echohl None
endfunction

" Get the word under the cursor using the special '<cword>' variable. First
" add some characters to the 'iskeyword' option to treat them as part of the
" current word.
function! coqtail#util#getcurword() abort
  " Add '.' to definition of a keyword
  let l:old_keywd = &iskeyword
  setlocal iskeyword+=.

  let l:cword = expand('<cword>')

  " Strip trailing '.'s
  let l:dotidx = match(l:cword, '[.]\+$')
  if l:dotidx > -1
    let l:cword = l:cword[: l:dotidx - 1]
  endif

  " Reset iskeyword
  let &l:iskeyword = l:old_keywd

  return l:cword
endfunction

" Get the text selected in Visual mode.
function! coqtail#util#getvisual() abort
  try
    let l:v_old = @v
    normal! gv"vy
    return join(split(@v, '\n'), ' ')
  finally
    " Restore register
    let @v = l:v_old
  endtry
endfunction

" Remove entries in the quickfix list with the same position.
function! coqtail#util#dedup_qflist() abort
  let l:qfl = getqflist()
  let l:seen = {}
  let l:uniq = []

  for l:entry in l:qfl
    let l:pos = string([l:entry.lnum, l:entry.col])
    if !has_key(l:seen, l:pos)
      let l:seen[l:pos] = 1
      let l:uniq = add(l:uniq, l:entry)
    endif
  endfor

  call setqflist(l:uniq)
endfunction

" Get 'var' from the first scope in 'scopes' in which it is defined.
function! coqtail#util#getvar(scopes, var, default) abort
  return a:scopes != []
    \ ? get(a:scopes[0], a:var, coqtail#util#getvar(a:scopes[1:], a:var, a:default))
    \ : a:default
endfunction
