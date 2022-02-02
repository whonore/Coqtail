" Author: Wolf Honore
" Utility functions.

" Print a message with the specified highlighting.
" NOTE: Without 'unsilent' messages triggered during autocmds don't display in
" NeoVim because 'shortmess+=F' is set by default.
" See: https://github.com/neovim/neovim/issues/8675
function! s:echom(msg, hl) abort
  execute 'echohl' a:hl
  for l:line in split(a:msg, '\n')
    unsilent echom l:line
  endfor
  echohl None
endfunction

" Print a message with warning highlighting.
function! coqtail#util#warn(msg) abort
  call s:echom(a:msg, 'WarningMsg')
endfunction

" Print a message with error highlighting.
function! coqtail#util#err(msg) abort
  call s:echom(a:msg, 'ErrorMsg')
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
    noautocmd normal! gv"vy
    return join(split(@v, '\n'), ' ')
  finally
    " Restore register
    let @v = l:v_old
  endtry
endfunction

" Remove entries in the quickfix list with the same position.
function! s:dedup_qflist() abort
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

" Find the positions of all matches.
function! s:searchall(text, search) abort
  let l:matches = []
  let l:cnt = 1

  while 1
    let l:match = matchstrpos(a:text, a:search, 0, l:cnt)[0:2]
    if l:match[1] == -1
      break
    endif

    let l:matches = add(l:matches, l:match)
    let l:cnt += 1
  endwhile

  return l:matches
endfunction

" Perform a sequence of searches and put the results in the quickfix list.
function! coqtail#util#qflist_search(buf, path, searches) abort
  " Temporarily set the global value of 'iskeyword' to the local value (which
  " should be Coq's). Otherwise ' is not handled properly by vimgrep.
  let l:isk = &g:iskeyword
  let &g:iskeyword = &l:iskeyword

  let l:found_match = 0
  let l:has_file = a:path !=# ''
  if !l:has_file
    let l:text = getbufline(a:buf, 1, '$')
    let l:matches = []
  endif

  for l:search in a:searches
    let l:search = '\v\C' . l:search
    try
      if !l:has_file
        let l:matches += map(
          \ s:searchall(l:text, l:search),
          \ '{"bufnr": a:buf, "text": v:val[0], "lnum": v:val[1] + 1, "col": v:val[2] + 1}')
      elseif !l:found_match
        execute 'vimgrep /' . l:search . '/j ' . a:path
        let l:found_match = 1
      else
        execute 'vimgrepadd /' . l:search . '/j ' . a:path
      endif
    catch /^Vim\%((\a\+)\)\=:E480/
    endtry
  endfor

  if !l:has_file
    let l:found_match = l:matches != []
    if l:found_match
      call setqflist(l:matches)
    endif
  endif

  if l:found_match
    " Filter duplicate matches
    call s:dedup_qflist()
  endif

  let &g:iskeyword = l:isk
  return l:found_match
endfunction

" Get 'var' from the first scope in 'scopes' in which it is defined.
function! coqtail#util#getvar(scopes, var, default) abort
  return a:scopes != []
    \ ? get(a:scopes[0], a:var, coqtail#util#getvar(a:scopes[1:], a:var, a:default))
    \ : a:default
endfunction
