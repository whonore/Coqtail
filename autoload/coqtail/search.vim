" Coqtail functions for searching common commands

let s:command_pattern    = '\C^\s*\zs\%(Axiom\|\%(Co\)\?Fixpoint\|Corollary\|Definition\|Example\|Goal\|Lemma\|Proposition\|Theorem\)\>'
let s:proofstart_pattern = '\C\%(\<Fail\_s\+\)\@<!\<\%(Proof\|Next Obligation\|Final Obligation\|Obligation \d\+\)\>[^.]*\.'
let s:proofend_pattern   = '\C\<\%(Qed\|Defined\|Abort\|Admitted\|Save\)\>\.'

function! coqtail#search#command(flags, count, visual) abort
  call s:search_count(
        \ s:command_pattern,
        \ a:flags,
        \ a:count,
        \ a:visual)
endfunction

function! coqtail#search#proof(flags, count, visual) abort
  call s:search_count(
        \ a:flags =~# 'b' ? s:proofstart_pattern : s:proofend_pattern,
        \ a:flags,
        \ a:count,
        \ a:visual)
endfunction

function! s:search_count(pattern, flags, count, visual) abort
  mark '
  if a:visual
    normal! gv
  endif
  for i in range(a:count)
    if !search(a:pattern, a:flags)
      break
    endif
  endfor
endfunction

function! s:get_proofs_delim() abort
  let origpos = getpos('.')

  " Accept a match even if the cursor isn't exactly at the beginning of a word
  let combined = '\%(' . s:proofstart_pattern . '\|' . s:proofend_pattern . '\)'
  let matchstart = searchpos(combined, 'bcW')
  if matchstart != [0, 0]
    let matchend = searchpos(combined, 'ce')
    if matchend[0] < origpos[1]
          \ || (matchend[0] == origpos[1] && matchend[1] < origpos[2])
      call setpos('.', origpos)
    else
      call cursor(matchstart)
    endif
  endif

  let block = searchpairpos(s:proofstart_pattern, '', s:proofend_pattern, 'cW')

  if block == [0, 0]
    call search(s:proofstart_pattern, 'cW')
    let start = getpos('.')
    call search(s:proofend_pattern, 'W')
    let end = getpos('.')
  else
    let end = getpos('.')
    call search(s:proofstart_pattern, 'bW')
    let start = getpos('.')
  endif

  call setpos('.', origpos)
  return [start, end]
endfunction


function! s:select_i() abort
  let [start, end] = s:get_proofs_delim()
  let start_max_col = match(getline(start[1]), '^[^.]\+\.\zs', start[2]) + 1

  " For indented proof blocks find the first non-whitespace character
  let start_first_col = match(getline(start[1]), '\S') + 1
  let end_first_col = match(getline(end[1]), '\S') + 1

  if end[1] - start[1] > 1
        \ && end[2] == end_first_col
        \ && start_max_col == col([start[1], '$'])
    let start[1] += 1
    let start[2]  = start_first_col
    let end[1]   -= 1
    let end[2]    = end_first_col

    return ['V', start, end]
  else
    if start_max_col == col([start[1], '$'])
      let start[1] += 1
      let start[2]  = start_first_col
    else
      let start[2] = start_max_col
    endif

    if end[2] == end_first_col
      let end[1] -= 1
      let end[2]  = col([end[1], '$'])
    else
      let end[2] -= 1
    endif

    if start[1] > end[1] || (start[1] == end[1] && start[2] >= end[2])
      return 0
    endif

    return ['v', start, end]
  endif
endfunction

function! s:select_a() abort
  let [start, end] = s:get_proofs_delim()
  let end_max_col = match(getline(end[1]), '^[^.]\+\.\zs', end[2]) + 1

  " For indented proof blocks find the first non-whitespace character
  let start_first_col = match(getline(start[1]), '\S') + 1
  let end_first_col = match(getline(end[1]), '\S') + 1

  if start[2] > start_first_col || end[2] > end_first_col || end_max_col != col([end[1], '$'])
    let end[2] = end_max_col
    return ['v', start, end]
  else
    return ['V', start, end]
  endif
endfunction

function! s:select_wrapper(args) abort
  if type(a:args) == type([]) && len(a:args) == 3
    let [visual, start, end] = a:args
    call setpos('.', start)
    exe 'normal! ' . visual
    call setpos('.', end)
  endif
endfunction

function! coqtail#search#select_i() abort
  call s:select_wrapper(s:select_i())
endfunction

function! coqtail#search#select_a() abort
  call s:select_wrapper(s:select_a())
endfunction
