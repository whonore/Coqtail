" Coqtail functions for searching common commands

let s:command_pattern    = '\C^\s*\zs\%(Axiom\|\%(Co\)\?Fixpoint\|Corollary\|Definition\|Example\|Goal\|Lemma\|Proposition\|Theorem\)\>'
let s:proofstart_pattern = '\C\%(\<Fail\_s\+\)\@<!\<\%(Proof\|Next Obligation\|Final Obligation\|Obligation \d\+\)\>[^.]*\.'
let s:proofend_pattern   = '\C\<\%(Qed\|Defined\|Abort\|Admitted\|Save\)\>'

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

function! s:find_proof_block() abort
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
  return [start, end]
endfunction

function! coqtail#search#select_i() abort
  let [start, end] = s:find_proof_block()
  let start_max_col = match(getline(start[1]), '^[^.]\+\.\zs', start[2]) + 1

  if start[1] != end[1] && start[2] == 1 && end[2] == 1 && start_max_col == col([start[1], '$'])
    let start[1] += 1
    let start[2]  = 0
    let end[1]   -= 1
    let end[2]    = 0

    call setpos('.', start)
    normal! V
    call setpos('.', end)
  else
    if start_max_col == col([start[1], '$'])
      let start[1] += 1
      let start[2]  = 0
    else
      let start[2] = start_max_col
    endif

    if end[2] == 1
      let end[1] -= 1
      let end[2]  = col([end[1], '$'])
    else
      let end[2] -= 1
    endif

    call setpos('.', start)
    normal! v
    call setpos('.', end)
  endif
endfunction

function! coqtail#search#select_a() abort
  let [start, end] = s:find_proof_block()
  let end_max_col = match(getline(end[1]), '^[^.]\+\.\zs', end[2]) + 1

  call setpos('.', start)
  if start[2] > 1 || end[2] > 1 || end_max_col != col([end[1], '$'])
    let end[2] = end_max_col
    normal! v
  else
    normal! V
  endif
  call setpos('.', end)
endfunction
