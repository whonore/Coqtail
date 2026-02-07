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
