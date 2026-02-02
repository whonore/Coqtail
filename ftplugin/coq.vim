" Only source once.
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

let b:undo_ftplugin = []

if g:coqtail#supported
  call coqtail#register()
endif

" Comments
if has('comments')
  setlocal commentstring=(*%s*)
  setlocal comments=srn:(*,mb:*,ex:*)
  " NOTE: The 'r' and 'o' flags mistake the '*' bullet as a middle comment and
  " will automatically add an extra one after <Enter>, 'o' or 'O'.
  setlocal formatoptions-=t formatoptions-=r formatoptions-=o formatoptions+=cql
  let b:undo_ftplugin = add(b:undo_ftplugin, 'setl cms< com< fo<')
endif

" Follow imports
if g:coqtail#supported
  setlocal includeexpr=coqtail#findlib(v:fname)
  setlocal suffixesadd=.v
  setlocal include=\\<Require\\>\\(\\_s*\\(Import\\\|Export\\)\\>\\)\\?
  let b:undo_ftplugin = add(b:undo_ftplugin, 'setl inex< sua< inc<')
endif

" Tags
if exists('+tagfunc') && g:coqtail#supported && get(g:, 'coqtail_tagfunc', 1)
  setlocal tagfunc=coqtail#gettags
  let b:undo_ftplugin = add(b:undo_ftplugin, 'setl tfu<')
endif

" Jump around commands and proofs
if !get(g:, 'coqtail_nomap', 0)
  let s:command_pattern    = '\C^\s*\zs\%(Axiom\|\%(Co\)\?Fixpoint\|Corollary\|Definition\|Example\|Goal\|Lemma\|Proposition\|Theorem\)\>'
  let s:proofstart_pattern = '\C\%(\<Fail\_s\+\)\@<!\<\%(Proof\|Next Obligation\|Final Obligation\|Obligation \d\+\)\>[^.]*\.'
  let s:proofend_pattern   = '\C\<\%(Qed\|Defined\|Abort\|Admitted\|Save\)\>'

  function! s:command_search(flags, count, visual) abort
    mark '
    if a:visual
      normal! gv
    endif
    for i in range(a:count)
      if !search(s:command_pattern, a:flags)
        break
      endif
    endfor
  endfunction

  function! s:proof_search(flags, count, visual) abort
    let pattern = a:flags =~# 'b' ? s:proofstart_pattern : s:proofend_pattern
    mark '
    if a:visual
      normal! gv
    endif
    for i in range(a:count)
      if !search(pattern, a:flags)
        break
      endif
    endfor
  endfunction

  nnoremap <buffer> <silent> [[ :<C-u>call <Sid>command_search('Wb', v:count1, 0)<CR>
  xnoremap <buffer> <silent> [[ :<C-u>call <Sid>command_search('Wb', v:count1, 1)<CR>

  nnoremap <buffer> <silent> ]] :<C-u>call <Sid>command_search('W' , v:count1, 0)<CR>
  xnoremap <buffer> <silent> ]] :<C-u>call <Sid>command_search('W' , v:count1, 1)<CR>

  nnoremap <buffer> <silent> [] :<C-u>call <Sid>proof_search('Wb', v:count1, 0)<CR>
  xnoremap <buffer> <silent> [] :<C-u>call <Sid>proof_search('Wb', v:count1, 1)<CR>

  nnoremap <buffer> <silent> ][ :<C-u>call <Sid>proof_search('W', v:count1, 0)<CR>
  xnoremap <buffer> <silent> ][ :<C-u>call <Sid>proof_search('W', v:count1, 1)<CR>

  let b:undo_ftplugin = b:undo_ftplugin
        \->add('silent! nunmap <buffer> [[')
        \->add('silent! xunmap <buffer> [[')
        \->add('silent! nunmap <buffer> ]]')
        \->add('silent! xunmap <buffer> ]]')
        \->add('silent! nunmap <buffer> []')
        \->add('silent! xunmap <buffer> []')
        \->add('silent! nunmap <buffer> ][')
        \->add('silent! xunmap <buffer> ][')
endif

" matchit/matchup patterns
if (exists('g:loaded_matchit') || exists('g:loaded_matchup')) && !exists('b:match_words')
  let b:match_ignorecase = 0
  let s:proof_starts = ['Proof', 'Next\_s\+Obligation', 'Final\_s\+Obligation', 'Obligation\_s\+\d\+']
  let s:proof_ends = ['Qed', 'Defined', 'Admitted', 'Abort', 'Save']
  let s:proof_start = '\%(' . join(map(s:proof_starts, '"\\<" . v:val . "\\>"'), '\|') . '\)'
  let s:proof_end = '\%(' . join(map(s:proof_ends, '"\\<" . v:val . "\\>"'), '\|') . '\)'
  let b:match_words = join([
    \ '\<if\>:\<then\>:\<else\>',
    \ '\<let\>:\<in\>',
    \ '\<\%(lazy\|multi\)\?match\>:\<with\>:\<end\>',
    \ '\%(\<Section\>\|\<Module\>\):\<End\>',
    \ s:proof_start . ':' . s:proof_end
  \], ',')
  let b:undo_ftplugin = add(b:undo_ftplugin, 'unlet! b:match_ignorecase b:match_words')
endif

" endwise
if exists('g:loaded_endwise')
  let b:endwise_addition = '\=submatch(0) =~# "match" ? "end." : "End " . submatch(0) . "."'
  let b:endwise_words = 'Section,Module,\%(lazy\|multi\)\?match'
  let s:section_pat = '\<\%(Section\|Module\)\_s\+\%(\<Type\>\_s\+\)\?\zs\S\+\ze\_s*\.'
  let s:match_pat = '\<\%(lazy\|multi\)\?match\>'
  let b:endwise_pattern = '\%(' . s:section_pat . '\|' . s:match_pat . '\)'
  let b:endwise_syngroups = 'coqVernacCmd,coqKwd,coqLtac'
  unlet! b:endwise_end_pattern
  let b:undo_ftplugin = add(
    \ b:undo_ftplugin,
    \ 'unlet! b:endwise_addition b:endwise_words b:endwise_pattern b:endwise_syngroups')
endif

let b:undo_ftplugin = join(b:undo_ftplugin, ' | ')
