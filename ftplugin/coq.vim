" Only source once.
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

call coqtail#Register()

" Comments
if has('comments')
  setlocal commentstring=(*%s*)
  setlocal comments=srn:(*,mb:*,exn:*)
  " N.B. The 'r' and 'o' flags mistake the '*' bullet as a middle comment
  " and will automatically add an extra one after <Enter>, 'o' or 'O'.
  setlocal formatoptions-=tro formatoptions+=cql
endif

" Follow imports
setlocal includeexpr=coqtail#FindLib(v:fname)
setlocal suffixesadd=.v
setlocal include=\\<Require\\>\\(\\s*\\(Import\\\|Export\\)\\>\\)\\?

let b:undo_ftplugin = 'setl cms< com< fo< inex< sua< inc<'

" Tags
if exists('+tagfunc')
  setlocal tagfunc=coqtail#GetTags
  let b:undo_ftplugin .= ' | setl tfu<'
endif

" matchit/matchup patterns
if (exists('loaded_matchit') || exists('loaded_matchup')) && !exists('b:match_words')
  let b:match_ignorecase = 0
  let s:proof_starts = ['Proof', 'Next\_s\+Obligation', 'Obligation\_s\+\d\+']
  let s:proof_ends = ['Qed', 'Defined', 'Admitted', 'Abort', 'Save']
  let s:proof_start = '\%(' . join(map(s:proof_starts, '"\\<" . v:val . "\\>"'), '\|') . '\)'
  let s:proof_end = '\%(' . join(map(s:proof_ends, '"\\<" . v:val . "\\>"'), '\|') . '\)'
  let b:match_words = join([
    \ '\<if\>:\<then\>:\<else\>',
    \ '\<let\>:\<in\>',
    \ '\<\%(lazy\)\?match\>:\<with\>:\<end\>',
    \ '\%(\<Section\>\|\<Module\>\):\<End\>',
    \ s:proof_start . ':' . s:proof_end
  \], ',')
  let b:undo_ftplugin .= ' | unlet! b:match_ignorecase b:match_words'
endif
