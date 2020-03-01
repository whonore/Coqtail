" Only source once
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

call coqtail#Register()

" Treat ' as a part of keywords
setlocal iskeyword+='
" Remove ? added by Verilog syntax file
setlocal iskeyword-=63

" Follow imports
setlocal includeexpr=coqtail#FindLib(v:fname)
setlocal suffixesadd=.v
setlocal include=\\<Require\\>\\(\\s*\\(Import\\\|Export\\)\\>\\)\\?

" Tags
if exists('+tagfunc')
  setlocal tagfunc=coqtail#GetTags
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
endif
