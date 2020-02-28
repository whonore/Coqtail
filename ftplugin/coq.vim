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
