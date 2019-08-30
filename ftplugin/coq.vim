call coqtail#Register()

" Treat ' as a part of keywords
setlocal iskeyword+='

" Follow imports
setlocal includeexpr=coqtail#FindLib(v:fname)
setlocal suffixesadd=.v
setlocal include=\\<Require\\>\\(\\s*\\(Import\\\|Export\\)\\>\\)\\?
