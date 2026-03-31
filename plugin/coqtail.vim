" Only source once.
if exists('g:loaded_coqtail')
  finish
endif
let g:loaded_coqtail = 1

" Initialize global variables.
" Default CoqProject file name.
if !exists('g:coqtail_project_names')
  let g:coqtail_project_names = ['_CoqProject', '_RocqProject']
endif

" Default to updating the tagstack on coqtail#gotodef.
if !exists('g:coqtail_update_tagstack')
  let g:coqtail_update_tagstack = 1
endif

" Default to not treating all stderr messages as warnings.
if !exists('g:coqtail_treat_stderr_as_warning')
  let g:coqtail_treat_stderr_as_warning = 0
endif

" Default to preferring dune if in a dune project.
if !exists('g:coqtail_build_system')
  let g:coqtail_build_system = 'prefer-dune'
endif

" Default to not compiling deps
if !exists('g:coqtail_dune_compile_deps')
  let g:coqtail_dune_compile_deps = 0
endif

" Use 'set' because wildignore is a global option
set wildignore+=*.vo,*.vo[ks],*.glob
