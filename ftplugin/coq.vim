" Only source once.
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

if g:coqtail_supported
  " Initialize buffer local variables, commands, and mappings.
  call coqtail#register()

  " Set 'path" to Rocq's library location
  let &l:path = coqtail#util#getpath()
else
  call coqtail#util#warn(
        \ "Coqtail requires Python 3.6 or later.\n" .
        \ 'See https://github.com/whonore/Coqtail/blob/main/README.md#python-2-support.'
        \)

  setlocal path-=/usr/include
endif

let b:undo_ftplugin = 'setl pa<'

setlocal suffixesadd=.v
setlocal include=\\<Require\\>\\(\\_s*\\(Import\\\|Export\\)\\>\\)\\?
let b:undo_ftplugin .= ' | setl sua< inc<'

" Follow imports
setlocal includeexpr=coqtail#includeexpr()
let b:undo_ftplugin .= ' | setl inex<'

" Comments
if has('comments')
  setlocal commentstring=(*%s*)
  setlocal comments=srn:(*,mb:*,ex:*)
  " NOTE: The 'r' and 'o' flags mistake the '*' bullet as a middle comment and
  " will automatically add an extra one after <Enter>, 'o' or 'O'.
  setlocal formatoptions-=t formatoptions-=r formatoptions-=o formatoptions+=cql
  let b:undo_ftplugin .= ' | setl cms< com< fo<'
endif

" Tags
if exists('+tagfunc') && g:coqtail_supported && get(g:, 'coqtail_tagfunc', 1)
  setlocal tagfunc=coqtail#gettags
  let b:undo_ftplugin .= ' | setl tfu<'
endif

" Maps
if !get(g:, 'coqtail_nomap', 0)
  " Jump around commands and proofs
  nnoremap <buffer> <silent> [[ :<C-u>call coqtail#search#command('Wb', v:count1, 0)<CR>
  xnoremap <buffer> <silent> [[ :<C-u>call coqtail#search#command('Wb', v:count1, 1)<CR>

  nnoremap <buffer> <silent> ]] :<C-u>call coqtail#search#command('W' , v:count1, 0)<CR>
  xnoremap <buffer> <silent> ]] :<C-u>call coqtail#search#command('W' , v:count1, 1)<CR>

  nnoremap <buffer> <silent> [] :<C-u>call coqtail#search#proof('Wb', v:count1, 0)<CR>
  xnoremap <buffer> <silent> [] :<C-u>call coqtail#search#proof('Wb', v:count1, 1)<CR>

  nnoremap <buffer> <silent> ][ :<C-u>call coqtail#search#proof('W', v:count1, 0)<CR>
  xnoremap <buffer> <silent> ][ :<C-u>call coqtail#search#proof('W', v:count1, 1)<CR>

  let b:undo_ftplugin .= ' | silent! nunmap <buffer> [['
  let b:undo_ftplugin .= ' | silent! xunmap <buffer> [['
  let b:undo_ftplugin .= ' | silent! nunmap <buffer> ]]'
  let b:undo_ftplugin .= ' | silent! xunmap <buffer> ]]'
  let b:undo_ftplugin .= ' | silent! nunmap <buffer> []'
  let b:undo_ftplugin .= ' | silent! xunmap <buffer> []'
  let b:undo_ftplugin .= ' | silent! nunmap <buffer> ]['
  let b:undo_ftplugin .= ' | silent! xunmap <buffer> ]['
endif

" Proof text object
onoremap <buffer> <silent> <Plug>(proof-text-object-inner) :<C-u>call coqtail#search#select_i()<CR>
xnoremap <buffer> <silent> <Plug>(proof-text-object-inner) :<C-u>call coqtail#search#select_i()<CR>
onoremap <buffer> <silent> <Plug>(proof-text-object-outer) :<C-u>call coqtail#search#select_a()<CR>
xnoremap <buffer> <silent> <Plug>(proof-text-object-outer) :<C-u>call coqtail#search#select_a()<CR>

if !get(g:, 'coqtail_nomap', 0)
  omap <buffer> iP <Plug>(proof-text-object-inner)
  xmap <buffer> iP <Plug>(proof-text-object-inner)
  omap <buffer> aP <Plug>(proof-text-object-outer)
  xmap <buffer> aP <Plug>(proof-text-object-outer)

  let b:undo_ftplugin .= ' | silent! ounmap <buffer> iP'
  let b:undo_ftplugin .= ' | silent! xunmap <buffer> iP'
  let b:undo_ftplugin .= ' | silent! ounmap <buffer> aP'
  let b:undo_ftplugin .= ' | silent! xunmap <buffer> aP'
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
  let b:undo_ftplugin .= ' | unlet! b:match_ignorecase b:match_words'
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
  let b:undo_ftplugin .= ' | unlet! b:endwise_addition b:endwise_words b:endwise_pattern b:endwise_syngroups'
endif

" Use g:coqtail_joinspaces as the local version of 'joinspaces'
augroup CoqtailJoinspaces
  autocmd!
  autocmd BufEnter <buffer>
        \ if !exists('b:_coqtail_save_js')
        \ |   let b:_coqtail_save_js = &js
        \ | endif
        \ | let &joinspaces = get(g:, 'coqtail_joinspaces', 0)

  autocmd BufLeave <buffer>
        \ let &joinspaces = get(b:, '_coqtail_save_js', 1)
        \ | unlet! b:_coqtail_save_js
augroup END

" Define Coqtail-specific highlighting groups.
function! s:CoqtailHighlight() abort
  if exists('*g:CoqtailHighlight')
    " Use user-defined colors if they exist.
    " NOTE: This is only for backwards compatability. Use the ColorScheme
    " autocommand instead.
    call g:CoqtailHighlight()
  else
    let l:t_Co = exists('&t_Co') && !empty(&t_Co) && &t_Co > 1 ? &t_Co : 1
    let l:checked = {}
    let l:sent = {}

    if &background ==# 'dark'
      " Dark GUI colors
      let l:checked.guibg = '#000087'
      let l:sent.guibg    = '#5F5F87'

      if l:t_Co >= 256
        " Dark 256-color terminal
        let l:checked.ctermbg = '18'
        let l:sent.ctermbg    = '60'
      else
        " Dark 16-color terminal
        let l:checked.ctermbg = '4'
        let l:sent.ctermbg    = '6'
      endif
    else
      " Light GUI colors
      let l:checked.guibg = '#90EE90'
      let l:sent.guibg    = '#32CD32'

      if l:t_Co >= 256
        " Light 256-color terminal
        let l:checked.ctermbg = '120'
        let l:sent.ctermbg    = '40'
      else
        " Light 16-color terminal
        let l:checked.ctermbg = '10'
        let l:sent.ctermbg    = '2'
      endif
    endif
  endif

  exe printf("hi def CoqtailChecked ctermbg=%s guibg=%s", l:checked.ctermbg, l:checked.guibg)
  exe printf("hi def CoqtailSent    ctermbg=%s guibg=%s", l:sent.ctermbg   , l:sent.guibg)

  hi def link CoqtailDiffAdded     DiffText
  hi def link CoqtailDiffAddedBg   DiffChange
  hi def link CoqtailDiffRemoved   DiffDelete
  hi def link CoqtailDiffRemovedBg DiffDelete
  hi def link CoqtailError         Error
  hi def link CoqtailOmitted       coqProofAdmit
endfunction

" Apply colors at least once here
call s:CoqtailHighlight()

augroup CoqtailHighlight
  autocmd!
  " Reapply highlighting when the colorscheme changes
  autocmd ColorScheme * call <Sid>CoqtailHighlight()
augroup END
