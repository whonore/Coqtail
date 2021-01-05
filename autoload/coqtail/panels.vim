" Author: Wolf Honore
" Goal and Info panel management.

" Unique suffix for auxiliary panel names.
let s:counter = 0
" Panel identifiers.
let g:coqtail#panels#none = ''
let g:coqtail#panels#main = 'main'
let g:coqtail#panels#goal = 'goal'
let g:coqtail#panels#info = 'info'
let g:coqtail#panels#aux = [g:coqtail#panels#goal, g:coqtail#panels#info]
" Highlighting groups.
let s:hlgroups = [
  \ ['coqtail_checked', 'CoqtailChecked'],
  \ ['coqtail_sent', 'CoqtailSent'],
  \ ['coqtail_error', 'CoqtailError']
\]
let s:richpp_hlgroups = {
      \ 'diff.added': 'CoqtailDiffAdded',
      \ 'diff.removed': 'CoqtailDiffRemoved',
      \ 'diff.added.bg': 'CoqtailDiffAddedBg',
      \ 'diff.removed.bg': 'CoqtailDiffRemovedBg',
      \}

" Default panel layout.
if !exists('g:coqtail_panel_layout')
  let g:coqtail_panel_layout = {
    \ g:coqtail#panels#goal:
      \ [[g:coqtail#panels#info, 'above'], [g:coqtail#panels#main, 'right']],
    \ g:coqtail#panels#info:
      \ [[g:coqtail#panels#goal, 'below'], [g:coqtail#panels#main, 'right']]
  \}
endif

" Default panel scroll options.
if !exists('g:coqtail_panel_scroll')
  let g:coqtail_panel_scroll = {
    \ g:coqtail#panels#goal: 0,
    \ g:coqtail#panels#info: 1
  \}
endif

" Open and initialize goal/info panel.
function! s:init(name) abort
  let l:name = a:name . 's'
  let l:bufname = substitute(a:name, '\l', '\u\0', '')

  " badd forces a new buffer to be created in case the main buffer is empty
  execute 'keepjumps badd ' . l:bufname . s:counter
  execute 'silent keepjumps keepalt hide edit ' . l:bufname . s:counter
  setlocal buftype=nofile
  execute 'setlocal filetype=coq-' . l:name
  setlocal noswapfile
  setlocal bufhidden=hide
  setlocal nobuflisted
  setlocal nocursorline
  setlocal wrap

  let b:coqtail_panel_open = 1
  let b:coqtail_panel_size = [-1, -1]
  let b:coqtail_panel_richpp = []
  return bufnr('%')
endfunction

" Create buffers for the auxiliary panels.
function! coqtail#panels#init() abort
  let l:main_buf = bufnr('%')
  let l:curpos = getcurpos()[1:]
  let l:coqtail_panel_bufs = {g:coqtail#panels#main: l:main_buf}

  " Add panels
  for l:panel in g:coqtail#panels#aux
    let l:coqtail_panel_bufs[l:panel] = s:init(l:panel)
  endfor
  for l:buf in values(l:coqtail_panel_bufs)
    call setbufvar(l:buf, 'coqtail_panel_bufs', l:coqtail_panel_bufs)
  endfor

  " Switch back to main panel
  execute 'silent keepjumps keepalt buffer ' . l:main_buf
  call cursor(l:curpos)

  let s:counter += 1
endfunction

" Detect what panel is focused.
function! s:getcurpanel(buf) abort
  for [l:panel, l:buf] in items(getbufvar(a:buf, 'coqtail_panel_bufs', {}))
    if l:buf == a:buf
      return l:panel
    endif
  endfor

  return g:coqtail#panels#none
endfunction

" Attempt to switch to a panel from a buffer.
function! s:switch_from(buf, panel) abort
  let l:cur_panel = s:getcurpanel(a:buf)

  if a:panel != l:cur_panel && a:panel != g:coqtail#panels#none
    if !win_gotoid(win_getid(bufwinnr(
      \ get(getbufvar(a:buf, 'coqtail_panel_bufs', {}), a:panel, -1)
    \)))
      return g:coqtail#panels#none
    endif
  endif

  return l:cur_panel
endfunction

" Attempt to switch to a panel from the current buffer.
function! coqtail#panels#switch(panel) abort
  return s:switch_from(bufnr('%'), a:panel)
endfunction

" Open an auxiliary panel.
function! s:open(panel, force) abort
  let l:from = s:getcurpanel(bufnr('%'))
  if l:from == g:coqtail#panels#none
    return 0
  endif

  " Re-open only if not already open, it was open before, or 'force' is true
  let l:opened = 0
  let l:buf = b:coqtail_panel_bufs[a:panel]
  if bufwinnr(l:buf) == -1 && (a:force || getbufvar(l:buf, 'coqtail_panel_open'))
    " Arrange relative to the first open panel
    for [l:relative, l:dir] in g:coqtail_panel_layout[a:panel]
      if coqtail#panels#switch(l:relative) != g:coqtail#panels#none
        let l:dir = l:dir ==# 'above' ? 'leftabove'
          \ : l:dir ==# 'below' ? 'rightbelow'
          \ : l:dir ==# 'left' ? 'vertical leftabove'
          \ : l:dir ==# 'right' ? 'vertical rightbelow' : ''
        if l:dir !=# ''
          execute printf('silent keepjumps keepalt %s sbuffer %d', l:dir, l:buf)
          clearjumps
          let b:coqtail_panel_open = 1
          let l:opened = l:buf
          break
        endif
      endif
    endfor
  endif

  call coqtail#define_commands()
  call coqtail#define_mappings()

  call coqtail#panels#switch(l:from)
  return l:opened
endfunction

" Open auxiliary panels.
function! coqtail#panels#open(force) abort
  " Open
  let l:opened = []
  for l:panel in g:coqtail#panels#aux
    if s:open(l:panel, a:force)
      let l:opened = add(l:opened, l:panel)
    endif
  endfor

  " Resize
  for l:panel in l:opened
    let l:buf = b:coqtail_panel_bufs[l:panel]
    let l:win = bufwinnr(l:buf)
    let l:size = getbufvar(l:buf, 'coqtail_panel_size')
    if l:size != [-1, -1]
      execute printf('vertical %dresize %d', l:win, l:size[0])
      execute printf('%dresize %d', l:win, l:size[1])
    endif
  endfor
endfunction

" Scroll a panel up so text doesn't go off the top of the screen.
function! s:scroll() abort
  " Check if scrolling is necessary
  let l:winh = winheight(0)
  let l:disph = line('w$') - line('w0') + 1

  " Scroll
  if line('w0') != 1 && l:disph < l:winh
    normal! Gz-
  endif
endfunction

" Clear Coqtop highlighting.
function! s:clearhl(win) abort
  for [l:var, l:_] in s:hlgroups
    let l:val = getwinvar(a:win, l:var, -1)
    if l:val != -1
      call matchdelete(l:val)
      call setwinvar(a:win, l:var, -1)
    endif
  endfor
endfunction

" Close auxiliary panels and clear highlighting.
function! coqtail#panels#hide() abort
  if coqtail#panels#switch(g:coqtail#panels#main) == g:coqtail#panels#none
    return
  endif

  call s:clearhl(winnr())

  " Hide other panels
  let l:toclose = []
  for l:panel in g:coqtail#panels#aux
    let l:buf = b:coqtail_panel_bufs[l:panel]
    let l:win = bufwinnr(l:buf)
    call setbufvar(l:buf, 'coqtail_panel_open', l:win != -1)
    call setbufvar(l:buf, 'coqtail_panel_size', [winwidth(l:win), winheight(l:win)])
    if l:win != -1
      let l:toclose = add(l:toclose, l:buf)
    endif
  endfor

  for l:buf in l:toclose
    execute bufwinnr(l:buf) . 'close!'
  endfor
endfunction

" Replace the contents of 'panel' with 'txt'.
function! s:replace(buf, panel, txt, richpp, scroll) abort
  if s:switch_from(a:buf, a:panel) == g:coqtail#panels#none
    return
  endif

  " Save the view
  let l:view = winsaveview()

  " Remove previous highlights
  for l:match in b:coqtail_panel_richpp
    call matchdelete(l:match)
  endfor

  " Update buffer text
  silent %delete _
  call append(0, a:txt)

  " Set new highlights
  let l:matches = []
  for [l:line_no, l:start_pos, l:span, l:hlgroup] in a:richpp
    if has_key(s:richpp_hlgroups, l:hlgroup)
      let l:match = matchaddpos(s:richpp_hlgroups[l:hlgroup], [[l:line_no, l:start_pos, l:span]])
      call add(l:matches, l:match)
    endif
  endfor

  let b:coqtail_panel_richpp = l:matches

  " Restore the view
  if !a:scroll || !g:coqtail_panel_scroll[a:panel]
    call winrestview(l:view)
  endif
  call s:scroll()
endfunction

" Refresh the highlighting and auxiliary panels.
function! coqtail#panels#refresh(buf, highlights, panels, scroll) abort
  " Catch interrupt instead of aborting
  try
    let l:wins = win_findbuf(a:buf)
    let l:refreshing = getbufvar(a:buf, 'coqtail_refreshing', 0)
    if l:wins == [] || l:refreshing
      return
    endif
    call setbufvar(a:buf, 'coqtail_refreshing', 1)
    let l:cur_win = win_getid()

    " Update highlighting
    for l:win in l:wins
      call win_gotoid(l:win)

      call s:clearhl(l:win)
      for [l:var, l:grp] in s:hlgroups
        let l:hl = a:highlights[l:var]
        if l:hl != v:null
          call setwinvar(l:win, l:var, matchadd(l:grp, l:hl, -10))
        endif
      endfor
    endfor

    " Update panels
    for [l:panel, l:panel_data] in items(a:panels)
      let [l:txt, l:richpp] = l:panel_data
      call s:replace(a:buf, l:panel, l:txt, l:richpp, a:scroll)
    endfor
  catch /^Vim:Interrupt$/
  finally
    " l:cur_win might not exist yet
    silent! call win_gotoid(l:cur_win)
    call setbufvar(a:buf, 'coqtail_refreshing', 0)
    redraw
  endtry
endfunction

" Delete panel variables and clear highlighting.
function! coqtail#panels#cleanup() abort
  for l:panel in g:coqtail#panels#aux
    silent! execute 'bwipeout' b:coqtail_panel_bufs[l:panel]
  endfor
  silent! unlet b:coqtail_panel_bufs

  call s:clearhl(winnr())
endfunction

" Getter for variables local to the main buffer
function! coqtail#panels#getvar(var) abort
  return getbufvar(b:coqtail_panel_bufs.main, a:var)
endfunction

" Setter for variables local to the main buffer
function! coqtail#panels#setvar(var, val) abort
  return setbufvar(b:coqtail_panel_bufs.main, a:var, a:val)
endfunction
