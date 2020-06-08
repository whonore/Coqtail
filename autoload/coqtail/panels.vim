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
let g:coqtail#panels#hlgroups = [
  \ ['coqtail_checked', 'CoqtailChecked'],
  \ ['coqtail_sent', 'CoqtailSent'],
  \ ['coqtail_error', 'CoqtailError']
\]

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

  execute 'silent hide edit ' . l:bufname . s:counter
  setlocal buftype=nofile
  execute 'setlocal filetype=coq-' . l:name
  setlocal noswapfile
  setlocal bufhidden=hide
  setlocal nocursorline
  setlocal wrap

  let b:coqtail_panel_open = 1
  let b:coqtail_panel_size = [-1, -1]
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
  execute 'silent buffer ' . l:main_buf
  call cursor(l:curpos)

  let s:counter += 1
endfunction

" Detect what panel is focused.
function! s:getcurpanel() abort
  if !exists('b:coqtail_panel_bufs')
    return g:coqtail#panels#none
  endif

  for [l:panel, l:buf] in items(b:coqtail_panel_bufs)
    if l:buf == bufnr('%')
      return l:panel
    endif
  endfor
endfunction

" Attempt to switch to a panel.
function! coqtail#panels#switch(panel) abort
  let l:cur_panel = s:getcurpanel()

  if a:panel != l:cur_panel && a:panel != g:coqtail#panels#none
    if !win_gotoid(win_getid(bufwinnr(b:coqtail_panel_bufs[a:panel])))
      return g:coqtail#panels#none
    endif
  endif

  return l:cur_panel
endfunction

" Open an auxiliary panel.
function! s:open(panel, force) abort
  let l:from = s:getcurpanel()
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
          execute printf('silent %s sbuffer %d', l:dir, l:buf)
          let b:coqtail_panel_open = 1
          let l:opened = l:buf
          break
        endif
      endif
    endfor
  endif

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

" Replace the contents of 'panel' with 'txt'.
function! coqtail#panels#replace(panel, txt, scroll) abort
  if coqtail#panels#switch(a:panel) == g:coqtail#panels#none
    return
  endif

  " Save the view
  let l:view = winsaveview()

  " Update buffer text
  silent %delete _
  call append(0, a:txt)

  " Restore the view
  if !a:scroll || !g:coqtail_panel_scroll[a:panel]
    call winrestview(l:view)
  endif
  call s:scroll()
endfunction

" Clear Coqtop highlighting.
function! s:clearhl() abort
  for [l:var, l:_] in g:coqtail#panels#hlgroups
    if get(b:, l:var, -1) != -1
      call matchdelete(b:[l:var])
      let b:[l:var] = -1
    endif
  endfor
endfunction

" Close auxiliary panels and clear highlighting.
function! coqtail#panels#hide() abort
  if coqtail#panels#switch(g:coqtail#panels#main) == g:coqtail#panels#none
    return
  endif

  call s:clearhl()

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

" Refresh the highlighting and auxiliary panels.
function! coqtail#panels#refresh(buf, highlights, panels, scroll) abort
  if a:buf != bufnr('%')
    return
  endif
  let l:win = win_getid()

  " Update highlighting
  call s:clearhl()
  for [l:var, l:grp] in g:coqtail#panels#hlgroups
    let l:hl = a:highlights[l:var]
    if l:hl != v:null
      let b:[l:var] = matchadd(l:grp, l:hl)
    endif
  endfor

  " Update panels
  try
    for [l:panel, l:txt] in items(a:panels)
      call coqtail#panels#replace(l:panel, l:txt, a:scroll)
    endfor
  finally
    call win_gotoid(l:win)
  endtry

  redraw
endfunction

" Delete panel variables and clear highlighting.
function! coqtail#panels#cleanup() abort
  for l:panel in g:coqtail#panels#aux
    silent! execute 'bdelete' . b:coqtail_panel_bufs[l:panel]
  endfor
  silent! unlet b:coqtail_panel_bufs

  call s:clearhl()
endfunction
