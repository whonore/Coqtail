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
  \ ['checked', 'CoqtailChecked'],
  \ ['sent', 'CoqtailSent'],
  \ ['error', 'CoqtailError'],
  \ ['omitted', 'CoqtailOmitted']
\]
let s:richpp_hlgroups = {
  \ 'diff.added': 'CoqtailDiffAdded',
  \ 'diff.removed': 'CoqtailDiffRemoved',
  \ 'diff.added.bg': 'CoqtailDiffAddedBg',
  \ 'diff.removed.bg': 'CoqtailDiffRemovedBg'
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

" Return the panels dictionary for buf.
function! s:panels(buf) abort
  return getbufvar(a:buf, 'coqtail_panel_bufs', {})
endfunction

" Open and initialize goal/info panel.
function! s:init(name) abort
  let l:name = a:name . 's'
  let l:bufname = substitute(a:name, '\l', '\u\0', '')

  " badd forces a new buffer to be created in case the main buffer is empty
  execute 'keepjumps badd ' . l:bufname . s:counter
  execute g:coqtail#util#bufchangepre . ' hide edit ' . l:bufname . s:counter
  setlocal buftype=nofile
  execute 'setlocal filetype=coq-' . l:name
  setlocal noswapfile
  setlocal bufhidden=hide
  setlocal nobuflisted
  setlocal nocursorline
  setlocal wrap
  setlocal undolevels=50

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

  " Show saved highlights when the buffer is newly displayed in a window.
  augroup coqtail#RecallHighlights
    autocmd! * <buffer>
    autocmd BufEnter <buffer>
          \ if !exists('w:coqtail_highlights') && exists('b:coqtail_highlights')
          \|  call s:updatehl(bufnr('%'), b:coqtail_highlights)
          \|endif
  augroup END

  " Add panels
  for l:panel in g:coqtail#panels#aux
    let l:coqtail_panel_bufs[l:panel] = s:init(l:panel)
  endfor
  for l:buf in values(l:coqtail_panel_bufs)
    call setbufvar(l:buf, 'coqtail_panel_bufs', l:coqtail_panel_bufs)
  endfor

  " Switch back to main panel
  execute g:coqtail#util#bufchangepre . ' buffer ' . l:main_buf
  call cursor(l:curpos)

  let s:counter += 1
endfunction

" Detect what panel is focused.
function! s:getcurpanel(buf) abort
  for [l:panel, l:buf] in items(s:panels(a:buf))
    if l:buf == a:buf
      return l:panel
    endif
  endfor

  return g:coqtail#panels#none
endfunction

" Return the window ID of a panel.
function! s:panel_winid(buf, panel) abort
  return bufwinid(get(s:panels(a:buf), a:panel, -1))
endfunction

" Attempt to call a function in the context of a panel.
function! s:panel_call(buf, panel, func, args, return) abort
  let l:winid = s:panel_winid(a:buf, a:panel)
  if l:winid != -1
    call coqtail#compat#win_call(l:winid, a:func, a:args, a:return)
  endif
endfunction

" Attempt to switch to a panel from a buffer.
function! s:switch_from(buf, panel) abort
  let l:cur_panel = s:getcurpanel(a:buf)

  if a:panel != l:cur_panel && a:panel != g:coqtail#panels#none
    if !win_gotoid(s:panel_winid(a:buf, a:panel))
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
  if bufwinid(l:buf) == -1 && (a:force || getbufvar(l:buf, 'coqtail_panel_open'))
    " Arrange relative to the first open panel
    for [l:relative, l:dir] in g:coqtail_panel_layout[a:panel]
      if coqtail#panels#switch(l:relative) != g:coqtail#panels#none
        let l:dir = l:dir ==# 'above' ? 'leftabove'
          \ : l:dir ==# 'below' ? 'rightbelow'
          \ : l:dir ==# 'left' ? 'vertical leftabove'
          \ : l:dir ==# 'right' ? 'vertical rightbelow' : ''
        if l:dir !=# ''
          execute printf(g:coqtail#util#bufchangepre . ' %s sbuffer %d', l:dir, l:buf)
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
    let l:winnr = bufwinnr(l:buf)
    let l:size = getbufvar(l:buf, 'coqtail_panel_size')
    if l:size != [-1, -1]
      execute printf('vertical %dresize %d', l:winnr, l:size[0])
      execute printf('%dresize %d', l:winnr, l:size[1])
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

" Clear Rocq highlighting of the current window
function! s:clearhl() abort
  if !exists('w:coqtail_highlights')
    return
  endif
  for [l:var, l:_] in s:hlgroups
    let l:matches = get(w:coqtail_highlights, l:var, [])
    for l:match in l:matches
      call matchdelete(l:match)
    endfor
  endfor
  unlet! w:coqtail_highlights
endfunction

function! coqtail#panels#cleanuphl() abort
  if exists('w:coqtail_highlights') && w:coqtail_highlights['buf'] != bufnr('%')
    call s:clearhl()
  endif
endfunction

" Update highlighting of the current window.
function! s:updatehl(buf, highlights) abort
  call s:clearhl()
  let w:coqtail_highlights = {'buf': a:buf}
  for [l:var, l:grp] in s:hlgroups
    let l:hl = a:highlights[l:var]
    if type(l:hl) == g:coqtail#compat#t_string
      let w:coqtail_highlights[l:var] = [matchadd(l:grp, l:hl, -10)]
    elseif type(l:hl) == g:coqtail#compat#t_list
      " NOTE: add positions one at a time to work around 8-position maximum in
      " older Vims.
      let l:matches = []
      for l:pos in l:hl
        let l:matches = add(l:matches, matchaddpos(l:grp, [l:pos], -10))
      endfor
      let w:coqtail_highlights[l:var] = l:matches
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
    let l:winid = bufwinid(l:buf)
    call setbufvar(l:buf, 'coqtail_panel_open', l:winid != -1)
    call setbufvar(l:buf, 'coqtail_panel_size', [winwidth(l:winid), winheight(l:winid)])
    call setbufvar(l:buf, 'coqtail_panel_richpp', [])
    if l:winid != -1
      let l:toclose = add(l:toclose, l:buf)
    endif
  endfor

  for l:buf in l:toclose
    execute bufwinnr(l:buf) . 'close!'
  endfor
endfunction

" Replace the contents of 'panel' with 'txt'.
" This function must be called in the context of the panel's window.
function! s:replace(panel, txt, richpp, scroll) abort
  " Save the view
  let l:view = winsaveview()

  " Remove previous highlights
  for l:match in b:coqtail_panel_richpp
    call matchdelete(l:match)
  endfor

  " Update buffer text
  let l:old = getline(1, '$') " returns [''] for empty buffer
  let l:old = l:old ==# [''] ? [] : l:old
  if l:old !=# a:txt
    let &l:undolevels = &l:undolevels " explicitly break undo sequence (:h undo-break)
    call coqtail#compat#replacelines(a:txt)
  endif

  " Set new highlights
  let l:matches = []
  for [l:line_no, l:start_pos, l:span, l:hlgroup] in a:richpp
    if has_key(s:richpp_hlgroups, l:hlgroup)
      let l:match = matchaddpos(
        \ s:richpp_hlgroups[l:hlgroup],
        \ [[l:line_no, l:start_pos, l:span]],
        \ -10)
      let l:matches = add(l:matches, l:match)
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
    let l:winids = win_findbuf(a:buf)
    let l:refreshing = getbufvar(a:buf, 'coqtail_refreshing', 0)
    if l:winids == [] || l:refreshing
      return
    endif
    call setbufvar(a:buf, 'coqtail_refreshing', 1)
    let l:cur_winid = win_getid()

    " Update highlighting
    call setbufvar(a:buf, 'coqtail_highlights', a:highlights)
    for l:winid in l:winids
      call coqtail#compat#win_call(
        \ l:winid,
        \ function('s:updatehl'),
        \ [a:buf, a:highlights],
        \ 0)
    endfor

    " Update panels
    for [l:panel, l:panel_data] in items(a:panels)
      let [l:txt, l:richpp] = l:panel_data
      call s:panel_call(
        \ a:buf,
        \ l:panel,
        \ function('s:replace'),
        \ [l:panel, l:txt, l:richpp, a:scroll],
        \ 0)
    endfor
  catch /^Vim:Interrupt$/
  finally
    if !g:coqtail#compat#has_win_execute
      " l:cur_winid might not exist yet
      silent! call win_gotoid(l:cur_winid)
    endif
    call setbufvar(a:buf, 'coqtail_refreshing', 0)
    " NOTE: NeoVim seems to update often enough on its own to make calling
    " `redraw` unnecessary, but skipping it in Vim results in noticeable delays
    " while updating highlighting and text in auxiliary panels delays.
    " See https://github.com/whonore/Coqtail/pull/260.
    if !g:coqtail#compat#nvim
      redraw
    endif
  endtry
endfunction

" Delete panel variables and clear highlighting.
function! coqtail#panels#cleanup() abort
  for l:panel in g:coqtail#panels#aux
    silent! execute 'bwipeout' b:coqtail_panel_bufs[l:panel]
  endfor
  silent! unlet b:coqtail_panel_bufs
  silent! unlet b:coqtail_highlights

  let l:cur_winid = win_getid()
  try
    for l:winid in win_findbuf(bufnr('%'))
      call coqtail#compat#win_call(
        \ l:winid,
        \ function('s:clearhl'),
        \ [],
        \ 0)
    endfor
  catch /^Vim:Interrupt$/
  finally
    if !g:coqtail#compat#has_win_execute
      call win_gotoid(l:cur_winid)
    endif
  endtry
endfunction

" Get the main panel's buffer number.
function! coqtail#panels#getmain() abort
  if exists('b:coqtail_panel_bufs')
    return b:coqtail_panel_bufs.main
  else
    " If b:coqtail_panel_bufs doesn't exist, then the other panels aren't
    " initialized and this must be the main buffer.
    return bufnr('%')
  endif
endfunction

" Getter for variables local to the main buffer
function! coqtail#panels#getvar(var) abort
  return getbufvar(coqtail#panels#getmain(), a:var)
endfunction

" Setter for variables local to the main buffer
function! coqtail#panels#setvar(var, val) abort
  return setbufvar(coqtail#panels#getmain(), a:var, a:val)
endfunction
