" Author: Wolf Honore
" Coqtail Python interface and window management.

" Only source once.
if exists('g:coqtail_sourced')
  finish
endif
let g:coqtail_sourced = 1

" Check Python version.
if has('python3')
  command! -nargs=1 Py py3 <args>
  function! s:pyeval(expr) abort
    return py3eval(a:expr)
  endfunction
elseif has('python')
  command! -nargs=1 Py py <args>
  function! s:pyeval(expr) abort
    return pyeval(a:expr)
  endfunction
else
  echoerr 'Coqtail requires Python support.'
  finish
endif

" Initialize global variables.
" Supported Coq versions (-1 means any number).
let s:supported = [
  \ [8, 4, -1],
  \ [8, 5, -1],
  \ [8, 6, -1],
  \ [8, 7, -1],
  \ [8, 8, -1],
  \ [8, 9, -1],
  \ [8, 10, -1],
  \ [8, 11, -1]
\]
let s:latest_supported = join(s:supported[-1][:1], '.')
" Unique suffix for auxiliary panel names.
let s:counter = 0
" Panel identifiers.
let s:no_panel = ''
let s:main_panel = 'main'
let s:goal_panel = 'goal'
let s:info_panel = 'info'
let s:aux_panels = [s:goal_panel, s:info_panel]
let s:panels = [s:main_panel] + s:aux_panels
" Default number of lines of a goal to show.
let s:goal_lines = 5
" Warning/error messages.
let s:unsupported_msg =
  \ 'Coqtail does not officially support your version of Coq (%s). ' .
  \ 'Continuing with the interface for the latest supported version (' .
  \ s:latest_supported . ').'
" Server port and channel options.
let s:port = -1
let s:chanopts = {'mode': 'json'}
" Highlighting groups.
let s:hlgroups = [
  \ ['coqtail_checked', 'CoqtailChecked'],
  \ ['coqtail_sent', 'CoqtailSent'],
  \ ['coqtail_error', 'CoqtailError']
\]

" Default Coq path.
if !exists('g:coqtail_coq_path')
  let g:coqtail_coq_path = ''
endif

" Default CoqProject file name.
if !exists('g:coqtail_project_name')
  let g:coqtail_project_name = '_CoqProject'
endif

" Add python directory to path so Python functions can be called.
let s:python_dir = expand('<sfile>:p:h:h') . '/python'
Py import shlex, sys, vim
Py if not vim.eval('s:python_dir') in sys.path:
  \    sys.path.insert(0, vim.eval('s:python_dir'))
Py from coqtail import Coqtail, start_server

" Print a message with warning highlighting.
function! s:warn(msg) abort
  echohl WarningMsg | echom a:msg | echohl None
endfunction

" Print a message with error highlighting.
function! s:err(msg) abort
  echohl ErrorMsg | echom a:msg | echohl None
endfunction

" Find the path corresponding to 'lib'. Used by includeexpr.
function! coqtail#FindLib(lib) abort
  if !s:coqtailRunning()
    return a:lib
  endif
  let [l:ok, l:lib] = s:callCoqtail('find_lib', 'sync', {'lib': a:lib})
  return (l:ok && l:lib != v:null) ? l:lib : a:lib
endfunction

" Open and initialize goal/info panel.
function! s:initPanel(name) abort
  let l:name = a:name . 's'
  let l:bufname = substitute(a:name, '\l', '\u\0', '')

  execute 'silent hide edit ' . l:bufname . s:counter
  setlocal buftype=nofile
  execute 'setlocal filetype=coq-' . l:name
  setlocal noswapfile
  setlocal bufhidden=hide
  setlocal nocursorline
  setlocal wrap

  augroup coqtail#PanelCmd
    autocmd! * <buffer>
    " TODO async: allow closing panel
    autocmd BufWinLeave <buffer> call s:hidePanels()
  augroup END

  return bufnr('%')
endfunction

" Create buffers for the auxiliary panels.
function! s:initPanels() abort
  let l:main_buf = bufnr('%')
  let l:curpos = getcurpos()[1:]
  let l:coqtail_panel_bufs = {s:main_panel: l:main_buf}

  " Add panels
  for l:panel in s:aux_panels
    let l:coqtail_panel_bufs[l:panel] = s:initPanel(l:panel)
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
function! s:checkPanel() abort
  if !exists('b:coqtail_panel_bufs')
    return s:no_panel
  endif

  for [l:panel, l:buf] in items(b:coqtail_panel_bufs)
    if l:buf == bufnr('%')
      return l:panel
    endif
  endfor
endfunction

" Attempt to switch to a panel.
function! s:switchPanel(panel) abort
  let l:cur_panel = s:checkPanel()

  if a:panel != l:cur_panel && a:panel != s:no_panel
    if !win_gotoid(win_getid(bufwinnr(b:coqtail_panel_bufs[a:panel])))
      return s:no_panel
    endif
  endif

  return l:cur_panel
endfunction

" Re-open auxiliary panels.
" TODO async: remember open panels and positions
function! coqtail#OpenPanels() abort
  " Do nothing if windows already open
  for [l:panel, l:buf] in items(b:coqtail_panel_bufs)
    if bufwinnr(l:buf) != -1 && l:panel != s:main_panel
      return
    endif
  endfor

  " Need to save in local vars because will be changing buffers
  let l:goal_buf = b:coqtail_panel_bufs[s:goal_panel]
  let l:info_buf = b:coqtail_panel_bufs[s:info_panel]

  execute 'rightbelow vertical sbuffer ' . l:goal_buf
  execute 'rightbelow sbuffer ' . l:info_buf

  " Switch back to main panel
  call s:switchPanel(s:main_panel)
endfunction

" Clear Coqtop highlighting.
function! s:clearHighlighting() abort
  for [l:var, l:_] in s:hlgroups
    if get(b:, l:var, -1) != -1
      call matchdelete(b:[l:var])
      let b:[l:var] = -1
    endif
  endfor
endfunction

" Replace the contents of 'buf' with 'txt'.
" TODO async: allow different restore behaviors
function! s:replacePanel(buf, txt) abort
  " Switch windows and save the view
  let l:view = winsaveview()

  " Update buffer text
  silent %delete _
  call append(0, a:txt)

  " Restore the view and switch to original window
  call winrestview(l:view)
  call s:scrollPanel()
endfunction

" Refresh the highlighting and auxiliary panels.
" TODO async: main-panel only
function! coqtail#Refresh(buf, highlights, panels) abort
  if a:buf != bufnr('%')
    return
  endif
  let l:win = win_getid()

  " Update highlighting
  call s:clearHighlighting()
  for [l:var, l:grp] in s:hlgroups
    let l:hl = a:highlights[l:var]
    if l:hl != v:null
      let b:[l:var] = matchadd(l:grp, l:hl)
    endif
  endfor

  " Update panels
  for [l:panel, l:txt] in items(a:panels)
    if s:switchPanel(l:panel) != s:no_panel
      call s:replacePanel(b:coqtail_panel_bufs[l:panel], l:txt)
    endif
  endfor
  call win_gotoid(l:win)

  redraw
endfunction

" Close auxiliary panels and clear highlighting.
function! s:hidePanels() abort
  let l:cur_panel = s:checkPanel()
  if l:cur_panel == s:no_panel
    return
  endif

  if l:cur_panel == s:main_panel
    call s:clearHighlighting()
  endif

  " Hide other panels
  for [l:panel, l:buf] in items(b:coqtail_panel_bufs)
    let l:win = bufwinnr(l:buf)
    if l:panel != l:cur_panel && l:win != -1
      execute l:win . 'close!'
    endif
  endfor
endfunction

" Scroll a panel up so text doesn't go off the top of the screen.
function! s:scrollPanel() abort
  " Check if scrolling is necessary
  let l:winh = winheight(0)
  let l:disph = line('w$') - line('w0') + 1

  " Scroll
  if line('w0') != 1 && l:disph < l:winh
    normal! Gz-
  endif
endfunction

" Find the start of the nth goal.
function! s:goalStart(ngoal) abort
  return search('\m^=\+ (' . a:ngoal . ' /', 'nw')
endfunction

" Find the end of the nth goal.
function! s:goalEnd(ngoal) abort
  if s:goalStart(a:ngoal) == 0
    return 0
  endif

  let l:end = s:goalStart(a:ngoal + 1)
  return l:end != 0 ? l:end - 2 : line('$')
endfunction

" Determine the next goal's index.
function! s:goalNext() abort
  let l:goal = search('\m^=\+ (\d', 'nWbc')
  if l:goal == 0
    return 1
  else
    return matchstr(getline(l:goal), '\d\+') + 1
  endif
endfunction

" Determine the previous goal's index.
function! s:goalPrev() abort
  let l:next = s:goalNext()
  return l:next != 1 ? l:next - 2 : 0
endfunction

" Place either the start or end of the nth goal at the bottom of the window.
function! coqtail#GotoGoal(ngoal, start) abort
  let l:panel = s:switchPanel(s:goal_panel)
  if l:panel == s:no_panel
    " Failed to switch to goal panel
    return 0
  endif

  " ngoal = -1: next goal, ngoal = -2: previous goal
  let l:ngoal =
    \ a:ngoal == -1 ? s:goalNext() : a:ngoal == -2 ? s:goalPrev() : a:ngoal

  let l:sline = s:goalStart(l:ngoal)
  let l:eline = s:goalEnd(l:ngoal)
  let l:line = a:start ? l:sline : l:eline
  if l:line != 0
    if a:start
      let l:off = 1 + get(g:, 'coqtail_goal_lines', s:goal_lines)
      let l:line = min([l:line + l:off, l:eline])
    endif
    execute 'normal! ' . l:line . 'zb'
  endif

  call s:switchPanel(l:panel)
endfunction

" Remove entries in the quickfix list with the same position.
function! s:uniqQFList() abort
  let l:qfl = getqflist()
  let l:seen = {}
  let l:uniq = []

  for l:entry in l:qfl
    let l:pos = string([l:entry.lnum, l:entry.col])
    if !has_key(l:seen, l:pos)
      let l:seen[l:pos] = 1
      let l:uniq = add(l:uniq, l:entry)
    endif
  endfor

  call setqflist(l:uniq)
endfunction

" Get a list of possible locations of the definition of 'target'.
function! s:findDef(target) abort
  let [l:ok, l:loc] = s:callCoqtail('find_def', 'sync', {'target': a:target})
  return (!l:ok || type(l:loc) != v:t_list) ? v:null : l:loc
endfunction

" Populate the quickfix list with possible locations of the definition of
" 'target'.
function! coqtail#GotoDef(target, bang) abort
  let l:bang = a:bang ? '!' : ''
  let l:loc = s:findDef(a:target)
  if type(l:loc) != v:t_list
    call s:warn('Cannot locate ' . a:target . '.')
    return
  endif
  let [l:path, l:searches] = l:loc

  " Try progressively broader searches
  let l:found_match = 0
  for l:search in l:searches
    try
      if !l:found_match
        execute 'vimgrep /\v' . l:search . '/j ' . l:path
        let l:found_match = 1
      else
        execute 'vimgrepadd /\v' . l:search . '/j ' . l:path
      endif
    catch /^Vim\%((\a\+)\)\=:E480/
    endtry
  endfor

  if l:found_match
    " Filter duplicate matches
    call s:uniqQFList()

    " Jump to first if possible, otherwise open list
    try
      execute 'cfirst' . l:bang
    catch /^Vim(cfirst):/
      botright cwindow
    endtry
  endif
endfunction

" Create a list of tags for 'target'.
function! coqtail#GetTags(target, flags, info) abort
  let l:loc = s:findDef(a:target)
  if type(l:loc) != v:t_list
    return v:null
  endif
  let [l:path, l:searches] = l:loc

  let l:tags = []
  for l:search in l:searches
    let l:tag = {'name': a:target, 'filename': l:path, 'cmd': '/\v' . l:search}
    let l:tags = add(l:tags, l:tag)
  endfor

  return l:tags
endfunction

" Read a CoqProject file and parse it into options that can be passed to
" Coqtop.
function! coqtail#ParseCoqProj(file, silent) abort
  let l:file_dir = fnamemodify(a:file, ':p:h')
  let l:dir_opts = {'-R': 2, '-Q': 2, '-I': 1, '-include': 1}

  let l:txt = join(readfile(a:file))
  let l:raw_args = s:pyeval(printf('shlex.split(r%s)', string(l:txt)))

  let l:proj_args = []
  let l:idx = 0
  while l:idx < len(l:raw_args)
    " Make paths absolute for -R, -Q, etc
    if has_key(l:dir_opts, l:raw_args[l:idx])
      let l:absdir = l:raw_args[l:idx + 1]
      if l:absdir[0] !=# '/'
        " Join relative paths with 'l:file_dir'
        let l:absdir = join([l:file_dir, l:absdir], '/')
      endif
      let l:raw_args[l:idx + 1] = fnamemodify(l:absdir, ':p')

      " Can be '-R dir -as coqdir' in 8.4
      let l:end = l:idx + l:dir_opts[l:raw_args[l:idx]]
      if l:raw_args[l:end] ==# '-as' || get(l:raw_args, l:end + 1, '') ==# '-as'
        let l:end = l:idx + 3
      endif
      let l:proj_args += l:raw_args[l:idx : l:end]
      let l:idx = l:end
    endif

    " Pass through options following -arg
    if l:raw_args[l:idx] ==# '-arg'
      let l:proj_args = add(l:proj_args, l:raw_args[l:idx + 1])
      let l:idx += 1
    endif

    let l:idx += 1
  endwhile

  return l:proj_args
endfunction

" Search for a CoqProject file using 'g:coqtail_project_name' starting in the
" current directory and recursively try parent directories until '/' is
" reached. Return the file name and a list of arguments to pass to Coqtop.
function! coqtail#FindCoqProj() abort
  let l:proj_args = []
  let l:proj_file = findfile(g:coqtail_project_name, '.;')
  if l:proj_file !=# ''
    let l:proj_args = coqtail#ParseCoqProj(l:proj_file, 0)
  endif

  return [l:proj_file, l:proj_args]
endfunction

" Get the word under the cursor using the special '<cword>' variable. First
" add some characters to the 'iskeyword' option to treat them as part of the
" current word.
function! s:getCurWord() abort
  " Add '.' to definition of a keyword
  let l:old_keywd = &iskeyword
  setlocal iskeyword+=.

  let l:cword = expand('<cword>')

  " Strip trailing '.'s
  let l:dotidx = match(l:cword, '[.]\+$')
  if l:dotidx > -1
    let l:cword = l:cword[: l:dotidx - 1]
  endif

  " Reset iskeyword
  let &l:iskeyword = l:old_keywd

  return l:cword
endfunction

" List query options for use in Coq command completion.
let s:queries = [
  \ 'Search',
  \ 'SearchAbout',
  \ 'SearchPattern',
  \ 'SearchRewrite',
  \ 'SearchHead',
  \ 'Check',
  \ 'Print',
  \ 'About',
  \ 'Locate',
  \ 'Show'
\]
function! s:queryComplete(arg, cmd, cursor) abort
  " Only complete one command
  return len(split(a:cmd)) <= 2 ? join(s:queries, "\n") : ''
endfunction

" Clean up commands, panels, and autocommands.
" TODO async: main-panel only
function! s:cleanup() abort
  " Clean up auxiliary panels
  for l:panel in s:aux_panels
    silent! execute 'bdelete' . b:coqtail_panel_bufs[l:panel]
  endfor
  silent! unlet b:coqtail_panel_bufs

  " Clean up autocmds
  silent! autocmd! coqtail#Autocmds * <buffer>

  " Close the channel
  let b:chan = 0
endfunction

" Get the Coq version and determine if it is supported.
function! s:checkVersion() abort
  " Check that Coq version is supported
  " Assumes message is of the following form:
  " The Coq Proof Assistant, version _._._ (_ _)
  " The 2nd '._' is optional and the 2nd '.' can also be 'pl'. Other text, such
  " as '+beta_' will be stripped and ignored by str2nr()
  let l:coqtop = 'coqtop'
  if b:coqtail_coq_path !=# ''
    let l:coqtop = b:coqtail_coq_path . '/' . l:coqtop
  endif
  let l:version_raw = split(system(l:coqtop . ' --version'))
  let l:version = l:version_raw[index(l:version_raw, 'version') + 1]
  let l:versions = map(split(l:version, '\v(\.|pl)'), 'str2nr(v:val)')

  " Pad missing version numbers with 0
  while len(l:versions) < 3
    let l:versions = add(l:versions, 0)
  endwhile

  let l:found_sup = 0
  for l:supp in s:supported
    let l:is_sup = 1

    for l:idx in range(3)
      if l:supp[l:idx] != l:versions[l:idx] && l:supp[l:idx] != -1
        let l:is_sup = 0
        break
      endif
    endfor

    if l:is_sup
      let l:found_sup = 1
      break
    endif
  endfor

  return [l:version, l:found_sup]
endfunction

" Check if the channel with Coqtail is open.
" TODO async: main-panel only
function! s:coqtailRunning() abort
  try
    return ch_status(b:chan) ==# 'open'
  catch
    return 0
  endtry
endfunction

" Send a request to Coqtail.
" TODO async: main-panel only
function! s:callCoqtail(cmd, cb, args) abort
  if !s:coqtailRunning()
    return [0, -1]
  endif

  let l:args = [bufnr('%'), a:cmd, a:args]
  if a:cb !=# 'sync'
    " Async
    let l:opts = a:cb !=# '' ? {'callback': a:cb} : {'callback': 'coqtail#DefaultCB'}
    return [1, ch_sendexpr(b:chan, l:args, l:opts)]
  else
    " Sync
    let l:res = ch_evalexpr(b:chan, l:args)
    return type(l:res) == v:t_dict
      \ ? [l:res.buf == bufnr('%'), l:res.ret]
      \ : [0, -1]
  endif
endfunction

" Initialize Python interface, commands, autocmds, and auxiliary panels.
function! coqtail#Start(...) abort
  if s:port == -1
    let s:port = s:pyeval('start_server()')
  endif

  if s:coqtailRunning()
    call s:warn('Coq is already running.')
  else
    " Check if version supported
    let [b:coqtail_version, l:supported] = s:checkVersion()
    if !l:supported
      call s:warn(printf(s:unsupported_msg, b:coqtail_version))
    endif

    " Open channel with Coqtail server
    let b:chan = ch_open('localhost:' . s:port, s:chanopts)

    " Check for a Coq project file
    let [b:coqtail_project_file, l:proj_args] = coqtail#FindCoqProj()

    " Prepare auxiliary panels
    call s:initPanels()
    call coqtail#OpenPanels()

    " Launch Coqtop
    let [l:ok, l:msg] = s:callCoqtail('start', 'sync', {
      \ 'version': b:coqtail_version,
      \ 'coq_path': expand(b:coqtail_coq_path),
      \ 'args': map(copy(l:proj_args + a:000), 'expand(v:val)')})
    if !l:ok || l:msg != v:null
      let l:msg = l:msg != v:null : l:msg ? 'Failed to launch Coq.'
      call s:err(l:msg)
      call coqtail#Stop()
      return 0
    endif

    " Draw the logo
    let l:info_win = bufwinnr(b:coqtail_panel_bufs[s:info_panel])
    call s:callCoqtail('splash', 'sync', {
      \ 'version': b:coqtail_version,
      \ 'width': winwidth(l:info_win),
      \ 'height': winheight(l:info_win)})
    call s:callCoqtail('refresh', 'sync', {})

    " Autocmds to do some detection when editing an already checked
    " portion of the code, and to hide and restore the info and goal
    " panels as needed
    augroup coqtail#Autocmds
      autocmd! * <buffer>
      autocmd InsertEnter <buffer> call s:callCoqtail('sync', 'sync', {})
      autocmd BufWinLeave <buffer> call s:hidePanels()
      autocmd BufWinEnter <buffer> call coqtail#OpenPanels() | call s:callCoqtail('refresh', 'sync', {})
      " TODO async: call stop_server
      autocmd QuitPre <buffer> call coqtail#Stop()
    augroup end
  endif

  return 1
endfunction

" Stop the Coqtop interface and clean up auxiliary panels.
function! coqtail#Stop() abort
  call s:callCoqtail('stop', 'sync', {})
  call s:cleanup()
endfunction

" Advance/rewind Coq to the specified position.
function! coqtail#ToLine(line) abort
  " If no line was given then use the cursor's position,
  " otherwise use the last column in the line
  " TODO async: fix on multi-byte characters
  call s:callCoqtail('to_line', '', {
    \ 'line': (a:line == 0 ? line('.') : a:line) - 1,
    \ 'col': (a:line == 0 ? col('.') : len(getline(a:line))) - 1})
endfunction

" Move the cursor to the end of the region checked by Coq.
function! coqtail#JumpToEnd() abort
  let [l:ok, l:pos] = s:callCoqtail('endpoint', 'sync', {})
  if l:ok
    call cursor(l:pos)
  endif
endfunction

" Print any error messages.
function! coqtail#DefaultCB(chan, msg) abort
  if a:msg.ret != v:null
    call s:err(a:msg.ret)
  endif
endfunction

" Define Coqtail commands with the correct options.
let s:cmd_opts = {
  \ 'CoqStart': '-nargs=* -complete=file',
  \ 'CoqStop': '',
  \ 'CoqNext': '-count=1',
  \ 'CoqUndo': '-count=1',
  \ 'CoqToLine': '-count=0',
  \ 'CoqToTop': '',
  \ 'CoqJumpToEnd': '',
  \ 'CoqGotoDef': '-bang -nargs=1',
  \ 'Coq': '-nargs=+ -complete=custom,s:queryComplete',
  \ 'CoqGotoGoal': '-bang -count=1',
  \ 'CoqGotoGoalNext': '-bang',
  \ 'CoqGotoGoalPrev': '-bang',
  \ 'CoqToggleDebug': ''
\}
function! s:cmdDef(name, act) abort
  " Start Coqtail first if needed
  let l:act = a:name !=# 'CoqStart' && a:name !=# 'CoqStop'
    \ ? printf('if s:coqtailRunning() || coqtail#Start() | %s | endif', a:act)
    \ : a:act
  execute printf('command! -buffer -bar %s %s %s', s:cmd_opts[a:name], a:name, l:act)
endfunction

" Define Coqtail commands.
function! s:commands() abort
  call s:cmdDef('CoqStart', 'call coqtail#Start(<f-args>)')
  call s:cmdDef('CoqStop', 'call coqtail#Stop()')
  call s:cmdDef('CoqNext', 'call s:callCoqtail("step", "", {"steps": <count>})')
  call s:cmdDef('CoqUndo', 'call s:callCoqtail("rewind", "", {"steps": <count>})')
  call s:cmdDef('CoqToLine', 'call coqtail#ToLine(<count>)')
  call s:cmdDef('CoqToTop', 'call s:callCoqtail("to_top", "", {})')
  call s:cmdDef('CoqJumpToEnd', 'call coqtail#JumpToEnd()')
  call s:cmdDef('CoqGotoDef', 'call coqtail#GotoDef(<f-args>, <bang>0)')
  call s:cmdDef('Coq', 'call s:callCoqtail("query", "", {"args": [<f-args>]})')
  call s:cmdDef('CoqGotoGoal', 'call coqtail#GotoGoal(<count>, <bang>1)')
  call s:cmdDef('CoqGotoGoalNext', 'call coqtail#GotoGoal(-1, <bang>1)')
  call s:cmdDef('CoqGotoGoalPrev', 'call coqtail#GotoGoal(-2, <bang>1)')
  call s:cmdDef('CoqToggleDebug', 'call s:callCoqtail("toggle_debug", "", {})')
endfunction

" Define <Plug> and default mappings for Coqtail commands.
function! s:mappings() abort
  nnoremap <buffer> <silent> <Plug>CoqStart :CoqStart<CR>
  nnoremap <buffer> <silent> <Plug>CoqStop :CoqStop<CR>
  nnoremap <buffer> <silent> <Plug>CoqNext :<C-U>execute v:count1 'CoqNext'<CR>
  nnoremap <buffer> <silent> <Plug>CoqUndo :<C-U>execute v:count1 'CoqUndo'<CR>
  nnoremap <buffer> <silent> <Plug>CoqToLine :<C-U>execute v:count 'CoqToLine'<CR>
  nnoremap <buffer> <silent> <Plug>CoqToTop :CoqToTop<CR>
  nnoremap <buffer> <silent> <Plug>CoqJumpToEnd :CoqJumpToEnd<CR>
  inoremap <buffer> <silent> <Plug>CoqNext <C-\><C-o>:CoqNext<CR>
  inoremap <buffer> <silent> <Plug>CoqUndo <C-\><C-o>:CoqUndo<CR>
  inoremap <buffer> <silent> <Plug>CoqToLine <C-\><C-o>:CoqToLine<CR>
  inoremap <buffer> <silent> <Plug>CoqToTop <C-\><C-o>:CoqToTop<CR>
  inoremap <buffer> <silent> <Plug>CoqJumpToEnd <C-\><C-o>:CoqJumpToEnd<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoDef :CoqGotoDef <C-r>=<SID>getCurWord()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqSearch :Coq Search <C-r>=<SID>getCurWord()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqCheck :Coq Check <C-r>=<SID>getCurWord()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqAbout :Coq About <C-r>=<SID>getCurWord()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqPrint :Coq Print <C-r>=<SID>getCurWord()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqLocate :Coq Locate <C-r>=<SID>getCurWord()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalStart :<C-U>execute v:count1 'CoqGotoGoal'<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalEnd :<C-U>execute v:count1 'CoqGotoGoal!'<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalNextStart :CoqGotoGoalNext<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalNextEnd :CoqGotoGoalNext!<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalPrevStart :CoqGotoGoalPrev<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalPrevEnd :CoqGotoGoalPrev!<CR>
  nnoremap <buffer> <silent> <Plug>CoqToggleDebug :CoqToggleDebug<CR>

  " Use default mappings unless user opted out
  if exists('g:coqtail_nomap') && g:coqtail_nomap
    return
  endif

  let l:maps = [
    \ ['Start', 'c', 'n'],
    \ ['Stop', 'q', 'n'],
    \ ['Next', 'j', 'ni'],
    \ ['Undo', 'k', 'ni'],
    \ ['ToLine', 'l', 'ni'],
    \ ['ToTop', 'T', 'ni'],
    \ ['JumpToEnd', 'G', 'ni'],
    \ ['GotoDef', 'g', 'n'],
    \ ['Search', 's', 'n'],
    \ ['Check', 'h', 'n'],
    \ ['About', 'a', 'n'],
    \ ['Print', 'p', 'n'],
    \ ['Locate', 'f', 'n'],
    \ ['GotoGoalStart', 'gg', 'ni'],
    \ ['GotoGoalEnd', 'GG', 'ni'],
    \ ['GotoGoalNextStart', '!g]', 'n'],
    \ ['GotoGoalNextEnd', '!G]', 'n'],
    \ ['GotoGoalPrevStart', '!g[', 'n'],
    \ ['GotoGoalPrevEnd', '!G[', 'n'],
    \ ['ToggleDebug', 'd', 'n']
  \]

  for [l:cmd, l:key, l:types] in l:maps
    for l:type in split(l:types, '\zs')
      if !hasmapto('<Plug>Coq' . l:cmd, l:type)
        let l:prefix = '<leader>c'
        if l:key[0] ==# '!'
          let l:key = l:key[1:]
          let l:prefix = ''
        endif
        execute l:type . 'map <buffer> ' . l:prefix . l:key . ' <Plug>Coq' . l:cmd
      endif
    endfor
  endfor
endfunction

" Initialize buffer local variables, commands, and mappings.
function! coqtail#Register() abort
  " Initialize once
  if !exists('b:chan')
    let b:chan = 0
    for [l:var, l:_] in s:hlgroups
      let b:[l:var] = -1
    endfor
    let b:coqtail_timeout = 0
    let b:coqtail_log_name = ''
    if !exists('b:coqtail_coq_path')
      let b:coqtail_coq_path = g:coqtail_coq_path
    endif

    call s:commands()
    call s:mappings()
  endif
endfunction
