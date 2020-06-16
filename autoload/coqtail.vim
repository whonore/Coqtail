" Author: Wolf Honore
" Coqtail Python interface and window management.

" Only source once.
if exists('g:loaded_coqtail')
  finish
endif
let g:loaded_coqtail = 1

let s:python_dir = expand('<sfile>:p:h:h') . '/python'
if !coqtail#compat#init(s:python_dir)
  echoerr 'Coqtail requires Python support.'
  finish
endif

Py from coqtail import ChannelManager, Coqtail, CoqtailServer

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

" Default Coq path.
if !exists('g:coqtail_coq_path')
  let g:coqtail_coq_path = ''
endif

" Default CoqProject file name.
if !exists('g:coqtail_project_name')
  let g:coqtail_project_name = '_CoqProject'
endif

" Find the path corresponding to 'lib'. Used by includeexpr.
function! coqtail#findlib(lib) abort
  let [l:ok, l:lib] = s:call('find_lib', 'sync', {'lib': a:lib})
  return (l:ok && l:lib != v:null) ? l:lib : a:lib
endfunction

" Find the start of the nth goal.
function! s:goal_start(ngoal) abort
  return search('\m^=\+ (' . a:ngoal . ' /', 'nw')
endfunction

" Find the end of the nth goal.
function! s:goal_end(ngoal) abort
  if s:goal_start(a:ngoal) == 0
    return 0
  endif

  let l:end = s:goal_start(a:ngoal + 1)
  return l:end != 0 ? l:end - 2 : line('$')
endfunction

" Determine the next goal's index.
function! s:goal_next() abort
  let l:goal = search('\m^=\+ (\d', 'nWbc')
  if l:goal == 0
    return 1
  else
    return matchstr(getline(l:goal), '\d\+') + 1
  endif
endfunction

" Determine the previous goal's index.
function! s:goal_prev() abort
  let l:next = s:goal_next()
  return l:next != 1 ? l:next - 2 : 0
endfunction

" Place either the start or end of the nth goal at the bottom of the window.
function! coqtail#gotogoal(ngoal, start) abort
  let l:panel = coqtail#panels#switch(g:coqtail#panels#goal)
  if l:panel == g:coqtail#panels#none
    " Failed to switch to goal panel
    return 0
  endif

  " ngoal = -1: next goal, ngoal = -2: previous goal
  let l:ngoal =
    \ a:ngoal == -1 ? s:goal_next() : a:ngoal == -2 ? s:goal_prev() : a:ngoal

  let l:sline = s:goal_start(l:ngoal)
  let l:eline = s:goal_end(l:ngoal)
  let l:line = a:start ? l:sline : l:eline
  if l:line != 0
    if a:start
      let l:off = 1 + get(g:, 'coqtail_goal_lines', s:goal_lines)
      let l:line = min([l:line + l:off, l:eline])
    endif
    execute 'normal! ' . l:line . 'zb'
  endif

  call coqtail#panels#switch(l:panel)
  return 1
endfunction

" Get a list of possible locations of the definition of 'target'.
function! s:finddef(target) abort
  let [l:ok, l:loc] = s:call('find_def', 'sync', {'target': a:target})
  return (!l:ok || type(l:loc) != g:coqtail#compat#t_list) ? v:null : l:loc
endfunction

" Populate the quickfix list with possible locations of the definition of
" 'target'.
function! coqtail#gotodef(target, bang) abort
  let l:bang = a:bang ? '!' : ''
  let l:loc = s:finddef(a:target)
  if type(l:loc) != g:coqtail#compat#t_list
    call coqtail#util#warn('Cannot locate ' . a:target . '.')
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
    call coqtail#util#dedup_qflist()

    " Jump to first if possible, otherwise open list
    try
      execute 'cfirst' . l:bang
    catch /^Vim(cfirst):/
      botright cwindow
    endtry
  endif
endfunction

" Create a list of tags for 'target'.
function! coqtail#gettags(target, flags, info) abort
  let l:loc = s:finddef(a:target)
  if type(l:loc) != g:coqtail#compat#t_list
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
function! s:querycomplete(arg, cmd, cursor) abort
  " Only complete one command
  return len(split(a:cmd)) <= 2 ? join(s:queries, "\n") : ''
endfunction

" Clean up commands, panels, and autocommands.
function! s:cleanup() abort
  " Clean up auxiliary panels
  call coqtail#panels#cleanup()

  " Clean up autocmds
  silent! autocmd! coqtail#Autocmds * <buffer>

  " Close the channel
  silent! call b:coqtail_chan.close()
  let b:coqtail_chan = 0
endfunction

" Get the Coq version and determine if it is supported.
function! s:coqversion() abort
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
function! s:running() abort
  try
    let l:ok = b:coqtail_chan.status() ==# 'open'
  catch
    let l:ok = 0
  finally
    return l:ok
  endtry
endfunction

" Send a request to Coqtail.
function! s:call(cmd, cb, args) abort
  if !s:running()
    return [0, -1]
  endif

  let a:args.opts = {
    \ 'encoding': &encoding,
    \ 'timeout': b:coqtail_timeout,
    \ 'filename': expand('%:p')
  \}
  let l:args = [bufnr('%'), a:cmd, a:args]

  if a:cb !=# 'sync' && g:coqtail#compat#has_channel
    " Async
    let b:cmds_pending += 1
    setlocal nomodifiable
    let l:opts = a:cb !=# '' ? {'callback': a:cb} : {'callback': 'coqtail#defaultCB'}
    return [1, b:coqtail_chan.sendexpr(l:args, l:opts)]
  else
    " Sync
    " Don't wait for interrupt to return
    let l:opts = a:cmd ==# 'interrupt' ? {'timeout': 0} : {}
    let l:res = b:coqtail_chan.evalexpr(l:args, l:opts)
    return type(l:res) == g:coqtail#compat#t_dict
      \ ? [l:res.buf == bufnr('%'), l:res.ret]
      \ : [0, -1]
  endif
endfunction

" Print any error messages.
function! coqtail#defaultCB(chan, msg) abort
  let l:pending = getbufvar(a:msg.buf, 'cmds_pending')
  call setbufvar(a:msg.buf, 'cmds_pending', l:pending - 1)
  if l:pending - 1 == 0
    call setbufvar(a:msg.buf, '&modifiable', 1)
  endif
  if a:msg.ret != v:null
    call coqtail#util#err(a:msg.ret)
  endif
endfunction

" Initialize Python interface, commands, autocmds, and auxiliary panels.
function! coqtail#start(...) abort
  if s:port == -1
    let s:port = coqtail#compat#pyeval(printf(
      \ 'CoqtailServer.start_server(bool(%d))', !g:coqtail#compat#has_channel))
    augroup coqtail#StopServer
      autocmd! *
      autocmd VimLeavePre *
        \ call coqtail#compat#pyeval('CoqtailServer.stop_server()') | let s:port = -1
    augroup END
  endif

  if s:running()
    call coqtail#util#warn('Coq is already running.')
  else
    " Check if version supported
    let [b:coqtail_version, l:supported] = s:coqversion()
    if !l:supported
      call coqtail#util#warn(printf(s:unsupported_msg, b:coqtail_version))
    endif
    let b:cmds_pending = 0

    " Open channel with Coqtail server
    let b:coqtail_chan = coqtail#channel#new()
    call b:coqtail_chan.open('localhost:' . s:port, s:chanopts)

    " Check for a Coq project file
    let [b:coqtail_project_file, l:proj_args] = coqtail#coqproject#locate()

    " Prepare auxiliary panels
    call coqtail#panels#init()
    call coqtail#panels#open(0)

    " Launch Coqtop
    let [l:ok, l:msg] = s:call('start', 'sync', {
      \ 'version': b:coqtail_version,
      \ 'coq_path': expand(b:coqtail_coq_path),
      \ 'args': map(copy(l:proj_args + a:000), 'expand(v:val)')})
    if !l:ok || l:msg != v:null
      let l:msg = l:ok && l:msg != v:null ? l:msg : 'Failed to launch Coq.'
      call coqtail#util#err(l:msg)
      call coqtail#stop()
      return 0
    endif

    " Draw the logo
    let l:info_win = bufwinnr(b:coqtail_panel_bufs[g:coqtail#panels#info])
    call s:call('splash', 'sync', {
      \ 'version': b:coqtail_version,
      \ 'width': winwidth(l:info_win),
      \ 'height': winheight(l:info_win),
      \ 'deprecated': has('python')})
    call s:call('refresh', '', {})

    " Autocmds to do some detection when editing an already checked
    " portion of the code, and to hide and restore the info and goal
    " panels as needed
    augroup coqtail#Autocmds
      autocmd! * <buffer>
      autocmd InsertEnter <buffer> call s:call('sync', 'sync', {})
      autocmd BufWinLeave <buffer> call coqtail#panels#hide()
      autocmd BufWinEnter <buffer>
        \ call coqtail#panels#open(0) | call s:call('refresh', '', {})
      autocmd QuitPre <buffer> call coqtail#stop()
    augroup END
  endif

  return 1
endfunction

" Stop the Coqtop interface and clean up auxiliary panels.
function! coqtail#stop() abort
  call s:call('stop', 'sync', {})
  call s:cleanup()
endfunction

" Advance/rewind Coq to the specified position.
function! coqtail#toline(line) abort
  " If no line was given then use the cursor's position,
  " otherwise use the last column in the line
  " TODO async: fix on multi-byte characters
  call s:call('to_line', '', {
    \ 'line': (a:line == 0 ? line('.') : a:line) - 1,
    \ 'col': (a:line == 0 ? col('.') : len(getline(a:line))) - 1})
endfunction

" Move the cursor to the end of the region checked by Coq.
function! coqtail#jumptoend() abort
  let [l:ok, l:pos] = s:call('endpoint', 'sync', {})
  if l:ok
    call cursor(l:pos)
  endif
endfunction

" Define Coqtail commands with the correct options.
let s:cmd_opts = {
  \ 'CoqStart': '-nargs=* -complete=file',
  \ 'CoqStop': '',
  \ 'CoqInterrupt': '',
  \ 'CoqNext': '-count=1',
  \ 'CoqUndo': '-count=1',
  \ 'CoqToLine': '-count=0',
  \ 'CoqToTop': '',
  \ 'CoqJumpToEnd': '',
  \ 'CoqGotoDef': '-bang -nargs=1',
  \ 'Coq': '-nargs=+ -complete=custom,s:querycomplete',
  \ 'CoqRestorePanels': '',
  \ 'CoqGotoGoal': '-bang -count=1',
  \ 'CoqGotoGoalNext': '-bang',
  \ 'CoqGotoGoalPrev': '-bang',
  \ 'CoqToggleDebug': ''
\}
function! s:cmddef(name, act) abort
  " Start Coqtail first if needed
  let l:act = a:name !~# '\(Start\|Stop\|Interrupt\)$'
    \ ? printf('if s:running() || coqtail#start() | %s | endif', a:act)
    \ : a:act
  execute printf('command! -buffer -bar %s %s %s', s:cmd_opts[a:name], a:name, l:act)
endfunction

" Define Coqtail commands.
function! s:commands() abort
  call s:cmddef('CoqStart', 'call coqtail#start(<f-args>)')
  call s:cmddef('CoqStop', 'call coqtail#stop()')
  call s:cmddef('CoqInterrupt', 'call s:call("interrupt", "sync", {})')
  call s:cmddef('CoqNext', 'call s:call("step", "", {"steps": <count>})')
  call s:cmddef('CoqUndo', 'call s:call("rewind", "", {"steps": <count>})')
  call s:cmddef('CoqToLine', 'call coqtail#toline(<count>)')
  call s:cmddef('CoqToTop', 'call s:call("to_top", "", {})')
  call s:cmddef('CoqJumpToEnd', 'call coqtail#jumptoend()')
  call s:cmddef('CoqGotoDef', 'call coqtail#gotodef(<f-args>, <bang>0)')
  call s:cmddef('Coq', 'call s:call("query", "", {"args": [<f-args>]})')
  call s:cmddef('CoqRestorePanels',
    \ 'call coqtail#panels#open(1) | call s:call("refresh", "", {})')
  call s:cmddef('CoqGotoGoal', 'call coqtail#gotogoal(<count>, <bang>1)')
  call s:cmddef('CoqGotoGoalNext', 'call coqtail#gotogoal(-1, <bang>1)')
  call s:cmddef('CoqGotoGoalPrev', 'call coqtail#gotogoal(-2, <bang>1)')
  call s:cmddef('CoqToggleDebug', 'call s:call("toggle_debug", "", {})')
endfunction

" Define <Plug> and default mappings for Coqtail commands.
function! s:mappings() abort
  nnoremap <buffer> <silent> <Plug>CoqStart :CoqStart<CR>
  nnoremap <buffer> <silent> <Plug>CoqStop :CoqStop<CR>
  nnoremap <buffer> <silent> <Plug>CoqInterrupt :CoqInterrupt<CR>
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
  nnoremap <buffer> <silent> <Plug>CoqGotoDef :CoqGotoDef <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqSearch :Coq Search <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqCheck :Coq Check <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqAbout :Coq About <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqPrint :Coq Print <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqLocate :Coq Locate <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqRestorePanels :CoqRestorePanels<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalStart :<C-U>execute v:count1 'CoqGotoGoal'<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalEnd :<C-U>execute v:count1 'CoqGotoGoal!'<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalNextStart :CoqGotoGoalNext<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalNextEnd :CoqGotoGoalNext!<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalPrevStart :CoqGotoGoalPrev<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoGoalPrevEnd :CoqGotoGoalPrev!<CR>
  nnoremap <buffer> <silent> <Plug>CoqToggleDebug :CoqToggleDebug<CR>

  " Use default mappings unless user opted out
  if get(g:, 'coqtail_nomap', 0)
    return
  endif

  let l:maps = [
    \ ['Start', 'c', 'n'],
    \ ['Stop', 'q', 'n'],
    \ ['Interrupt', '!<C-c>', 'n'],
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
    \ ['RestorePanels', 'r', 'ni'],
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
function! coqtail#register() abort
  " Initialize once
  if !exists('b:coqtail_chan')
    let b:coqtail_chan = 0
    for [l:var, l:_] in g:coqtail#panels#hlgroups
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
