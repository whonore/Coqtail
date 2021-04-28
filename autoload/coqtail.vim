" Author: Wolf Honore
" Coqtail Python interface and window management.

" Only source once.
if exists('g:loaded_coqtail')
  finish
endif
let g:loaded_coqtail = 1

let s:python_dir = expand('<sfile>:p:h:h') . '/python'
let g:coqtail#supported = coqtail#compat#init(s:python_dir)
if !g:coqtail#supported
  call coqtail#util#warn(
    \ "Coqtail requires Python 3.6 or later.\n" .
    \ 'See https://github.com/whonore/Coqtail/blob/master/README.md#python-2-support.'
  \)
  finish
endif

py3 from coqtail import ChannelManager, Coqtail, CoqtailServer

" Initialize global variables.
" Supported Coq versions.
let s:supported = [
  \ '8.4.*',
  \ '8.5.*',
  \ '8.6.*',
  \ '8.7.*',
  \ '8.8.*',
  \ '8.9.*',
  \ '8.10.*',
  \ '8.11.*',
  \ '8.12.*',
  \ '8.13.*'
\]
" Coq binaries to try when checking the version if coqtail_coq_prog is not set.
let s:default_coqs = [
  \ 'coqtop.opt',
  \ 'coqtop',
  \ 'coqidetop.opt',
  \ 'coqidetop',
  \ 'coq-prover.coqidetop'
\]
" Default number of lines of a goal to show.
let s:goal_lines = 5
" Warning/error messages.
let s:unsupported_msg =
  \ "Coqtail does not officially support your version of Coq (%s).\n" .
  \ 'Continuing with the interface for the latest supported version (' .
  \ s:supported[-1] . ').'
" Server port.
let s:port = -1

" Default CoqProject file name.
if !exists('g:coqtail_project_names')
  let g:coqtail_project_names = ['_CoqProject']
endif

" Find the path corresponding to 'lib'. Used by includeexpr.
function! coqtail#findlib(lib) abort
  let [l:ok, l:lib] = s:call('find_lib', 'sync', 0, {'lib': a:lib})
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
  let [l:ok, l:loc] = s:call('find_def', 'sync', 0, {'target': a:target})
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
  if coqtail#util#qflist_search(b:coqtail_panel_bufs.main, l:path, l:searches)
    " Set usetab instead of opening a new buffer
    let l:swb = &switchbuf
    set switchbuf+=usetab

    " Jump to first if possible, otherwise open list
    try
      execute 'cfirst' . l:bang
    catch /^Vim(cfirst):/
      botright cwindow
    endtry

    " Reset switchbuf
    let &switchbuf = l:swb
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
  " Switch back to main buffer for cleanup
  call coqtail#panels#switch(g:coqtail#panels#main)

  " Clean up autocmds
  silent! autocmd! coqtail#Quit * <buffer>
  silent! autocmd! coqtail#Sync * <buffer>

  " Close the channel
  silent! call b:coqtail_chan.close()
  let b:coqtail_chan = 0
  let b:coqtail_started = 0

  " Clean up auxiliary panels
  call coqtail#panels#cleanup()
endfunction

" Get the Coq version and determine if it is supported.
" Only called in coqtail#start(), from main buffer, so we can safely use b:
" vars here.
function! s:coqversion() abort
  " Find a coq(ide)top(.opt) binary
  let l:coq_path = coqtail#util#getvar([b:, g:], 'coqtail_coq_path', '')
  let l:coq = coqtail#util#getvar([b:, g:], 'coqtail_coq_prog', '')
  let l:coqs = l:coq !=# '' ? [l:coq] : s:default_coqs
  let l:ok = 0
  for l:coq in l:coqs
    let l:coq = l:coq_path !=# '' ? l:coq_path . '/' . l:coq : exepath(l:coq)
    if l:coq ==# ''
      continue
    endif
    let l:version_raw = split(system(l:coq . ' --version'))
    let l:ok = !v:shell_error && l:version_raw != []
    if l:ok
      break
    endif
  endfor

  " No binary found
  if !l:ok
    return [-1, 0]
  endif

  " Assumes message is of the form: The Coq Proof Assistant, version _ (_ _)
  let l:version = l:version_raw[index(l:version_raw, 'version') + 1]
  for l:supp in s:supported
    if coqtail#version#match(l:version, l:supp)
      return [l:version, 1]
    endif
  endfor

  return [l:version, 0]
endfunction

" Check if the channel with Coqtail is open.
function! s:initted() abort
  try
    return coqtail#panels#getvar('coqtail_chan').status() ==# 'open'
  catch
    return 0
  endtry
endfunction

" Check if Coqtop has been started.
function! s:running() abort
  try
    return s:initted() && coqtail#panels#getvar('coqtail_started')
  catch
    return 0
  endtry
endfunction

" Send a request to Coqtail.
function! s:call(cmd, cb, nocoq, args) abort
  if !((a:nocoq && s:initted()) || (!a:nocoq && s:running()))
    return [0, -1]
  endif

  let a:args.opts = {
    \ 'encoding': &encoding,
    \ 'timeout': coqtail#panels#getvar('coqtail_timeout'),
    \ 'filename': expand('#' . b:coqtail_panel_bufs.main . ':p')
  \}
  let l:args = [b:coqtail_panel_bufs.main, a:cmd, a:args]

  if a:cb !=# 'sync' && g:coqtail#compat#has_channel
    " Async

    " Increment cmds_pending
    let l:cmds_pending = coqtail#panels#getvar('coqtail_cmds_pending')
    call coqtail#panels#setvar('coqtail_cmds_pending', l:cmds_pending + 1)

    call coqtail#panels#setvar('&modifiable', 0)
    let l:opts = a:cb !=# '' ? {'callback': a:cb} : {'callback': 'coqtail#defaultCB'}
    return [1, coqtail#panels#getvar('coqtail_chan').sendexpr(l:args, l:opts)]
  else
    " Sync
    " Don't wait for interrupt to return
    let l:opts = a:cmd ==# 'interrupt' ? {'timeout': 0} : {}
    let l:res = coqtail#panels#getvar('coqtail_chan').evalexpr(l:args, l:opts)
    return type(l:res) == g:coqtail#compat#t_dict
      \ ? [l:res.buf == b:coqtail_panel_bufs.main, l:res.ret]
      \ : [0, -1]
  endif
endfunction

" Enable proof diffs upon starting.
function! s:init_proof_diffs(coq_version) abort
    let l:proof_diffs_arg = coqtail#util#getvar([b:, g:], 'coqtail_auto_set_proof_diffs', '')
    if l:proof_diffs_arg ==# ''
      return
    endif

    if coqtail#version#atleast(a:coq_version, '8.9.*')
      call s:call('query', '', 0, {
        \ 'args': ['Set', 'Diffs', '"' . l:proof_diffs_arg . '"'],
        \ 'silent': 1})
    endif
endfunction

" Print any error messages.
function! coqtail#defaultCB(chan, msg) abort
  let l:pending = getbufvar(a:msg.buf, 'coqtail_cmds_pending')
  call setbufvar(a:msg.buf, 'coqtail_cmds_pending', l:pending - 1)
  if l:pending - 1 == 0
    call setbufvar(a:msg.buf, '&modifiable', 1)
  endif
  if a:msg.ret != v:null
    call coqtail#util#err(a:msg.ret)
  endif
endfunction

" Initialize Python interface.
function! coqtail#init() abort
  if s:port == -1
    let s:port = py3eval(printf(
      \ 'CoqtailServer.start_server(bool(%d))',
      \ !g:coqtail#compat#has_channel))
    augroup coqtail#StopServer
      autocmd! *
      autocmd VimLeavePre *
        \ call py3eval('CoqtailServer.stop_server()') | let s:port = -1
    augroup END
  endif

  if !s:initted()
    " Since we are initializing, we are in the main buffer;
    " the other buffers have not been initialized yet.
    " Thus, we can safely refer to buffer-local b: variables
    let b:coqtail_cmds_pending = 0

    " Open channel with Coqtail server
    let b:coqtail_chan = coqtail#channel#new()
    call b:coqtail_chan.open('localhost:' . s:port)

    " Prepare auxiliary panels
    call coqtail#panels#init()

    " Shutdown the Coqtop interface when the last instance of this buffer is
    " closed
    augroup coqtail#Quit
      autocmd! * <buffer>
      autocmd QuitPre <buffer>
        \ if len(win_findbuf(expand('<abuf>'))) == 1 | call coqtail#stop() | endif
    augroup END
  endif

  return 1
endfunction

" Launch Coqtop and open the auxiliary panels.
function! coqtail#start(...) abort
  if s:running()
    call coqtail#util#warn('Coq is already running.')
  else
    " See comment in coqtail#init() about buffer-local variables
    let b:coqtail_started = 1
    call coqtail#init()

    " Check if version supported
    let [b:coqtail_version, l:supported] = s:coqversion()
    if !l:supported
      if b:coqtail_version == -1
        call coqtail#util#err(printf(
          \ "No %s binary found.\n" .
          \ 'Check that it exists in your $PATH, or set b:coqtail_coq_path.',
          \ coqtail#util#getvar([b:, g:], 'coqtail_coq_prog', 'coqtop')))
        call coqtail#stop()
        return 0
      else
        call coqtail#util#warn(printf(s:unsupported_msg, b:coqtail_version))
      endif
    endif

    " Locate Coq project files
    let [b:coqtail_project_files, l:proj_args] = coqtail#coqproject#locate()

    " Open auxiliary panels
    call coqtail#panels#open(0)

    " Launch Coqtop
    let [l:ok, l:msg] = s:call('start', 'sync', 0, {
      \ 'version': b:coqtail_version,
      \ 'coq_path': expand(coqtail#util#getvar([b:, g:], 'coqtail_coq_path', '')),
      \ 'coq_prog': coqtail#util#getvar([b:, g:], 'coqtail_coq_prog', ''),
      \ 'args': map(copy(l:proj_args + a:000), 'expand(v:val)')})
    if !l:ok || l:msg != v:null
      let l:msg = l:ok && l:msg != v:null ? l:msg : 'Failed to launch Coq.'
      call coqtail#util#err(l:msg)
      call coqtail#stop()
      return 0
    endif

    " Draw the logo
    let l:info_win = bufwinnr(b:coqtail_panel_bufs[g:coqtail#panels#info])
    call s:call('splash', 'sync', 0, {
      \ 'version': b:coqtail_version,
      \ 'width': winwidth(l:info_win),
      \ 'height': winheight(l:info_win)})
    call s:call('refresh', '', 0, {})

    call s:init_proof_diffs(b:coqtail_version)

    " Sync edits to the buffer, close and restore the auxiliary panels
    augroup coqtail#Sync
      autocmd! * <buffer>
      autocmd InsertEnter <buffer> call s:call('sync', 'sync', 0, {})
      autocmd BufWinLeave <buffer> call coqtail#panels#hide()
      autocmd BufWinEnter <buffer>
        \ call coqtail#panels#open(0) | call s:call('refresh', '', 0, {})
      autocmd WinNew <buffer> call s:call('refresh', '', 0, {})
    augroup END
  endif

  return 1
endfunction

" Stop the Coqtop interface and clean up auxiliary panels.
function! coqtail#stop() abort
  call s:call('stop', 'sync', 1, {})
  call s:cleanup()
endfunction

" Advance/rewind Coq to the specified position.
function! coqtail#toline(line) abort
  " If no line was given then use the cursor's position,
  " otherwise use the last column in the line
  call s:call('to_line', '', 0, {
    \ 'line': (a:line == 0 ? line('.') : a:line) - 1,
    \ 'col': (a:line == 0 ? col('.') : len(getline(a:line))) - 1})
endfunction

" Move the cursor to the specified target:
" - "endpoint": the end of the region checked by Coq
" - "errorpoint": the start of the error region
function! coqtail#jumpto(target) abort
  let l:panel = coqtail#panels#switch(g:coqtail#panels#main)
  if l:panel == g:coqtail#panels#none
    " Failed to switch to main panel
    return
  endif

  let [l:ok, l:pos] = s:call(a:target, 'sync', 0, {})
  if l:ok && type(l:pos) == g:coqtail#compat#t_list
    mark '
    call cursor(l:pos)
  endif
endfunction

" Define Coqtail commands with the correct options.
let s:cmd_opts = {
  \ 'CoqStart': '-bar -nargs=* -complete=file',
  \ 'CoqStop': '-bar',
  \ 'CoqInterrupt': '-bar',
  \ 'CoqNext': '-bar -count=1',
  \ 'CoqUndo': '-bar -count=1',
  \ 'CoqToLine': '-bar -count=0',
  \ 'CoqToTop': '-bar',
  \ 'CoqJumpToEnd': '-bar',
  \ 'CoqJumpToError': '-bar',
  \ 'CoqGotoDef': '-bang -nargs=1',
  \ 'Coq': '-nargs=+ -complete=custom,s:querycomplete',
  \ 'CoqRestorePanels': '-bar',
  \ 'CoqGotoGoal': '-bar -bang -count=1',
  \ 'CoqGotoGoalNext': '-bar -bang',
  \ 'CoqGotoGoalPrev': '-bar -bang',
  \ 'CoqToggleDebug': '-bar'
\}

function! s:cmddef(name, act, precmd) abort
  " Start Coqtail first if needed
  let l:act = {
    \ '_': a:act,
    \ 's': printf('if s:running() || coqtail#start() | %s | endif', a:act),
    \ 'i': printf('if s:initted() || coqtail#init() | %s | endif', a:act)
  \}[a:precmd ==# '' ? '_' : a:precmd]
  execute printf('command! -buffer %s %s %s', s:cmd_opts[a:name], a:name, l:act)
endfunction

" Define Coqtail commands.
function! coqtail#define_commands() abort
  call s:cmddef('CoqStart', 'call coqtail#start(<f-args>)', '')
  call s:cmddef('CoqStop', 'call coqtail#stop()', '')
  call s:cmddef('CoqInterrupt', 'call s:call("interrupt", "sync", 0, {})', '')
  call s:cmddef('CoqNext', 'call s:call("step", "", 0, {"steps": <count>})', 's')
  call s:cmddef('CoqUndo', 'call s:call("rewind", "", 0, {"steps": <count>})', 's')
  call s:cmddef('CoqToLine', 'call coqtail#toline(<count>)', 's')
  call s:cmddef('CoqToTop', 'call s:call("to_top", "", 0, {})', 's')
  call s:cmddef('CoqJumpToEnd', 'call coqtail#jumpto("endpoint")', 's')
  call s:cmddef('CoqJumpToError', 'call coqtail#jumpto("errorpoint")', 's')
  call s:cmddef('CoqGotoDef', 'call coqtail#gotodef(<f-args>, <bang>0)', 's')
  call s:cmddef('Coq', 'call s:call("query", "", 0, {"args": [<f-args>]})', 's')
  call s:cmddef('CoqRestorePanels',
    \ 'call coqtail#panels#open(1) | call s:call("refresh", "", 0, {})', 's')
  call s:cmddef('CoqGotoGoal', 'call coqtail#gotogoal(<count>, <bang>1)', 's')
  call s:cmddef('CoqGotoGoalNext', 'call coqtail#gotogoal(-1, <bang>1)', 's')
  call s:cmddef('CoqGotoGoalPrev', 'call coqtail#gotogoal(-2, <bang>1)', 's')
  call s:cmddef('CoqToggleDebug', 'call s:call("toggle_debug", "", 1, {})', 'i')
endfunction

" Define <Plug> and default mappings for Coqtail commands.
function! coqtail#define_mappings() abort
  nnoremap <buffer> <silent> <Plug>CoqStart :CoqStart<CR>
  nnoremap <buffer> <silent> <Plug>CoqStop :CoqStop<CR>
  nnoremap <buffer> <silent> <Plug>CoqInterrupt :CoqInterrupt<CR>
  nnoremap <buffer> <silent> <Plug>CoqNext :<C-U>execute v:count1 'CoqNext'<CR>
  nnoremap <buffer> <silent> <Plug>CoqUndo :<C-U>execute v:count1 'CoqUndo'<CR>
  nnoremap <buffer> <silent> <Plug>CoqToLine :<C-U>execute v:count 'CoqToLine'<CR>
  nnoremap <buffer> <silent> <Plug>CoqToTop :CoqToTop<CR>
  nnoremap <buffer> <silent> <Plug>CoqJumpToEnd :CoqJumpToEnd<CR>
  nnoremap <buffer> <silent> <Plug>CoqJumpToError :CoqJumpToError<CR>
  inoremap <buffer> <silent> <Plug>CoqNext <C-\><C-o>:CoqNext<CR>
  inoremap <buffer> <silent> <Plug>CoqUndo <C-\><C-o>:CoqUndo<CR>
  inoremap <buffer> <silent> <Plug>CoqToLine <C-\><C-o>:CoqToLine<CR>
  inoremap <buffer> <silent> <Plug>CoqToTop <C-\><C-o>:CoqToTop<CR>
  inoremap <buffer> <silent> <Plug>CoqJumpToEnd <C-\><C-o>:CoqJumpToEnd<CR>
  inoremap <buffer> <silent> <Plug>CoqJumpToError <C-\><C-o>:CoqJumpToError<CR>
  nnoremap <buffer> <silent> <Plug>CoqGotoDef :CoqGotoDef <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqSearch :Coq Search <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqCheck :Coq Check <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqAbout :Coq About <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqPrint :Coq Print <C-r>=coqtail#util#getcurword()<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqLocate :Coq Locate <C-r>=coqtail#util#getcurword()<CR><CR>
  xnoremap <buffer> <silent> <Plug>CoqSearch <ESC>:Coq Search <C-r>=coqtail#util#getvisual()<CR><CR>
  xnoremap <buffer> <silent> <Plug>CoqCheck <ESC>:Coq Check <C-r>=coqtail#util#getvisual()<CR><CR>
  xnoremap <buffer> <silent> <Plug>CoqAbout <ESC>:Coq About <C-r>=coqtail#util#getvisual()<CR><CR>
  xnoremap <buffer> <silent> <Plug>CoqPrint <ESC>:Coq Print <C-r>=coqtail#util#getvisual()<CR><CR>
  xnoremap <buffer> <silent> <Plug>CoqLocate <ESC>:Coq Locate <C-r>=coqtail#util#getvisual()<CR><CR>
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
  let l:imap = !get(g:, 'coqtail_noimap', 0)

  " Use custom mapping prefix if set
  let l:map_prefix = get(g:, 'coqtail_map_prefix', '<leader>c')
  let l:imap_prefix = get(g:, 'coqtail_imap_prefix', l:map_prefix)

  let l:maps = [
    \ ['Start', 'c', 'n'],
    \ ['Stop', 'q', 'n'],
    \ ['Interrupt', '!<C-c>', 'n'],
    \ ['Next', 'j', 'ni'],
    \ ['Undo', 'k', 'ni'],
    \ ['ToLine', 'l', 'ni'],
    \ ['ToTop', 'T', 'ni'],
    \ ['JumpToEnd', 'G', 'ni'],
    \ ['JumpToError', 'E', 'ni'],
    \ ['GotoDef', 'g', 'n'],
    \ ['Search', 's', 'nx'],
    \ ['Check', 'h', 'nx'],
    \ ['About', 'a', 'nx'],
    \ ['Print', 'p', 'nx'],
    \ ['Locate', 'f', 'nx'],
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
      if !hasmapto('<Plug>Coq' . l:cmd, l:type) && (l:type !=# 'i' || l:imap)
        let l:prefix = l:type ==# 'i' ? l:imap_prefix : l:map_prefix
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
" Called from ftplugin/coq.vim, from the main buffer, meaning we can safely
" refer to b: vars here.
function! coqtail#register() abort
  " Initialize once
  if !exists('b:coqtail_chan')
    let b:coqtail_chan = 0
    let b:coqtail_started = 0
    let b:coqtail_timeout = 0
    let b:coqtail_log_name = ''

    " Only define commands + mappings for main buffer for now;
    " these will be redefined for the goal and info buffers
    " when those are created (when :CoqStart is called)
    call coqtail#define_commands()
    call coqtail#define_mappings()
  endif
endfunction
