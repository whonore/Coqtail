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
    \ 'See https://github.com/whonore/Coqtail/blob/main/README.md#python-2-support.'
  \)
  finish
endif

py3 from coqtail import CoqtailServer

" Initialize global variables.
" Default number of lines of a goal to show.
let s:goal_lines = 5
" Warning/error messages.
let s:unsupported_msg =
  \ "Coqtail does not officially support your version of Coq (%s).\n" .
  \ 'Continuing with the interface for the latest supported version (%s).'
" Server port.
let s:port = -1

" Default CoqProject file name.
if !exists('g:coqtail_project_names')
  let g:coqtail_project_names = ['_CoqProject']
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

" Patch the given filepath to refer to the source in case dune is used.
function! s:patch_path_for_dune(path) abort
  let l:patched = substitute(a:path, "/_build/default", "", "")
  return l:patched
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
  let l:patched_path = s:patch_path_for_dune(l:path)

  " Try progressively broader searches
  if coqtail#util#qflist_search(b:coqtail_panel_bufs.main, l:patched_path, l:searches)
    " Set usetab instead of opening a new buffer
    let l:swb = &switchbuf
    set switchbuf+=usetab

    let l:item = coqtail#util#preparetagstack()

    " Jump to first if possible, otherwise open list
    try
      execute 'cfirst' . l:bang
      call coqtail#util#pushtagstack(l:item)
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
    let l:patched_path = s:patch_path_for_dune(l:path)
    let l:tag = {'name': a:target, 'filename': l:patched_path, 'cmd': '/\v' . l:search}
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
" `cb` is either 'sync', '', or the name of a `:h channel-callback` with
" msg: string | {'buf': bufnr, 'ret': any}.
" Returns [ok, msg].
function! s:call(cmd, cb, nocoq, args) abort
  if !((a:nocoq && s:initted()) || (!a:nocoq && s:running()))
    return [0, -1]
  endif

  let a:args.opts = {
    \ 'encoding': &encoding,
    \ 'timeout': coqtail#panels#getvar('coqtail_timeout'),
    \ 'filename': expand('#' . b:coqtail_panel_bufs.main . ':p'),
    \ 'stderr_is_warning': g:coqtail_treat_stderr_as_warning
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

" Unlock the buffer if there's no pending command and print any error messages.
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

    " Clear Coqtail highlights when window shows an unrelated buffer.
    augroup coqtail#CleanupHighlights
      autocmd! *
      autocmd BufEnter * call coqtail#panels#cleanuphl()
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
    if b:coqtail_chan.status() !=# 'open'
      call coqtail#util#err(
        \ printf('Failed to connect to Coqtail server at port %d.', s:port))
      return 0
    endif

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

function! coqtail#locate_dune() abort
  let l:files = []
  let l:file = findfile("dune-project", '.;')
  if l:file !=# ''
    return 1
  else
    return 0
  endif
endfunction

" Launch Coqtop and open the auxiliary panels.
function! coqtail#start(...) abort
  if s:running()
    call coqtail#util#warn('Coq is already running.')
  else
    " See comment in coqtail#init() about buffer-local variables
    let b:coqtail_started = coqtail#init()
    if !b:coqtail_started
      call coqtail#stop()
      return 0
    endif

    " Locate CoqProject and dune-project files
    let [b:coqtail_project_files, l:proj_args] = coqtail#coqproject#locate()
    let b:coqtail_in_dune_project = coqtail#locate_dune()

    " Determine which build system to use
    if g:coqtail_build_system == 'prefer-dune'
      let b:coqtail_use_dune = b:coqtail_in_dune_project
    elseif g:coqtail_build_system == 'prefer-coqproject'
      if b:coqtail_project_files == []
        let b:coqtail_use_dune = b:coqtail_in_dune_project
      else
        let b:coqtail_use_dune = 0
      endif
    elseif g:coqtail_build_system == 'dune'
      let b:coqtail_use_dune = 1 
    elseif g:coqtail_build_system == 'coqproject'
      let b:coqtail_use_dune = 0
    else
      " invalid value
      let l:msg = 'Invalid value for config g:coqtail_build_system: '
      let l:msg .= g:coqtail_build_system
      call coqtail#util#err(l:msg)
      call coqtail#stop()
      return 0
    endif

    " Determine the CoqProject args to pass
    if b:coqtail_use_dune
      let l:args = []
    else
      let l:args = map(copy(l:proj_args + a:000), 'expand(v:val)')
    endif

    " Open auxiliary panels
    call coqtail#panels#open(0)

    " Launch Coqtop
    let [l:ok, l:ver_or_msg] = s:call('start', 'sync', 0, {
      \ 'coq_path': expand(coqtail#util#getvar([b:, g:], 'coqtail_coq_path', $COQBIN)),
      \ 'coq_prog': coqtail#util#getvar([b:, g:], 'coqtail_coq_prog', ''),
      \ 'coqproject_args': l:args,
      \ 'use_dune': coqtail#util#getvar([b:], 'coqtail_use_dune', 0),
      \ 'dune_compile_deps': coqtail#util#getvar([b:, g:], 'coqtail_dune_compile_deps', 0)})
    if !l:ok || type(l:ver_or_msg[0]) == g:coqtail#compat#t_string
      let l:msg = 'Failed to launch Coq.'
      if l:ok
        " l:ver_or_msg is [coqtail_error_message, coqtop_stderr]
        let l:msg .= "\n" . l:ver_or_msg[0]
        if l:ver_or_msg[1] !=# ''
          let l:msg .= "\n" . l:ver_or_msg[1]
        endif
      endif
      call coqtail#util#err(l:msg)
      call coqtail#stop()
      return 0
    endif

    " Check if version is supported
    " l:ver_or_msg[0] is
    " {version: [major, minor, patch], str_version: str, latest: str | None}
    let b:coqtail_version = l:ver_or_msg[0]
    if b:coqtail_version.latest != v:null
      call coqtail#util#warn(printf(
        \ s:unsupported_msg,
        \ b:coqtail_version.str_version,
        \ b:coqtail_version.latest))
    endif

    " Draw the logo
    let l:info_winid = bufwinid(b:coqtail_panel_bufs[g:coqtail#panels#info])
    call s:call('splash', 'sync', 0, {
      \ 'version': b:coqtail_version.str_version,
      \ 'width': winwidth(l:info_winid),
      \ 'height': winheight(l:info_winid)})
    call coqtail#refresh()

    call s:init_proof_diffs(b:coqtail_version.str_version)

    " Sync edits to the buffer, close and restore the auxiliary panels
    augroup coqtail#Sync
      autocmd! * <buffer>
      autocmd InsertEnter <buffer> call s:call('sync', 'sync', 0, {})
      autocmd BufWinLeave <buffer> call coqtail#panels#hide()
      autocmd BufWinEnter <buffer>
        \ call coqtail#panels#open(0) | call coqtail#refresh()
      autocmd WinNew <buffer> call coqtail#refresh()
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
function! coqtail#toline(line, admit) abort
  " If no line was given then use the cursor's position,
  " otherwise use the last column in the line
  call s:call('to_line', '', 0, {
    \ 'line': (a:line == 0 ? line('.') : a:line) - 1,
    \ 'col': (a:line == 0 ? col('.') : len(getline(a:line))) - 1,
    \ 'admit': a:admit})
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
    normal! m'
    call cursor(l:pos)
  endif
endfunction

" Refresh the auxiliary panels.
function! coqtail#refresh() abort
  call s:call('refresh', '', 0, {})
endfunction

" Define Coqtail commands with the correct options.
let s:cmd_opts = {
  \ 'CoqStart': '-bar -nargs=* -complete=file',
  \ 'CoqStop': '-bar',
  \ 'CoqInterrupt': '-bar',
  \ 'CoqNext': '-bar -count=1',
  \ 'CoqUndo': '-bar -count=1',
  \ 'CoqToLine': '-bar -count=0',
  \ 'CoqOmitToLine': '-bar -count=0',
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
  call s:cmddef('CoqToLine', 'call coqtail#toline(<count>, 0)', 's')
  call s:cmddef('CoqOmitToLine', 'call coqtail#toline(<count>, 1)', 's')
  call s:cmddef('CoqToTop', 'call s:call("to_top", "", 0, {})', 's')
  call s:cmddef('CoqJumpToEnd', 'call coqtail#jumpto("endpoint")', 's')
  call s:cmddef('CoqJumpToError', 'call coqtail#jumpto("errorpoint")', 's')
  call s:cmddef('CoqGotoDef', 'call coqtail#gotodef(<f-args>, <bang>0)', 's')
  call s:cmddef('Coq', 'call s:call("query", "", 0, {"args": [<f-args>]})', 's')
  call s:cmddef('CoqRestorePanels',
    \ 'call coqtail#panels#open(1) | call coqtail#refresh()', 's')
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
  nnoremap <buffer> <silent> <Plug>CoqOmitToLine :<C-U>execute v:count 'CoqOmitToLine'<CR>
  nnoremap <buffer> <silent> <Plug>CoqToTop :CoqToTop<CR>
  nnoremap <buffer> <silent> <Plug>CoqJumpToEnd :CoqJumpToEnd<CR>
  nnoremap <buffer> <silent> <Plug>CoqJumpToError :CoqJumpToError<CR>
  inoremap <buffer> <silent> <Plug>CoqNext <C-\><C-o>:CoqNext<CR>
  inoremap <buffer> <silent> <Plug>CoqUndo <C-\><C-o>:CoqUndo<CR>
  inoremap <buffer> <silent> <Plug>CoqToLine <C-\><C-o>:CoqToLine<CR>
  inoremap <buffer> <silent> <Plug>CoqOmitToLine <C-\><C-o>:CoqOmitToLine<CR>
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

  let l:maps = {
    \ 'Start': ['c', 'n'],
    \ 'Stop': ['q', 'n'],
    \ 'Interrupt': ['!<C-c>', 'n'],
    \ 'Next': ['j', 'ni'],
    \ 'Undo': ['k', 'ni'],
    \ 'ToLine': ['l', 'ni'],
    \ 'ToTop': ['T', 'ni'],
    \ 'JumpToEnd': ['G', 'ni'],
    \ 'JumpToError': ['E', 'ni'],
    \ 'GotoDef': ['gd', 'n'],
    \ 'Search': ['s', 'nx'],
    \ 'Check': ['h', 'nx'],
    \ 'About': ['a', 'nx'],
    \ 'Print': ['p', 'nx'],
    \ 'Locate': ['f', 'nx'],
    \ 'RestorePanels': ['r', 'ni'],
    \ 'GotoGoalStart': ['gg', 'ni'],
    \ 'GotoGoalEnd': ['gG', 'ni'],
    \ 'GotoGoalNextStart': ['!]g', 'n'],
    \ 'GotoGoalNextEnd': ['!]G', 'n'],
    \ 'GotoGoalPrevStart': ['![g', 'n'],
    \ 'GotoGoalPrevEnd': ['![G', 'n'],
    \ 'ToggleDebug': ['d', 'n']
  \}

  " Use v1.5 mappings
  let l:compat15 = index(get(g:, 'coqtail_version_compat', []), '1.5') != -1
  if l:compat15
    let l:maps15 =  {
      \ 'GotoDef': ['g', 'n'],
      \ 'GotoGoalEnd': ['GG', 'ni'],
      \ 'GotoGoalNextStart': ['!g]', 'n'],
      \ 'GotoGoalNextEnd': ['!G]', 'n'],
      \ 'GotoGoalPrevStart': ['!g[', 'n'],
      \ 'GotoGoalPrevEnd': ['!G[', 'n']
    \}
    let l:maps = extend(l:maps, l:maps15, 'force')
  endif

  for [l:cmd, l:info] in items(l:maps)
    let [l:key, l:types] = l:info
    let l:cmd = '<Plug>Coq' . l:cmd
    for l:type in split(l:types, '\zs')
      if !hasmapto(l:cmd, l:type) && (l:type !=# 'i' || l:imap)
        let l:prefix = l:type ==# 'i' ? l:imap_prefix : l:map_prefix
        if l:key[0] ==# '!'
          let l:key = l:key[1:]
          let l:prefix = ''
        endif
        execute printf('%smap <buffer> %s%s %s', l:type, l:prefix, l:key, l:cmd)
      endif
    endfor
  endfor

  if exists('*CoqtailHookDefineMappings')
    call CoqtailHookDefineMappings()
  endif
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
