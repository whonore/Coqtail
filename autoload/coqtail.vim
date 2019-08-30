" Author: Wolf Honore
" Provides an interface to the Python functions in coqtail.py and manages windows.

" Only source once
if exists('g:coqtail_sourced')
  finish
endif
let g:coqtail_sourced = 1

" Check python version
if has('python3')
  command! -nargs=1 Py py3 <args>
  function! s:pyeval(expr) abort
    return function('py3eval', [a:expr])
  endfunction
elseif has('python')
  command! -nargs=1 Py py <args>
  function! s:pyeval(expr) abort
    return function('pyeval', [a:expr])
  endfunction
else
  echoerr 'Coqtail requires python support.'
  finish
endif

" Initialize global variables
let s:counter = 0
"
" Default Coq path
if !exists('g:coqtail_coq_path')
  let g:coqtail_coq_path = ''
endif

" Default CoqProject file name
if !exists('g:coqtail_project_name')
  let g:coqtail_project_name = '_CoqProject'
endif

" Load vimbufsync if not already done
call vimbufsync#init()

" Add python directory to path so python functions can be called
let s:python_dir = expand('<sfile>:p:h:h') . '/python'
Py import sys, vim
Py if not vim.eval('s:python_dir') in sys.path:
\    sys.path.insert(0, vim.eval('s:python_dir'))
Py from coqtail import Coqtail

function! s:warn(msg) abort
  echohl WarningMsg | echom a:msg | echohl None
endfunction

function! s:err(msg) abort
  echohl ErrorMsg | echom a:msg | echohl None
endfunction

" Find the path corresponding to 'lib'. Used by includeexpr.
function! coqtail#FindLib(lib) abort
  return b:coqtail_running
  \ ? s:pyeval("Coqtail().find_lib(vim.eval('a:lib')) or vim.eval('a:lib')")()
  \ : a:lib
endfunction

" Open and initialize goal/info panel.
function! s:initPanel(name, coq_buf) abort
  let l:name_lower = substitute(a:name, '\u', '\l\0', '')

  execute 'hide edit ' . a:name . s:counter
  setlocal buftype=nofile
  execute 'setlocal filetype=coq-' . l:name_lower
  setlocal noswapfile
  setlocal bufhidden=hide
  setlocal nocursorline
  setlocal wrap
  let b:coqtail_coq_buf = a:coq_buf  " Assumes buffer number won't change

  augroup coqtail#PanelCmd
    autocmd! * <buffer>
    autocmd BufWinLeave <buffer> call coqtail#HidePanels()
  augroup end

  return bufnr('%')
endfunction

" Create buffers for the goals and info panels.
function! coqtail#InitPanels() abort
  let l:coq_buf = bufnr('%')
  let l:curpos = getcurpos()[2]

  " Add panels
  let l:goal_buf = s:initPanel('Goals', l:coq_buf)
  let l:info_buf = s:initPanel('Infos', l:coq_buf)

  " Switch back to main panel
  execute 'hide edit #' . l:coq_buf
  call cursor('.', l:curpos)
  let b:coqtail_panel_bufs = {'goal': l:goal_buf, 'info': l:info_buf}

  Py Coqtail().splash(vim.eval('b:coqtail_version'))
  let s:counter += 1
endfunction

" Reopen goals and info panels and re-highlight.
function! coqtail#OpenPanels() abort
  " Do nothing if windows already open
  for l:buf in values(b:coqtail_panel_bufs)
    if bufwinnr(l:buf) != -1
      return
    endif
  endfor

  " Need to save in local vars because will be changing buffers
  let l:coq_win = winnr()
  let l:goal_buf = b:coqtail_panel_bufs.goal
  let l:info_buf = b:coqtail_panel_bufs.info

  execute 'rightbelow vertical sbuffer ' . l:goal_buf
  execute 'rightbelow sbuffer ' . l:info_buf

  " Switch back to main panel
  execute l:coq_win . 'wincmd w'

  Py Coqtail().reset_color()
  Py Coqtail().show_goal()
  Py Coqtail().show_info()
endfunction

" Clear Coqtop highlighting.
function! coqtail#ClearHighlight() abort
  for l:id in ['b:coqtail_checked', 'b:coqtail_sent', 'b:coqtail_errors']
    if eval(l:id) != -1
      call matchdelete(eval(l:id))
      execute 'let ' . l:id . ' = - 1'
    endif
  endfor
endfunction

" Close goal and info panels and clear highlighting.
function! coqtail#HidePanels() abort
  " If changing files from goal or info buffer
  " N.B. Switching files from anywhere other than the 3 main windows may
  " cause unexpected behaviors
  if exists('b:coqtail_coq_buf')
    " Do nothing if main window isn't up yet
    if bufwinnr(b:coqtail_coq_buf) == -1
      return
    endif

    " Switch to main panel and hide as usual
    execute bufwinnr(b:coqtail_coq_buf) . 'wincmd w'
    call coqtail#HidePanels()
    close!
    return
  endif

  " Hide other panels
  let l:coq_buf = bufnr('%')
  for l:buf in values(b:coqtail_panel_bufs)
    let l:win = bufwinnr(l:buf)
    if l:win != -1
      execute l:win . 'wincmd w'
      close!
    endif
  endfor

  let l:coq_win = bufwinnr(l:coq_buf)
  execute l:coq_win . 'wincmd w'

  call coqtail#ClearHighlight()
endfunction

" Scroll a panel up so text doesn't go off the top of the screen.
function! coqtail#ScrollPanel() abort
  " Check if scrolling is necessary
  let l:winh = winheight(0)
  let l:disph = line('w$') - line('w0') + 1

  " Scroll
  if line('w0') != 1 && l:disph < l:winh
    normal! Gz-
  endif
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

" Populate the quickfix list with possible locations of the definition of
" 'target'.
function! coqtail#GotoDef(target, bang) abort
  let l:bang = a:bang ? '!' : ''
  let l:loc = s:pyeval("Coqtail().find_def(vim.eval('a:target')) or []")()
  if l:loc == []
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

" Read a CoqProject file and parse it into options that can be passed to
" Coqtop.
function! coqtail#ParseCoqProj(file, silent) abort
  let l:proj_args = []
  let l:file_dir = fnamemodify(a:file, ':p:h')
  " TODO: recognize more options
  let l:valid_opts = {'-R': 2, '-Q': 2, '-I': 1, '-include': 1}

  " Remove any excess whitespace
  let l:opts = filter(split(join(readfile(a:file)), ' '), 'v:val !=# ""')
  let l:idx = 0

  while l:idx < len(l:opts)
    if has_key(l:valid_opts, l:opts[l:idx])
      let l:absdir = l:opts[l:idx + 1]
      if l:absdir[0] !=# '/'
        " Join relative paths with 'l:file_dir'
        let l:absdir = join([l:file_dir, l:absdir], '/')
      endif

      " Ignore directories that don't exist
      if finddir(l:absdir, l:file_dir) !=# ''
        let l:opts[l:idx + 1] = fnamemodify(l:absdir, ':p')
        let l:end = l:idx + l:valid_opts[l:opts[l:idx]]

        " Can be either '-R dir -as coqdir' or '-R dir coqdir'
        if l:opts[l:end] ==# '-as' || get(l:opts, l:end + 1, '') ==# '-as'
          let l:end = l:idx + 3
        endif

        let l:proj_args = add(l:proj_args, join(l:opts[l:idx : l:end], ' '))
        let l:idx = l:end
      else
        if !a:silent
          call s:warn(l:opts[l:idx + 1] . ' does not exist.')
        endif
      endif
    endif

    let l:idx += 1
  endwhile

  return split(join(l:proj_args))
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
function! s:queryComplete(arg, cmd, cursor) abort
  let l:queries = [
        \'Search', 'SearchAbout', 'SearchPattern', 'SearchRewrite',
        \'SearchHead', 'Check', 'Print', 'About', 'Locate', 'Show'
  \]
  " Only complete one command
  if len(split(a:cmd)) <= 2
    return join(l:queries, "\n")
  else
    return ''
  endif
endfunction

" Define Coqtail commands with the correct options.
let s:cmd_opts = {
  \'CoqStart': '-nargs=* -complete=file',
  \'CoqStop': '',
  \'CoqNext': '-count=1',
  \'CoqUndo': '-count=1',
  \'CoqToLine': '-count=0',
  \'CoqToTop': '',
  \'CoqJumpToEnd': '',
  \'CoqGotoDef': '-bang -nargs=1',
  \'Coq': '-nargs=+ -complete=custom,s:queryComplete',
  \'CoqMakeMatch': '-nargs=1',
  \'CoqToggleDebug': ''
\}
function! s:cmdDef(name, act) abort
  execute printf('command! -buffer -bar %s %s %s', s:cmd_opts[a:name], a:name, a:act)
endfunction

" Define CoqStart and define all other commands to first call it.
function! s:initCommands(supported) abort
  if a:supported
    call s:cmdDef('CoqStart', 'call coqtail#Start(<f-args>)')
    call s:cmdDef('CoqStop', '')
    call s:cmdDef('CoqNext', 'CoqStart | <count>CoqNext')
    call s:cmdDef('CoqUndo', 'CoqStart | <count>CoqUndo')
    call s:cmdDef('CoqToLine', 'CoqStart | <count>CoqToLine')
    call s:cmdDef('CoqToTop', 'CoqStart | CoqToTop')
    call s:cmdDef('CoqJumpToEnd', 'CoqStart | CoqJumpToEnd')
    call s:cmdDef('CoqGotoDef', 'CoqStart | <bang>CoqGotoDef <args>')
    call s:cmdDef('Coq', 'CoqStart | Coq <args>')
    call s:cmdDef('CoqMakeMatch', 'CoqStart | CoqMakeMatch <args>')
    call s:cmdDef('CoqToggleDebug', 'CoqStart | CoqToggleDebug')
  else
    for l:cmd in keys(s:cmd_opts)
      if l:cmd !=# 'CoqStart'
        call s:cmdDef(l:cmd, 'call s:err("Coqtail does not support Coq version " . b:coqtail_version)')
      endif
    endfor
  endif
endfunction

" Initialize commands, panels, and autocommands.
function! s:prepare() abort
  " Commands
  call s:cmdDef('CoqStop', 'call coqtail#Stop()')
  call s:cmdDef('CoqNext', 'Py Coqtail().step(<count>)')
  call s:cmdDef('CoqUndo', 'Py Coqtail().rewind(<count>)')
  call s:cmdDef('CoqToLine', 'Py Coqtail().to_line(<count>)')
  call s:cmdDef('CoqToTop', 'Py Coqtail().to_top()')
  call s:cmdDef('CoqJumpToEnd', 'Py Coqtail().jump_to_end()')
  call s:cmdDef('CoqGotoDef', 'call coqtail#GotoDef(<f-args>, <bang>0)')
  call s:cmdDef('Coq', 'Py Coqtail().query(<f-args>)')
  call s:cmdDef('CoqMakeMatch', 'Py Coqtail().make_match(<f-args>)')
  call s:cmdDef('CoqToggleDebug', 'Py Coqtail().toggle_debug()')

  " Initialize goals and info panels
  call coqtail#InitPanels()
  call coqtail#OpenPanels()

  " Autocmds to do some detection when editing an already checked
  " portion of the code, and to hide and restore the info and goal
  " panels as needed
  augroup coqtail#Autocmds
    autocmd! * <buffer>
    autocmd InsertEnter <buffer> Py Coqtail().sync()
    autocmd BufWinLeave <buffer> call coqtail#HidePanels()
    autocmd BufWinEnter <buffer> call coqtail#OpenPanels()
    autocmd QuitPre <buffer> call coqtail#Stop()
  augroup end
endfunction

" Clean up commands, panels, and autocommands.
function! s:cleanup() abort
  " Clean up goal and info buffers
  try
    for l:buf in values(b:coqtail_panel_bufs)
      execute 'bdelete' . l:buf
    endfor
    unlet b:coqtail_panel_bufs
  catch
  endtry

  " Clean up autocmds
  try
    autocmd! coqtail#Autocmds * <buffer>
  catch
  endtry

  call s:initCommands(1)
endfunction

" Get the Coq version and determine if it is supported.
function! s:checkVersion() abort
  " Supported versions (-1 means any number)
  let l:supported = [
    \[8, 4, -1],
    \[8, 5, -1],
    \[8, 6, -1],
    \[8, 7, -1],
    \[8, 8, -1],
    \[8, 9, -1],
    \[8, 10, -1]
  \]

  " Check that Coq version is supported
  " Assumes message is of the following form:
  " The Coq Proof Assistant, version _._._ (_ _)
  " The 2nd '._' is optional and the 2nd '.' can also be 'pl'. Other text, such
  " as '+beta_' will be stripped and ignored by str2nr()
  let l:coqtop = 'coqtop'
  if b:coqtail_coq_path !=# ''
    let l:coqtop = b:coqtail_coq_path . '/' . l:coqtop
  endif
  let l:version = system(l:coqtop . " --version | awk '/version/{printf \"%s\", $6}'")
  let l:versions = map(split(l:version, '\v(\.|pl)'), 'str2nr(v:val)')

  " Pad missing version numbers with 0
  while len(l:versions) < 3
    let l:versions = add(l:versions, 0)
  endwhile

  let l:found_sup = 0
  for l:supp in l:supported
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

" Initialize Python interface, commands, autocmds, and goals and info panels.
function! coqtail#Start(...) abort
  if b:coqtail_running
    echo 'Coq is already running.'
  else
    " Check if version supported
    let [b:coqtail_version, l:supported] = s:checkVersion()
    if !l:supported
      call s:initCommands(0)
      CoqStop
      return
    endif

    let b:coqtail_running = 1

    " Check for a Coq project file
    let [b:coqtail_project_file, l:proj_args] = coqtail#FindCoqProj()

    " Launch Coqtop
    try
      Py Coqtail().start(vim.eval('b:coqtail_version'),
      \                  vim.eval('expand(b:coqtail_coq_path)'),
      \                  *vim.eval('map(copy(l:proj_args+a:000),'
      \                            '"expand(v:val)")'))

      call s:prepare()
    catch /Failed to launch Coq/
      echoerr v:exception
      call coqtail#Stop()
    endtry
  endif
endfunction

" Stop the Coqtop interface and clean up goal and info buffers.
function! coqtail#Stop() abort
  if b:coqtail_running
    let b:coqtail_running = 0

    " Stop Coqtop
    try
      Py Coqtail().stop()
    catch
    endtry

    call s:cleanup()
  endif
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
  nnoremap <buffer> <silent> <Plug>CoqGotoDef :CoqGotoDef <C-r>=expand(<SID>getCurWord())<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqSearch :Coq SearchAbout <C-r>=expand(<SID>getCurWord())<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqCheck :Coq Check <C-r>=expand(<SID>getCurWord())<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqAbout :Coq About <C-r>=expand(<SID>getCurWord())<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqPrint :Coq Print <C-r>=expand(<SID>getCurWord())<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqLocate :Coq Locate <C-r>=expand(<SID>getCurWord())<CR><CR>
  nnoremap <buffer> <silent> <Plug>CoqToggleDebug :CoqToggleDebug<CR>

  " Use default mappings unless user opted out
  if exists('g:coqtail_nomap') && g:coqtail_nomap
    return
  endif

  let l:maps = [
    \['Start', 'c', 'n'], ['Stop', 'q', 'n'], ['Next', 'j', 'ni'],
    \['Undo', 'k', 'ni'], ['ToLine', 'l', 'ni'], ['ToTop', 'T', 'ni'],
    \['JumpToEnd', 'G', 'ni'], ['GotoDef', 'g', 'n'], ['Search', 's', 'n'],
    \['Check', 'h', 'n'], ['About', 'a', 'n'], ['Print', 'p', 'n'],
    \['Locate', 'f', 'n'], ['ToggleDebug', 'd', 'n']
  \]

  for [l:cmd, l:key, l:types] in l:maps
    for l:type in split(l:types, '\zs')
      if !hasmapto('<Plug>Coq' . l:cmd, l:type)
        execute l:type . 'map <buffer> <leader>c' . l:key . ' <Plug>Coq' . l:cmd
      endif
    endfor
  endfor
endfunction

" Initialize buffer local variables, commands, and mappings.
function! coqtail#Register() abort
  " Initialize once
  if !exists('b:coqtail_running')
    let b:coqtail_running = 0
    let b:coqtail_checked = -1
    let b:coqtail_sent = -1
    let b:coqtail_errors = -1
    let b:coqtail_timeout = 0
    let b:coqtail_coqtop_done = 0
    let b:coqtail_log_name = ''
    if !exists('b:coqtail_coq_path')
      let b:coqtail_coq_path = g:coqtail_coq_path
    endif

    call s:initCommands(1)
    call s:mappings()
  endif
endfunction
