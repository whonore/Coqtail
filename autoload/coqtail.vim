" File: coqtail.vim
" Author: Wolf Honore (inspired by/partially adapted from Coquille)
"
" Coquille Credit:
" Copyright (c) 2013, Thomas Refis
"
" Permission to use, copy, modify, and/or distribute this software for any
" purpose with or without fee is hereby granted, provided that the above
" copyright notice and this permission notice appear in all copies.
"
" THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
" REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
" FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
" INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
" LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
" OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
" PERFORMANCE OF THIS SOFTWARE.
"
" Description: Provides an interface to the Python functions in coqtail.py and
" coqtop.py, and manages windows.

" Only source once
if exists('g:coqtail_sourced')
    finish
endif
let g:coqtail_sourced = 1

" Check python version
if has('python')
    command! -nargs=1 Py py <args>
elseif has('python3')
    command! -nargs=1 Py py3 <args>
else
    echoerr 'Coqtail requires python support.'
    finish
endif

" Initialize global variables
let g:counter = 0

" Default CoqProject file name
if !exists('g:coq_proj_file')
    let g:coq_proj_file = '_CoqProject'
endif

" Load vimbufsync if not already done
call vimbufsync#init()

" Add current directory to path so python functions can be called
let s:current_dir = expand('<sfile>:p:h')
Py import sys, vim
Py if not vim.eval('s:current_dir') in sys.path:
\    sys.path.append(vim.eval('s:current_dir'))
Py import coqtail

" Get the word under the cursor using the special '<cword>' variable. First
" add some characters to the 'iskeyword' option to treat them as part of the
" current word.
function! coqtail#GetCurWord()
    " Add '.' and ''' to definition of a keyword
    let l:old_keywd = &iskeyword
    setlocal iskeyword+=.
    setlocal iskeyword+='

    " Check if current word ends in '.' and remove it if so
    let l:cword = expand('<cword>')
    if l:cword =~ '.*[.]$'
        let l:cword = l:cword[:-2]
    endif

    " Reset iskeyword
    let &l:iskeyword = l:old_keywd

    return l:cword
endfunction

" Set the maximum time Coqtail will wait after sending a command before
" interrupting Coqtop.
function! coqtail#SetTimeout()
    let l:old_timeout = b:coq_timeout

    let b:coq_timeout = input('Set timeout to (secs): ')
    echo "\n"

    if b:coq_timeout !~ '^[0-9]\+$' || b:coq_timeout < 0
        echoerr 'Invalid timeout, keeping old value.'
        let b:coq_timeout = l:old_timeout
    elseif b:coq_timeout == 0
        echo 'Timeout of 0 will disable timeout.'
    endif

    let b:coq_timeout = str2nr(b:coq_timeout)
    echo 'timeout=' . b:coq_timeout
endfunction

" Create buffers for the goals and info panels.
function! coqtail#InitPanels()
    let l:coq_buf = bufnr('%')

    " Add goals panel
    execute 'hide edit Goals' . g:counter
    setlocal buftype=nofile
    setlocal filetype=coq-goals
    setlocal noswapfile
    setlocal bufhidden=hide
    setlocal nocursorline
    setlocal wrap
    let b:coq_buf = l:coq_buf  " Assumes buffer number won't change
    let l:goal_buf = bufnr('%')
    augroup coqtail#PanelCmd
        autocmd! * <buffer>
        autocmd BufWinLeave <buffer> call coqtail#HidePanels()
    augroup end

    " Add info panel
    execute 'hide edit Infos' . g:counter
    setlocal buftype=nofile
    setlocal filetype=coq-infos
    setlocal noswapfile
    setlocal bufhidden=hide
    setlocal nocursorline
    setlocal wrap
    let b:coq_buf = l:coq_buf
    let l:info_buf = bufnr('%')
    augroup coqtail#PanelCmd
        autocmd! * <buffer>
        autocmd BufWinLeave <buffer> call coqtail#HidePanels()
    augroup end

    " Switch back to main panel
    execute 'hide edit #' . l:coq_buf
    let b:goal_buf = l:goal_buf
    let b:info_buf = l:info_buf

    Py coqtail.splash(vim.eval('b:version'))
    let g:counter += 1
endfunction

" Reopen goals and info panels and re-highlight.
function! coqtail#OpenPanels()
    let l:coq_win = winnr()

    " Need to save in local vars because will be changing buffers
    let l:goal_buf = b:goal_buf
    let l:info_buf = b:info_buf

    execute 'rightbelow vertical sbuffer ' . l:goal_buf
    execute 'rightbelow sbuffer ' . l:info_buf

    " Switch back to main panel
    execute l:coq_win . 'wincmd w'

    Py coqtail.reset_color()
    Py coqtail.restore_goal()
    Py coqtail.show_info()
endfunction

" Clear Coqtop highlighting.
function! coqtail#ClearHighlight()
    if b:checked != -1
        call matchdelete(b:checked)
        let b:checked = -1
    endif

    if b:sent != -1
        call matchdelete(b:sent)
        let b:sent = -1
    endif

    if b:errors != -1
        call matchdelete(b:errors)
        let b:errors = -1
    endif
endfunction

" Close goal and info panels and clear highlighting.
function! coqtail#HidePanels()
    " If changing files from goal or info buffer
    " N.B. Switching files from anywhere other than the 3 main windows may
    " cause unexpected behaviors
    if exists('b:coq_buf')
        " Do nothing if main window isn't up yet
        if bufwinnr(b:coq_buf) == -1
            return
        endif

        " Switch to main panel and hide as usual
        execute bufwinnr(b:coq_buf) . 'wincmd w'
        call coqtail#HidePanels()
        close!
        return
    endif

    " Hide other panels
    let l:coq_buf = bufnr('%')
    let l:goal_buf = b:goal_buf
    let l:info_buf = b:info_buf

    let l:goal_win = bufwinnr(l:goal_buf)
    if l:goal_win != -1
        execute l:goal_win . 'wincmd w'
        close!
    endif

    let l:info_win = bufwinnr(l:info_buf)
    if l:info_win != -1
        execute l:info_win . 'wincmd w'
        close!
    endif

    let l:coq_win = bufwinnr(l:coq_buf)
    execute l:coq_win . 'wincmd w'

    call coqtail#ClearHighlight()
endfunction

" Scroll a panel up so text doesn't go off the top of the screen.
function! coqtail#ScrollPanel(bufnum)
    " Check if scrolling is necessary
    let l:winh = winheight(0)
    let l:disph = line('w$') - line('w0') + 1

    " Scroll
    if line('w0') != 1 && l:disph < l:winh
        normal Gz-
    endif
endfunction

" Interface to Python query function.
function! coqtail#Query(...)
    Py coqtail.query(*vim.eval('a:000'))
endfunction

" Mappings for Coq queries on the current word.
function! coqtail#QueryMapping()
    map <silent> <leader>cs :Coq SearchAbout <C-r>=expand(coqtail#GetCurWord())<CR>.<CR>
    map <silent> <leader>ch :Coq Check <C-r>=expand(coqtail#GetCurWord())<CR>.<CR>
    map <silent> <leader>ca :Coq About <C-r>=expand(coqtail#GetCurWord())<CR>.<CR>
    map <silent> <leader>cp :Coq Print <C-r>=expand(coqtail#GetCurWord())<CR>.<CR>
    map <silent> <leader>cf :Coq Locate <C-r>=expand(coqtail#GetCurWord())<CR>.<CR>

    map <silent> <leader>co :FindDef <C-r>=expand(coqtail#GetCurWord())<CR><CR>
endfunction

" Mappings for Coqtail commands.
function! coqtail#Mapping()
    map <silent> <leader>cc :CoqStart<CR>
    map <silent> <leader>cq :CoqStop<CR>

    map <silent> <leader>cj :CoqNext<CR>
    map <silent> <leader>ck :CoqUndo<CR>
    map <silent> <leader>cl :CoqToCursor<CR>
    map <silent> <leader>cT :CoqToTop<CR>

    imap <silent> <leader>cj <C-\><C-o>:CoqNext<CR>
    imap <silent> <leader>ck <C-\><C-o>:CoqUndo<CR>
    imap <silent> <leader>cl <C-\><C-o>:CoqToCursor<CR>
    imap <silent> <leader>cT <C-\><C-o>:CoqToTop<CR>

    map <silent> <leader>cG :JumpToEnd<CR>

    map <silent> <leader>cm :MakeMatch <C-r>=input('Inductive type: ')<CR><CR>
    imap <silent> <leader>cm <C-\><C-o>:MakeMatch <C-r>=input('Inductive type: ')<CR><CR>

    map <silent> <leader>ct :call coqtail#SetTimeout()<CR>

    call coqtail#QueryMapping()
endfunction

" Stop the Coqtop interface and clean up goal and info buffers.
function! coqtail#Stop()
    if b:coq_running == 1
        let b:coq_running = 0

        " Stop Coqtop
        try
            Py coqtail.stop()
        catch
        endtry

        " Clean up goal and info buffers
        try
            execute 'bdelete' . b:goal_buf
            execute 'bdelete' . b:info_buf

            unlet b:goal_buf b:info_buf
        catch
        endtry

        " Clean up autocmds
        try
            autocmd! coqtail#Autocmds * <buffer>
        catch
        endtry

        " Unset Coqtail commands
        try
            delcommand CoqStop
            delcommand CoqNext
            delcommand CoqUndo
            delcommand CoqToCursor
            delcommand CoqToTop
            delcommand Coq
            delcommand JumpToEnd
            delcommand FindDef
            delcommand MakeMatch

            command! -buffer -nargs=* Coq echoerr 'Coq is not running.'
        catch
        endtry
    endif
endfunction

" Read a CoqProject file and parse it into options that can be passed to
" Coqtop.
function! coqtail#ParseCoqProj(file)
    let l:proj_args = []
    let l:file_dir = fnamemodify(a:file, ':p:h')

    for l:line in readfile(a:file)
        " Remove any excess whitespace
        let l:line = join(split(l:line, ' '), ' ')

        if line == ''
            continue
        endif

        let l:parts = split(line, ' ')

        " TODO: recognize more options
        if l:parts[0] == '-R'
            " Convert the directory to an absolute path
            let l:absdir = finddir(l:parts[1], l:file_dir)
            if l:absdir != ''
                " Ignore directories that don't exist
                let l:parts[1] = fnamemodify(l:absdir, ':p')
                let l:proj_args = add(l:proj_args, join(l:parts, ' '))
            endif
        endif
    endfor

    return split(join(l:proj_args))
endfunction

" Search for a CoqProject file using 'g:coq_proj_file' starting in the
" current directory and recursively try parent directories until '/' is
" reached. Return a list of arguments to pass to Coqtop.
function! coqtail#FindCoqProj()
    let l:proj_args = []
    let l:proj_file = findfile(g:coq_proj_file, '.;')
    if l:proj_file != ''
        let l:proj_args = coqtail#ParseCoqProj(l:proj_file)
    endif

    return l:proj_args
endfunction

" Initialize Python interface, commands, autocmds, and goals and info panels.
function! coqtail#Start(...)
    " Highlighting for checked parts
    hi default CheckedByCoq ctermbg=17 guibg=LightGreen
    hi default SentToCoq ctermbg=60 guibg=LimeGreen
    hi link CoqError Error

    if b:coq_running == 1
        echo 'Coq is already running.'
    else
        let b:coq_running = 1

        " Check for a Coq project file
        let l:proj_args = coqtail#FindCoqProj()

        " Launch Coqtop
        try
            Py coqtail.start(vim.eval('b:version'),
            \                *vim.eval('map(copy(l:proj_args+a:000),'
            \                          '"expand(v:val)")'))

            " Coqtail commands

            " Stop Coqtail
            command! -buffer CoqStop call coqtail#Stop()

            " Move Coq position
            command! -buffer CoqNext Py coqtail.step()
            command! -buffer CoqUndo Py coqtail.rewind()
            command! -buffer CoqToCursor Py coqtail.to_cursor()
            command! -buffer CoqToTop Py coqtail.to_top()

            " Coq query
            command! -buffer -nargs=* Coq call coqtail#Query(<f-args>)

            " Move cursor
            command! -buffer JumpToEnd Py coqtail.jump_to_end()
            command! -buffer -nargs=1 FindDef Py coqtail.find_def(<f-args>)

            " Insert match template
            command! -buffer -nargs=1 MakeMatch Py coqtail.make_match(<f-args>)

            " Initialize goals and info panels
            call coqtail#InitPanels()
            call coqtail#OpenPanels()

            " Autocmds to do some detection when editing an already checked
            " portion of the code, and to hide and restore the info and goal
            " panels as needed
            augroup coqtail#Autocmds
                autocmd! * <buffer>
                autocmd InsertEnter <buffer> Py coqtail.sync()
                autocmd BufWinLeave <buffer> call coqtail#HidePanels()
                autocmd BufWinEnter <buffer> call coqtail#OpenPanels()
                autocmd QuitPre <buffer> call coqtail#Stop()
            augroup end
        catch /Failed to launch Coq/
            echoerr v:exception
            call coqtail#Stop()
        endtry
    endif
endfunction

" Initialize buffer local variables and the 'CoqStart' command.
function! coqtail#Register(version, supported)
    " Initialize once
    if !exists('b:coq_running')
        let b:coq_running = 0
        let b:checked = -1
        let b:sent    = -1
        let b:errors  = -1
        let b:coq_timeout = 0
        let b:coqtop_done = 0
        let b:version = a:version

        " TODO: find a less hacky solution
        " Define a dummy command for 'Coq' so it does not autocomplete to
        " 'CoqStart' and cause Coqtop to hang
        command! -buffer -nargs=* Coq echoerr 'Coq is not running.'

        if a:supported
            command! -bar -buffer -nargs=* -complete=file CoqStart call coqtail#Start(<f-args>)
        else
            command! -bar -buffer -nargs=* -complete=file CoqStart echoerr 'Coqtail does not support Coq version ' . b:version
        endif
    endif
endfunction
