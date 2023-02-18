" Author: Wolf Honore
" LSP configuration.

let s:lsp_server_name = 'coq-lsp'

let s:goal_timer = -1
let s:goal_delay = 100
let s:progress_delay = 100

function! s:register_lsp() abort
  call lsp#register_server({
    \ 'name': s:lsp_server_name,
    \ 'cmd': {server_info -> ['coq-lsp']},
    \ 'root_uri': {server_info -> lsp#utils#path_to_uri(
      \ lsp#utils#find_nearest_parent_file_directory(
        \ lsp#utils#get_buffer_path(),
        \ ['.git/', '_CoqProject', 'Makefile.coq', 'dune-project']
      \)
    \)},
    \ 'allowlist': ['coq']
  \})

  " Listen for `$/coq/fileProgress`
  call lsp#callbag#pipe(
    \ lsp#stream(),
    \ lsp#callbag#filter({msg ->
      \ has_key(msg, 'response')
      \ && !has_key(msg['response'], 'error')
      \ && get(msg['response'], 'method', '') == '$/coq/fileProgress'
    \}),
    \ lsp#callbag#debounceTime(s:progress_delay),
    \ lsp#callbag#map({msg -> msg.response.params.processing}),
    \ lsp#callbag#subscribe({'next': function('s:on_file_progress')}),
  \)
endfunction

function s:parse_goals(goals)
  if a:goals == v:null
    return []
  endif

  " Translation of python/coqtail.py:pp_goals
  let l:lines = []

  let l:ngoals = len(a:goals.goals)
  let l:nhidden = a:goals.stack != [] ? len(a:goals.stack[0][0] + a:goals.stack[0][1]) : 0
  let l:nshelved = len(a:goals.shelf)
  let l:nadmit = len(a:goals.given_up)

  " Information about number of remaining goals
  let l:lines = add(l:lines, printf('%d subgoal%s', l:ngoals, l:ngoals == 1 ? '' : 's'))
  if l:nhidden > 0
    let l:lines = add(l:lines, printf('(%d unfocused at this level)', l:nhidden))
  endif
  if l:nshelved > 0 || l:nadmit > 0
    let l:line = []
    if l:nshelved > 0
      let l:line = add(l:line, printf('%d shelved', l:nshelved))
    endif
    if l:nadmit > 0
      let l:line = add(l:line, printf('%d admitted', l:nadmit))
    endif
    let l:lines = add(l:lines, join(l:line, ' '))
  endif

  let l:lines = add(l:lines, '')

  " When a subgoal is finished
  if l:ngoals == 0
    let l:next_goal = v:null
    for [_, l:nexts] in a:goals.stack
      if l:nexts != []
        let l:next_goal = l:nexts[0]
        break
      endif
    endfor

    if l:next_goal != v:null
      let l:bullet = a:goals.bullet
      let l:next_info = 'Next goal'
      if l:next_goal.info.name != v:null
        let l:next_info .= printf(' [%s]', l:next_goal.info.name)
      endif
      if l:bullet != v:null
        let l:bullet = substitute(l:bullet, '\.$', '', '')
        let l:next_info .= printf(' (%s)', l:bullet)
      endif
      let l:next_info .= ':'

      let l:lines += [l:next_info, '']
      let l:lines += split(l:next_goal.ty, '\n')
    else
      let l:lines = add(l:lines, 'All goals completed.')
    endif
  endif

  for l:idx in range(len(a:goals.goals))
    let l:goal = a:goals.goals[l:idx]
    if l:idx == 0
      " Print the environment only for the current goal
      for l:hyp in l:goal.hyps
        let l:line = printf('%s : %s', join(l:hyp.names, ', '), l:hyp.ty)
        if l:hyp.def != v:null
          let l:line .= printf(' := %s', l:hyp.def)
        endif
        let l:lines = add(l:lines, l:line)
      endfor
    endif

    let l:hbar = printf('%s (%d / %d)', repeat('=', 25), l:idx + 1, l:ngoals)
    if l:goal.info.name != v:null
      let l:hbar .= printf(' [%s]', l:goal)
    endif
    let l:lines += ['', l:hbar, '']

    let l:lines += split(l:goal.ty, '\n')
  endfor

  return l:lines
endfunction

function s:parse_messages(msgs)
  if a:msgs == v:null
    return []
  endif

  let l:lines = []
  for l:msg in a:msgs
    let l:lines = add(l:lines, l:msg.text)
  endfor

  return l:lines
endfunction

function s:on_goals(response) abort
  let l:goal = [s:parse_goals(a:response.response.result.goals), []]
  let l:info = [s:parse_messages(a:response.response.result.messages), []]
  if l:goal[0] != [] || l:info[0] != []
    call coqtail#panels#open(1)
    call coqtail#panels#refresh(bufnr('%'), {}, {'goal': l:goal, 'info': l:info}, 0)
  else
    call coqtail#panels#hide()
  endif
endfunction

function! s:get_goals() abort
  call lsp#send_request(s:lsp_server_name, {
    \ 'method': 'proof/goals',
    \ 'params': {
      \ 'textDocument': lsp#get_text_document_identifier(),
      \ 'position': lsp#get_position()
    \},
    \ 'on_notification': function('s:on_goals')
  \})
endfunction

function! s:schedule_goals() abort
  call timer_stop(s:goal_timer)
  let s:goal_timer = timer_start(s:goal_delay, {_ -> s:get_goals()})
endfunction

function s:match_from_pos(sline, scol, eline, ecol) abort
  let l:match = []
  for l:line in range(a:sline, a:eline)
    let l:col = l:line == a:sline ? a:scol : 1
    let l:span = l:line == a:eline ? a:ecol - l:col : len(getline(l:line)) - l:col
    let l:match = add(l:match, [l:line, l:col, l:span])
  endfor
  return l:match
endfunction

function! s:on_file_progress(processing) abort
  let l:hls = {
    \ 'coqtail_checked': [],
    \ 'coqtail_sent': [],
    \ 'coqtail_error': [],
    \ 'coqtail_omitted': []
  \}

  for l:info in a:processing
    let [l:sline, l:scol] = lsp#utils#position#lsp_to_vim('%', l:info.range.start)
    let [l:eline, l:ecol] = lsp#utils#position#lsp_to_vim('%', l:info.range.end)
    if l:info.kind == 1
      let l:hls.coqtail_sent += s:match_from_pos(l:sline, l:scol, l:eline, l:ecol)
    elseif l:info.kind == 2
      let l:hls.coqtail_error += s:match_from_pos(l:sline, l:scol, l:eline, l:ecol)
    endif
  endfor

  call coqtail#panels#refresh(bufnr('%'), l:hls, {}, 0)
endfunction

function! s:register_commands() abort
  command! -buffer CoqGoals call <sid>get_goals()
  augroup coqtail_goals
    autocmd! *
    autocmd CursorMoved <buffer> call s:schedule_goals()
    autocmd CursorMovedI <buffer> call s:schedule_goals()
  augroup END
endfunction

function coqtail#lsp#init() abort
  if executable('coq-lsp')
    augroup coqtail_coq_lsp
      autocmd! *
      autocmd User lsp_setup call s:register_lsp()
      autocmd User lsp_buffer_enabled call s:register_commands()
    augroup END
  endif
endfunction
