" Author: Wolf Honore
" Python communication channels.

function! coqtail#channel#new() abort
  let l:chan = {'handle': -1}
  for l:f in ['open', 'close', 'status', 'sendexpr', 'evalexpr']
    let l:chan[l:f] = function('s:' . l:f)
  endfor
  return l:chan
endfunction

if g:coqtail#compat#has_channel && !g:coqtail#compat#nvim
  function! s:open(address) dict abort
    let l:chanopts = {'mode': 'json', 'timeout': 5000}
    let self.handle = ch_open(a:address, l:chanopts)
    return self.handle
  endfunction

  function! s:close() dict abort
    return ch_close(self.handle)
  endfunction

  function! s:status() dict abort
    return ch_status(self.handle)
  endfunction

  function! s:sendexpr(expr, options) dict abort
    return ch_sendexpr(self.handle, a:expr, a:options)
  endfunction

  function! s:evalexpr(expr, options) dict abort
    return ch_evalexpr(self.handle, a:expr, a:options)
  endfunction
elseif g:coqtail#compat#nvim
  " Rate in ms to check if Coqtail is done computing.
  let s:poll_rate = 10

  " Unique message ID.
  let s:msg_id = 0

  " Coqtail responses to synchronous messages.
  let s:replies_raw = ['']
  let s:replies = {}

  " Callbacks for asynchronous messages.
  let s:callbacks = {}

  function! s:open(address) dict abort
    let l:chanopts = {'on_data': function('s:chanrecv'), 'data_buffered': 0}
    let self.handle = sockconnect('tcp', a:address, l:chanopts)
    return self.handle
  endfunction

  function! s:close() dict abort
    return chanclose(self.handle)
  endfunction

  function! s:status() dict abort
    return nvim_get_chan_info(self.handle) != {} ? 'open' : ''
  endfunction

  function! s:pre_send(expr) abort
    let s:msg_id += 1
    return [s:msg_id, [json_encode([s:msg_id, a:expr]), '']]
  endfunction

  function! s:sendexpr(expr, options) dict abort
    let [l:msg_id, l:msg] = s:pre_send(a:expr)
    let s:callbacks[l:msg_id] = a:options.callback
    call chansend(self.handle, l:msg)
  endfunction

  function! s:evalexpr(expr, options) dict abort
    let [l:msg_id, l:msg] = s:pre_send(a:expr)
    let s:replies[l:msg_id] = {}
    call chansend(self.handle, l:msg)

    " NOTE: only `'timeout': 0` is used now
    if get(a:options, 'timeout', -1) == 0
      return ''
    endif

    while s:replies[l:msg_id] == {}
      execute printf('sleep %dm', s:poll_rate)
    endwhile
    let l:res = s:replies[l:msg_id]
    unlet s:replies[l:msg_id]
    return l:res
  endfunction

  " Handle replies from Coqtail.
  function! s:chanrecv(handle, msg, event) abort
    " Every element of a:msg except the first and last is a complete line and
    " is expected to be valid JSON. The first and last elements may be partial
    " lines where the first is a continuation of the previous last element. By
    " appending the first element of a:msg to the last of s:replies_raw, we
    " guarantee that every element of s:replies_raw except the last one is a
    " complete reply. When the last line of the reply is received,
    " s:replies_raw will be [''].
    let s:replies_raw[-1] .= a:msg[0]
    let s:replies_raw += a:msg[1:]

    " Parse complete replies (all but the last).
    for l:reply in s:replies_raw[:-2]
      let l:res = json_decode(l:reply)
      if l:res[0] ==# 'call'
        let [l:func, l:args; l:msg_id] = l:res[1:]
        let l:val = call(l:func, l:args)
        " Reply only if expected
        if len(l:msg_id) == 1
          call chansend(a:handle, [json_encode([l:msg_id[0], l:val]), ''])
        endif
      else
        let [l:msg_id, l:data] = l:res
        " Return or execute callback
        if has_key(s:replies, l:msg_id)
          let s:replies[l:msg_id] = l:data
        elseif has_key(s:callbacks, l:msg_id)
          call call(s:callbacks[l:msg_id], [a:handle, l:data])
          unlet s:callbacks[l:msg_id]
        endif
      endif
    endfor

    " Remove parsed replies (all but the last).
    let s:replies_raw = [s:replies_raw[-1]]
  endfunction
else
  py3 from coqtail import ChannelManager

  " Rate in ms to check if Coqtail is done computing.
  let s:poll_rate = 10

  " Unique session ID.
  let s:session = 0

  function! s:open(address) dict abort
    let self.handle = py3eval(printf('ChannelManager.open("%s")', a:address))
    return self.handle
  endfunction

  function! s:close() dict abort
    return py3eval(printf('ChannelManager.close(%d)', self.handle))
  endfunction

  function! s:status() dict abort
    return py3eval(printf('ChannelManager.status(%d)', self.handle))
  endfunction

  function! s:sendexpr(expr, options) dict abort
    echoerr 'Calling ch_sendexpr in synchronous mode.'
  endfunction

  " Send a command to Coqtail and wait for the response.
  function! s:send_wait(handle, session, expr, reply_id) abort
    let l:response = a:expr[0] == -1
    let l:returns = l:response || a:expr[1] !=# 'interrupt'

    " In Vim 7.4, json_encode(expand('%')) returns v:null instead of "",
    " which breaks pyeval
    if has_key(a:expr[2], 'opts') && a:expr[2].opts.filename ==# ''
      let a:expr[2].opts.filename = ''
    endif

    call py3eval(printf(
      \ 'ChannelManager.send(%d, %s, %s, reply_id=%s, returns=bool(%s))',
      \ a:handle,
      \ l:returns ? a:session : 'None',
      \ json_encode(l:response ? a:expr[1] : a:expr),
      \ a:reply_id != 0 ? a:reply_id : 'None',
      \ l:returns
    \))

    " Continually check if Coqtail is done computing
    let l:poll = printf('ChannelManager.poll(%d)', a:handle)
    while l:returns
      let l:res = json_decode(py3eval(l:poll))
      if type(l:res) == g:coqtail#compat#t_list
        return l:res
      endif

      execute printf('sleep %dm', s:poll_rate)
    endwhile

    return v:null
  endfunction

  " Send a command to execute and reply to any requests from Coqtail.
  function! s:evalexpr(expr, options) dict abort
    let s:session += 1
    let l:session = s:session
    let l:res = v:null
    let l:did_int = 0

    " Retry until Coqtop responds
    while 1
      try
        let l:res = s:send_wait(self.handle, l:session, a:expr, 0)

        " Handle requests
        while type(l:res) == g:coqtail#compat#t_list && l:res[0] ==# 'call'
          let l:val = call(l:res[1], l:res[2])
          let l:res = s:send_wait(self.handle, l:session, [-1, l:val, {}], l:res[-1])
        endwhile
      catch /^Vim:Interrupt$/
        " Interrupt Coqtop and retry
        if l:did_int
          call coqtail#util#err('Coqtail is stuck. Try restarting to fix.')
          return v:null
        endif
        let l:did_int = 1
        call s:send_wait(self.handle, l:session, [a:expr[0], 'interrupt', {}], 0)
        continue
      endtry

      return type(l:res) == g:coqtail#compat#t_list ? l:res[1] : v:null
    endwhile
  endfunction
endif
