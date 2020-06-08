" Author: Wolf Honore
" Python communication channels.

function! coqtail#channel#new() abort
  let l:chan = {'handle': -1}
  for l:f in ['open', 'close', 'status', 'sendexpr', 'evalexpr']
    let l:chan[l:f] = function('s:' . l:f)
  endfor
  return l:chan
endfunction

if g:coqtail#compat#has_channel
  function! s:open(address, options) dict abort
    let self.handle = ch_open(a:address, a:options)
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
else
  " Rate in ms to check if Coqtail is done computing.
  let s:poll_rate = 10

  " Unique session ID.
  let s:session = 0

  function! s:open(address, options) dict abort
    let self.handle = coqtail#compat#pyeval(printf(
      \ 'ChannelManager.open("%s")', a:address
    \))
    return self.handle
  endfunction

  function! s:close() dict abort
    return coqtail#compat#pyeval(printf('ChannelManager.close(%d)', self.handle))
  endfunction

  function! s:status() dict abort
    return coqtail#compat#pyeval(printf('ChannelManager.status(%d)', self.handle))
  endfunction

  function! s:sendexpr(expr, options) dict abort
    echoerr 'Calling ch_sendexpr in synchronous mode.'
  endfunction

  " Send a command to Coqtail and wait for the response.
  function! s:send_wait(handle, session, expr, reply) abort
    let l:returns = a:expr[1] !=# 'interrupt'
    call coqtail#compat#pyeval(printf(
      \ 'ChannelManager.send(%d, %s, %s, reply=%s, returns=bool(%s))',
      \ a:handle,
      \ a:expr[1] !=# 'interrupt' ? a:session : 'None',
      \ json_encode(a:expr),
      \ a:reply != 0 ? a:reply : 'None',
      \ l:returns
    \))

    " Continually check if Coqtail is done computing
    let l:poll = printf('ChannelManager.poll(%d)', a:handle)
    while l:returns
      let l:res = json_decode(coqtail#compat#pyeval(l:poll))
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
          let l:res = s:send_wait(self.handle, l:session, l:val, l:res[-1])
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
