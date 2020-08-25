" Author: Wolf Honore
" Common Coq syntax definitions.

" Highlighting Helpers.
function! s:join(xs, sep) abort
  return type(a:xs) == type([]) ? join(a:xs, a:sep) : a:xs
endfunction

function! s:match(group, pat, opts) abort
  execute printf('syn match %s "%s" %s', a:group, s:join(a:pat, '\|'), a:opts)
endfunction

function! s:region(group, matchgrp, start, end, opts) abort
  let [l:start, l:start_off] = type(a:start) == type([]) ? a:start : [a:start, '']
  let [l:end, l:end_off] = type(a:end) == type([]) ? a:end : [a:end, '']
  let l:grps = type(a:matchgrp) == type([]) ? a:matchgrp : [a:matchgrp, a:matchgrp]
  let [l:sgrp, l:egrp] = map(l:grps, 'v:val !=# "" ? "matchgroup=" . v:val : ""')
  execute printf('syn region %s %s start="%s"%s %s end="%s"%s %s',
    \ a:group, l:sgrp, l:start, l:start_off, l:egrp, l:end, l:end_off, a:opts)
endfunction

" Regex Combinators.
function! s:or(...) abort
  return join(a:000, '\|')
endfunction

function! s:atom(x) abort
  return printf('\<%s\>', a:x)
endfunction

function! s:atoms(...) abort
  return join(map(copy(a:000), 's:atom(v:val)'), '\_s\+')
endfunction

function! s:group(x) abort
  return printf('\%%(%s\)', a:x)
endfunction

function! s:optional(x) abort
  return printf('%s\?', s:group(a:x))
endfunction

let s:helpers = {
  \ 'match': function('s:match'),
  \ 'region': function('s:region'),
  \ 'or': function('s:or'),
  \ 'atom': function('s:atom'),
  \ 'atoms': function('s:atoms'),
  \ 'group': function('s:group'),
  \ 'optional': function('s:optional'),
\}

" Alpha, alphanum groups that include non-ascii characters
let s:helpers.alpha = '[:lower:][:upper:]'
let s:helpers.alphanum = s:helpers.alpha . '[:digit:]'

" Some common patterns
let s:helpers.ident = printf("[_%s][_'%s]*", s:helpers.alpha, s:helpers.alphanum)
let s:helpers.spaces = '\_s\+'
let s:helpers.dot = '\.\_s'
let s:helpers.scope = s:optional('\<' . s:group(s:or('Global', 'Local')) . s:helpers.spaces)

function! g:CoqtailSyntaxHelpers() abort
  return s:helpers
endfunction

" Common Settings.

" N.B. Must be here and not in ftplugin. The Verilog syntax file resets it and
" ftplugin is only sourced once so it is lost when a buffer is reloaded.
" Keywords are alphanumeric, _, and '
setlocal iskeyword=@,48-57,192-255,_,'
syn iskeyword clear

" Coq is case sensitive.
syn case match

" Synchronization
syn sync minlines=50
syn sync maxlines=500

" Common Syntax.
" TODO: move common parts of coq.vim
