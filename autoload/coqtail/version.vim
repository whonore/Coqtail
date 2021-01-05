" Author: Wolf Honore
" Parse and compare version strings.

" Pad xs with x on the right up to length n.
function! s:rpad(xs, x, n) abort
  return a:xs + repeat([a:x], a:n - len(a:xs))
endfunction

" Split a version into components.
" Version is of the form: \d+.\d+((.|pl)\d+|+(alpha|beta|rc)\d+)?
function! s:parse(version) abort
  return s:rpad(split(substitute(a:version, '+.*', '', ''), '\v(\.|pl)'), '0', 3)
endfunction

" Create a list of pairs.
function! s:zip(xs, ys) abort
  return map(copy(a:xs), '[v:val, a:ys[v:key]]')
endfunction

" Check if version matches pattern.
function! coqtail#version#match(version, pattern) abort
  for [l:ver, l:pat] in s:zip(s:parse(a:version), s:parse(a:pattern))
    if !(l:pat ==# '*' || l:pat ==# l:ver)
      return 0
    endif
  endfor

  return 1
endfunction

" Check if version is at least pattern.
function! coqtail#version#atleast(version, pattern) abort
  for [l:ver, l:pat] in s:zip(s:parse(a:version), s:parse(a:pattern))
    if l:pat ==# '*' || l:pat ==# l:ver
      continue
    elseif str2nr(l:pat) < str2nr(l:ver)
      return 1
    else
      return 0
    endif
  endfor

  return 1
endfunction
