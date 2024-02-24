" Author: Wolf Honore
" Locate and parse _CoqProject files.

" Parser adapted from https://github.com/coq/coq/blob/v8.19/lib/coqProject_file.ml.

function! s:parse_skip_comment(s) abort
  let l:s = a:s
  while !empty(l:s)
    let l:c = l:s[0]
    let l:s = l:s[1:]
    if l:c ==# "\n"
      break
    endif
  endwhile
  return l:s
endfunction

function! s:parse_string2(s) abort
  let l:buf = ''
  let l:s = a:s
  while !empty(l:s)
    let l:c = l:s[0]
    let l:s = l:s[1:]
    if l:c ==# '"'
      break
    else
      let l:buf .= l:c
    endif
  endwhile
  return [l:s, l:buf]
endfunction

function! s:parse_string(s) abort
  let l:buf = ''
  let l:s = a:s
  while !empty(l:s)
    let l:c = l:s[0]
    let l:s = l:s[1:]
    if l:c ==# ' ' || l:c ==# "\r" || l:c ==# "\n" || l:c ==# "\t"
      break
    elseif l:c ==# '#'
      let l:s = s:parse_skip_comment(l:s)
    else
      let l:buf .= l:c
    endif
  endwhile
  return [l:s, l:buf]
endfunction

function! s:parse_args(s) abort
  let l:accu = []
  let l:s = a:s
  while !empty(l:s)
    let l:c = l:s[0]
    let l:s = l:s[1:]
    if l:c ==# ' ' || l:c ==# "\r" || l:c ==# "\n" || l:c ==# "\t"
    elseif l:c ==# '#'
      let l:s = s:parse_skip_comment(l:s)
    elseif l:c ==# '"'
      let [l:s, l:str] = s:parse_string2(l:s)
      let l:accu = add(l:accu, l:str)
    else
      let [l:s, l:str] = s:parse_string(l:s)
      let l:accu = add(l:accu, l:c . l:str)
    endif
  endwhile
  return l:accu
endfunction

function! s:process_extra_args(arg) abort
  let l:out_list = []
  let l:arg = a:arg
  let l:inside_quotes = 0
  let l:has_leftovers = 0
  let l:buf = ''
  while !empty(l:arg)
    let l:c = l:arg[0]
    let l:arg = l:arg[1:]
    if l:c ==# "'"
      let l:inside_quotes = !l:inside_quotes
      let l:has_leftovers = 1
    elseif l:c ==# ' '
      if l:inside_quotes
        let l:has_leftovers = 1
        let l:buf .= ' '
      elseif l:has_leftovers
        let l:has_leftovers = 0
        let l:out_list = add(l:out_list, l:buf)
        let l:buf = ''
      endif
    else
      let l:has_leftovers = 1
      let l:buf .= l:c
    endif
  endwhile
  if l:has_leftovers
    let l:out_list = add(l:out_list, l:buf)
  endif
  return l:out_list
endfunction

" Parse a _CoqProject file into options that can be passed to Coqtop.
function! coqtail#coqproject#parse(file) abort
  let l:dir = fnamemodify(a:file, ':p:h')
  let l:dir_opts = {'-R': 2, '-Q': 2, '-I': 1, '-include': 1}

  let l:txt = join(readfile(a:file), "\n")
  let l:raw_args = s:parse_args(l:txt)

  let l:proj_args = []
  let l:idx = 0
  while l:idx < len(l:raw_args)
    " Make paths absolute for -R, -Q, etc
    if has_key(l:dir_opts, l:raw_args[l:idx])
      let l:absdir = l:raw_args[l:idx + 1]
      if l:absdir[0] !=# '/'
        " Join relative paths with 'l:dir'
        let l:absdir = join([l:dir, l:absdir], '/')
      endif
      let l:raw_args[l:idx + 1] = fnamemodify(l:absdir, ':p')

      " Can be '-R dir -as coqdir' in 8.4
      let l:end = l:idx + l:dir_opts[l:raw_args[l:idx]]
      if l:raw_args[l:end] ==# '-as' || get(l:raw_args, l:end + 1, '') ==# '-as'
        let l:end = l:idx + 3
      endif
      let l:proj_args += l:raw_args[l:idx : l:end]
      let l:idx = l:end
    endif

    " Pass through options following -arg
    if l:raw_args[l:idx] ==# '-arg'
      let l:proj_args += s:process_extra_args(l:raw_args[l:idx + 1])
      let l:idx += 1
    endif

    let l:idx += 1
  endwhile

  return l:proj_args
endfunction

" Find Coq project files in 'g:coqtail_project_names' searching upwards from
" the current directory. Return the file names and a list of arguments to pass
" to Coqtop.
function! coqtail#coqproject#locate() abort
  let l:files = []
  let l:args = []
  for l:proj in g:coqtail_project_names
    let l:file = findfile(l:proj, '.;')
    if l:file !=# ''
      let l:files = add(l:files, l:file)
      let l:args += coqtail#coqproject#parse(l:file)
    endif
  endfor
  return [l:files, l:args]
endfunction
