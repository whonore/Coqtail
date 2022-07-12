" Vim indent file
" Language:     Coq
" Maintainer: 	Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Thanks:       Some functions were inspired by the ocaml indent file
"               written by Jean-Francois Yuen, Mike Leary and Markus Mottl
" Last Change: 2007 Dec 2  - Bugfix.
"              2007 Nov 28 - Handle proofs that do not start with 'Proof'.
"              2007 Nov 27 - Initial version.
" Modified By: Wolf Honore

" Only load this indent file when no other was loaded and user didn't opt out.
if exists('b:did_indent') || get(g:, 'coqtail_noindent', 0)
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetCoqIndent()
setlocal indentkeys=o,O,0=end,0=End,0=in,0=\|,0=Qed,0=Defined,0=Abort,0=Admitted,0},0),0-,0+,0<*>,0--,0++,0<*><*>,0---,0+++,0<*><*><*>
if get(g:, 'coqtail_indent_on_dot', 0)
  setlocal indentkeys+=.
endif
setlocal expandtab
setlocal nolisp
setlocal nosmartindent
setlocal shiftwidth=2
setlocal tabstop=2

let b:undo_indent = 'setl et< inde< indk< lisp< si< sw< ts<'

" Only define the function once.
if exists('*GetCoqIndent')
  finish
endif

" Some useful patterns
let s:vernac = '\C\<\%(Abort\|About\|Add\|Admitted\|Arguments\|Axiom\|Back\|Bind\|Canonical\|Cd\|Check\|Class\|Close\|Coercion\|CoFixpoint\|CoInductive\|Combined\|Conjecture\|Context\|Corollary\|Declare\|Defined\|Definition\|Delimit\|Derive\|Drop\|End\|Eval\|Example\|Existential\|Export\|Extract\|Extraction\|Fact\|Fixpoint\|Focus\|Function\|Functional\|Goal\|Hint\|Hypothes[ie]s\|Identity\|Implicit\|Import\|Inductive\|Infix\|Inspect\|Lemma\|Let\|Load\|Locate\|Ltac\|Module\|Mutual\|Notation\|Opaque\|Open\|Parameters\=\|Print\|Program\|Proof\|Proposition\|Pwd\|Qed\|Quit\|Record\|Recursive\|Remark\|Remove\|Require\|Reserved\|Reset\|Restart\|Restore\|Resume\|Save\|Scheme\|Search\%(About\|Pattern\|Rewrite\)\=\|Section\|Set\|Show\|Structure\|SubClass\|Suspend\|Tactic\|Test\|Theorem\|Time\|Transparent\|Undo\|Unfocus\|Unset\|Variables\?\|Whelp\|Write\)\>'
let s:tactic = '\C\<\%(absurd\|apply\|assert\|assumption\|auto\|case_eq\|change\|clear\%(body\)\?\|cofix\|cbv\|compare\|compute\|congruence\|constructor\|contradiction\|cut\%(rewrite\)\?\|decide\|decompose\|dependent\|destruct\|discriminate\|do\|double\|eapply\|eassumption\|econstructor\|elim\%(type\)\?\|equality\|evar\|exact\|eexact\|exists\|f_equal\|fold\|functional\|generalize\|hnf\|idtac\|induction\|info\|injection\|instantiate\|intros\?\|intuition\|inversion\%(_clear\)\?\|lapply\|left\|move\|omega\|pattern\|pose\|proof\|quote\|red\|refine\|reflexivity\|rename\|repeat\|replace\|revert\|rewrite\|right\|ring\|set\|simple\?\|simplify_eqsplit\|split\|subst\|stepl\|stepr\|symmetry\|transitivity\|trivial\|try\|unfold\|vm_compute'
let s:proofstart = '\%(\<Fail\_s\+\)\@<!\<\%(Proof\|Next Obligation\|Obligation \d\+\)\>[^.]*\.'
let s:proofend = '\<\%(Qed\|Defined\|Abort\|Admitted\|Save\)\>'
let s:bullet = '[-+*]\+)\@!'
let s:bulletline = '^\s*' . s:bullet
let s:match = '\<\%(lazy\|multi\)\?match\>'
let s:inductive = '\%(\%(Co\)\?Inductive\|Variant\)'
let s:lineend = '\s*$'

" Match syntax groups.
function! s:matchsyn(line, col, syns) abort
  return printf(
    \ 'synIDattr(synID(%s, %s, 0), "name") =~? "%s"',
    \ a:line,
    \ a:col,
    \ join(a:syns, '\\|'))
endfunction
let s:skip = s:matchsyn('line(".")', 'col(".")', ['string', 'comment'])

" Skipping pattern, for comments
" (stolen from indent/ocaml.vim, thanks to the authors)
function! s:GetLineWithoutFullComment(lnum) abort
  let l:lnum = prevnonblank(a:lnum - 1)
  let l:previousline = substitute(getline(l:lnum), '(\*.*\*)\s*$', '', '')
  while l:previousline =~# '^\s*$' && l:lnum > 0
    let l:lnum = prevnonblank(l:lnum - 1)
    let l:previousline = substitute(getline(l:lnum), '(\*.*\*)\s*$', '', '')
  endwhile
  return l:lnum
endfunction

let s:zflag = has('patch-7.4.984') ? 'z' : ''

" Indent of a previous match
function! s:indent_of_previous(patt) abort
  " If 'z' flag isn't supported then move the cursor to the start of the line
  if s:zflag ==# ''
    let l:pos = getcurpos()
    call cursor(line('.'), 1)
  endif

  let l:indent = indent(search(a:patt, 'bWn' . s:zflag))

  " Restore cursor
  if s:zflag ==# ''
    call setpos('.', l:pos)
  endif

  return l:indent
endfunction

" Indent pairs
function! s:indent_of_previous_pair(pstart, pmid, pend, usecol, syns) abort
  let l:skip = s:matchsyn('line(".")', 'col(".")', a:syns)
  " NOTE: Match when cursor is inside the match. See ':h searchpair'.
  let l:pend = len(a:pend) > 1 ? a:pend . '\zs' : a:pend
  let [l:line, l:col] = searchpairpos(a:pstart, a:pmid, l:pend, 'bWn', l:skip)
  return a:usecol && l:line != 0 ? l:col - 1 : indent(l:line)
endfunction

" Search modulo strings and comments
function! s:search_skip(pattern, flags, stopline) abort
  while 1
    let l:match = search(a:pattern, a:flags, a:stopline)
    if l:match == 0 || !eval(s:skip)
      return l:match
    endif
  endwhile
endfunction

" Check for intervening unclosed '{' or '}'
function! s:find_unclosed_bracket(start, end) abort
  while 1
    let l:brack = s:search_skip('[{}]', 'W', a:end)
    if l:brack == 0
      " No brackets
      break
    endif

    " Search for match
    let [l:dir, l:stop] =
      \ getline(l:brack)[col('.') - 1] ==# '{' ? ['', a:end] : ['b', a:start]
    let l:matched = searchpair('{', '', '}', l:dir . 'Wn', s:skip, l:stop)
    if l:matched == 0
      " Unclosed bracket found
      break
    endif
  endwhile

  " Restore position
  call cursor(a:start, 1)
  return l:brack
endfunction

" Indent matching bullets
function! s:indent_bullet(currentline) abort
  let l:proof_start = search(s:proofstart, 'bWn')
  if l:proof_start == 0
    return -1
  endif

  let l:pos = getcurpos()
  call cursor(line('.'), 1)
  let l:bullet = matchstr(a:currentline, s:bullet)
  let l:ind = -1
  while l:ind == -1
    " Find previous bullet of the same length
    let l:prev_bullet = search('\M^\s\*' . l:bullet . l:bullet[0] . '\@!', 'bW', l:proof_start)
    " If no previous ones to match, fall through and indent using another rule
    if l:prev_bullet == 0
      break
    endif

    if s:find_unclosed_bracket(l:prev_bullet, v:lnum)
      " Bullets not in the same brackets, keep looking
      continue
    endif

    let l:ind = indent(l:prev_bullet)
  endwhile

  " Restore position
  call setpos('.', l:pos)
  return l:ind
endfunction

function! GetCoqIndent() abort
  try
    let l:ignorecase_save = &ignorecase
    let l:smartcase_save = &smartcase
    let l:magic_save = &magic
    set noignorecase nosmartcase magic
    return s:GetCoqIndent()
  finally
    let &ignorecase = l:ignorecase_save
    let &smartcase = l:smartcase_save
    let &magic = l:magic_save
  endtry
endfunction

" Main function
function! s:GetCoqIndent() abort
  " Find a non-commented currentline above the current currentline.
  let l:lnum = s:GetLineWithoutFullComment(v:lnum)
  let l:ind = indent(l:lnum)
  let l:previousline = substitute(getline(l:lnum), '(\*.*\*)\s*$', '', '')
  let l:currentline = getline(v:lnum)

  " current line is a comment
  if l:currentline =~# '^\s*(\*' || eval(s:matchsyn(v:lnum, 1, ['comment']))
    " ignore comments
    if get(g:, 'coqtail_noindent_comment', 0)
      return -1
    endif

    " ignore line comments
    if l:currentline !~# '^\s*(\*'
      " current line is starting a multiline comment
      let l:startcom = s:indent_of_previous_pair('(\*', '', '\*)', 1, ['string'])
      if l:currentline =~# '^\s*\*'
        return l:startcom + 1
      else
        return l:startcom + 3
      endif
    endif
  endif

  " At the start of the file use zero indent.
  if l:lnum == 0
    return 0
  endif

  " previous line ends a comment
  if l:previousline =~# '\*)\s*$'
    while eval(s:matchsyn(l:lnum, 1, ['comment']))
      " indent relative to the last non-comment
      call search('\*)', 'bW')
      let l:skip = s:matchsyn('line(".")', 'col(".")', ['string'])
      let l:startcom = searchpair('(\*', '', '\*)', 'bWn', l:skip)
      let l:lnum = s:GetLineWithoutFullComment(l:startcom)
    endwhile

    let l:ind = indent(l:lnum)
    let l:previousline = substitute(getline(l:lnum), '(\*.*\*)\s*$', '', '')

    if l:lnum == 0
      return 0
    endif
  endif

  " current line begins with '.':
  if l:currentline =~# '^\s*\.'
    return s:indent_of_previous(s:vernac)
  endif

  " current line begins with 'end':
  if l:currentline =~# '^\s*end\>'
    return s:indent_of_previous_pair(s:match, '', '\<end\>', 1, ['string', 'comment'])
  endif

  " current line begins with 'in':
  if l:currentline =~# '^\s*\<in\>'
    return s:indent_of_previous_pair('\<let\>', '', '\<in\>', 0, ['string', 'comment'])
  endif

  " current line begins with '|':
  if l:currentline =~# '^\s*|[|}]\@!'
    let l:match = s:indent_of_previous_pair(s:match, '', '\<end\>', 1, ['string', 'comment'])
    let l:off = get(g:, 'coqtail_inductive_shift', 1) * &sw
    return l:match != -1 ? l:match : s:indent_of_previous('^\s*' . s:inductive) + l:off
  endif

  " current line begins with terminating '|}', '}', or ')'
  if l:currentline =~# '^\s*|}'
    return s:indent_of_previous_pair('{|', '', '|}', 0, ['string', 'comment'])
  elseif l:currentline =~# '^\s*}'
    return s:indent_of_previous_pair('{', '', '}', 0, ['string', 'comment'])
  elseif l:currentline =~# '^\s*)'
    return s:indent_of_previous_pair('(', '', ')', 0, ['string', 'comment'])
  endif

  " end of proof
  if l:currentline =~# s:proofend
    return s:indent_of_previous(s:vernac . '\&\%(' . s:proofend . '\)\@!')
  endif

  " start of proof
  if l:previousline =~# s:proofstart . s:lineend
    return l:ind + &sw
  endif

  " bullet on current line
  if l:currentline =~# s:bulletline
    let l:ind_bullet = s:indent_bullet(l:currentline)
    if l:ind_bullet != -1
      return l:ind_bullet
    endif
    " fall through
  endif

  " bullet on previous line
  if l:previousline =~# s:bulletline
    let l:bullet = matchstr(l:previousline, s:bullet)
    return l:ind + len(l:bullet) + 1
  endif

  " } at end of previous line
  " NOTE: must come after the bullet cases
  if l:previousline =~# '}\s*$'
    call search('}', 'bW')
    return s:indent_of_previous_pair('{', '', '}', 0, ['string', 'comment'])
  endif

  " previous line begins with 'Section/Module':
  if l:previousline =~# '^\s*\%(Section\|Module\)\>'
    " don't indent if Section/Module is empty or is defined on one line
    if l:currentline !~# '^\s*End\>' && l:previousline !~# ':=.*\.\s*$' && l:previousline !~# '\<End\>'
      return l:ind + &sw
    endif
    " fall through
  endif

  " current line begins with 'End':
  if l:currentline =~# '^\s*End\>'
    let l:matches = matchlist(l:currentline, 'End\_s\+\([^.[:space:]]\+\)')
    if l:matches != []
      let l:name = l:matches[1]
      return s:indent_of_previous('\%(Section\|Module\)\_s\+' . l:name)
    endif
    " fall through
  endif

  " previous line has the form '|...'
  if l:previousline =~# '[{|]\@1<!|\%([^|}]\%(\.\|\<end\>\)\@!\)*$'
    return l:ind + get(g:, 'coqtail_match_shift', 2) * &sw
  endif

  " previous line has '{|' or '{' with no matching '|}' or '}'
  if l:previousline =~# '{|\?[^}]*\s*$'
    return l:ind + &sw
  endif

  " unterminated vernacular sentences
  if l:previousline =~# s:vernac . '.*[^.[:space:]]\s*$' && l:previousline !~# '^\s*$'
    return l:ind + &sw
  endif

  " back to normal indent after lines ending with '.'
  if l:previousline =~# '\.\s*$'
    if eval(s:matchsyn(l:lnum, 1, ['proof', 'tactic']))
      return l:ind
    else
      return s:indent_of_previous(s:vernac)
    endif
  endif

  " previous line ends with 'with'
  if l:previousline =~# '\<with\s*$'
    return l:ind + &sw
  endif

  " unterminated 'let ... in'
  if l:previousline =~# '\<let\>\%(.\%(\<in\>\)\@!\)*$'
    return l:ind + &sw
  endif

  " else
  return l:ind
endfunction
