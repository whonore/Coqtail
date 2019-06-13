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
if exists('b:did_indent') || (exists('g:coqtail_noindent') && g:coqtail_noindent)
  finish
endif
let b:did_indent = 1

setlocal expandtab
setlocal indentexpr=GetCoqIndent()
setlocal indentkeys=o,O,0=.,0=end,0=End,0=in,0=\|,0=Qed,0=Defined,0=Abort,0=Admitted,0},0),0-,0+,0*
setlocal nolisp
setlocal nosmartindent
setlocal shiftwidth=2
setlocal tabstop=2

" Comment handling
if !exists('no_coq_comments')
  if has('comments')
    setlocal comments=srn:(*,mb:*,exn:*)
    setlocal fo=cqt
  endif
endif

" Only define the function once.
if exists('*GetCoqIndent')
  finish
endif

" Some useful patterns
let s:vernac = '\C\<\%(Abort\|About\|Add\|Admitted\|Arguments\|Axiom\|Back\|Bind\|Canonical\|Cd\|Check\|Close\|Coercion\|CoFixpoint\|CoInductive\|Combined\|Conjecture\|Context\|Corollary\|Declare\|Defined\|Definition\|Delimit\|Derive\|Drop\|End\|Eval\|Example\|Existential\|Export\|Extract\|Extraction\|Fact\|Fixpoint\|Focus\|Function\|Functional\|Goal\|Hint\|Hypothes[ie]s\|Identity\|Implicit\|Import\|Inductive\|Infix\|Inspect\|Lemma\|Let\|Load\|Locate\|Ltac\|Module\|Mutual\|Notation\|Opaque\|Open\|Parameters\=\|Print\|Program\|Proof\|Proposition\|Pwd\|Qed\|Quit\|Record\|Recursive\|Remark\|Remove\|Require\|Reserved\|Reset\|Restart\|Restore\|Resume\|Save\|Scheme\|Search\%(About\|Pattern\|Rewrite\)\=\|Section\|Set\|Show\|Structure\|SubClass\|Suspend\|Tactic\|Test\|Theorem\|Time\|Transparent\|Undo\|Unfocus\|Unset\|Variables\?\|Whelp\|Write\)\>'
let s:tactic = '\C\<\%(absurd\|apply\|assert\|assumption\|auto\|case_eq\|change\|clear\%(body\)\?\|cofix\|cbv\|compare\|compute\|congruence\|constructor\|contradiction\|cut\%(rewrite\)\?\|decide\|decompose\|dependent\|destruct\|discriminate\|do\|double\|eapply\|eassumption\|econstructor\|elim\%(type\)\?\|equality\|evar\|exact\|eexact\|exists\|f_equal\|fold\|functional\|generalize\|hnf\|idtac\|induction\|info\|injection\|instantiate\|intros\?\|intuition\|inversion\%(_clear\)\?\|lapply\|left\|move\|omega\|pattern\|pose\|proof\|quote\|red\|refine\|reflexivity\|rename\|repeat\|replace\|revert\|rewrite\|right\|ring\|set\|simple\?\|simplify_eqsplit\|split\|subst\|stepl\|stepr\|symmetry\|transitivity\|trivial\|try\|unfold\|vm_compute'
let s:proofstart = '^\s*\%(Proof\|\%(Next Obligation\|Obligation \d\+\)\( of [^.]\+\)\?\)\.$'

" Skipping pattern, for comments
" (stolen from indent/ocaml.vim, thanks to the authors)
function s:GetLineWithoutFullComment(lnum)
  let l:lnum = prevnonblank(a:lnum - 1)
  let l:previousline = substitute(getline(l:lnum), '(\*.*\*)\s*$', '', '')
  while l:previousline =~ '^\s*$' && l:lnum > 0
    let l:lnum = prevnonblank(l:lnum - 1)
    let l:previousline = substitute(getline(l:lnum), '(\*.*\*)\s*$', '', '')
  endwhile
  return l:lnum
endfunction

let s:zflag = has('patch-7.4.984') ? 'z' : ''

" Indent of a previous match
function s:indent_of_previous(patt)
  " If 'z' flag isn't supported then move the cursor to the start of the line
  if s:zflag == ''
    let l:pos = getcurpos()
    call cursor(line('.'), 1)
  endif

  let l:indent = indent(search(a:patt, 'bWn' . s:zflag))

  " Restore cursor
  if s:zflag == ''
    call setpos('.', l:pos)
  endif

  return l:indent
endfunction

" Indent pairs
function s:indent_of_previous_pair(pstart, pmid, pend, searchFirst)
  if a:searchFirst
    call search(a:pend, 'bW')
  endif
  return indent(searchpair(a:pstart, a:pmid, a:pend, 'bWn', 'synIDattr(synID(line("."), col("."), 0), "name") =~? "string\\|comment"'))
endfunction

" Main function
function GetCoqIndent()
  " Find a non-commented currentline above the current currentline.
  let l:lnum = s:GetLineWithoutFullComment(v:lnum)

  " At the start of the file use zero indent.
  if l:lnum == 0
    return 0
  endif

  let l:ind = indent(l:lnum)
  let l:previousline = substitute(getline(l:lnum), '(\*.*\*)\s*$', '', '')
  let l:currentline = getline(v:lnum)

  " current line begins with '.':
  if l:currentline =~ '^\s*\.'
    return s:indent_of_previous(s:vernac)

  " current line begins with 'end':
  elseif l:currentline =~ '\C^\s*end\>'
    return s:indent_of_previous_pair('\<match\>', '', '\<end\>', 0)

  " current line begins with 'in':
  elseif l:currentline =~ '^\s*\<in\>'
    return s:indent_of_previous_pair('\<let\>', '', '\<in\>', 0)

  " current line begins with '|':
  elseif l:currentline =~ '^\s*|}\@!'
    if l:previousline =~ '^\s*Inductive'
      return l:ind + &sw
    elseif l:previousline =~ '^\s*match'
      return l:ind
    elseif l:previousline =~ '^\s*end\>'
      return s:indent_of_previous_pair('\<match\>', '', '\<end\>', 0)
    else
      return s:indent_of_previous('^\s*|}\@!')
    endif

  " current line begins with terminating '|}'
  elseif l:currentline =~ '^\s*|}'
    return s:indent_of_previous_pair('{|', '', '|}', 0)

  " ending } or )
  elseif l:currentline =~ '^\s*}'
    return s:indent_of_previous_pair('{', '', '}', 0)
  elseif l:currentline =~ '^\s*)'
    return s:indent_of_previous_pair('(', '', ')', 0)

  " end of proof
  elseif l:currentline =~ '\<\%(Qed\|Defined\|Abort\|Admitted\)\>'
    return s:indent_of_previous(s:vernac.'\&\%(\<\%(Qed\|Defined\|Abort\|Admitted\)\>\)\@!')

  " start of proof
  elseif l:previousline =~ s:proofstart
    return l:ind + &sw

  " bullet in proof
  elseif l:currentline =~ '^\s*[-+*]' || l:previousline =~ '^\s*[-+*]'
    let l:proof_start = search(s:proofstart, 'bWn')

    if l:proof_start != 0
      " In proof

      if l:currentline =~ '^\s*[-+*]'
        let l:bullet = matchstr(l:currentline, '[-+*]\+')

        while 1
          " Find previous bullet of the same length
          let l:prev_bullet = search('\M^\s\*' . l:bullet . l:bullet[0] . '\@!', 'bW', l:proof_start)

          " If no previous ones to match, fall through and indent using another rule
          if l:prev_bullet != 0
            " Check for intervening unclosed '{' or '}'
            let l:brack_open = search('{', 'W', v:lnum)

            if l:brack_open == 0 || searchpair('{', '', '}', 'Wn', '', v:lnum) > 0
              " No '{' or it is matched
              call cursor(v:lnum, 1)
              let l:brack_close = search('}', 'bW', l:prev_bullet)

              if l:brack_close == 0 || searchpair('{', '', '}', 'bWn', '', l:prev_bullet) > 0
                " No '}'
                return indent(l:prev_bullet)
              endif
              " else '}', but no matching '{', look for another bullet
            endif

            " Restore position
            call cursor(l:prev_bullet, 1)
          else
            break
          endif
        endwhile
      endif

      " after a bullet in proof
      if l:previousline =~ '^\s*[-+*]'
        let l:bullet = matchstr(l:previousline, '[-+*]\+')

        return l:ind + len(l:bullet) + 1
      endif
    endif

    return l:ind

  " } at end of previous line
  " N.B. must come after the bullet cases
  elseif l:previousline =~ '}\s*$'
    return s:indent_of_previous_pair('{', '', '}', 1)

  " previous line begins with 'Section/Module':
  elseif l:previousline =~ '^\s*\%(Section\|Module\)\>'
    " don't indent if Section/Module is empty or is defined on one line
    if l:currentline !~ '^\s*End\>' && l:previousline !~ ':=.*\.\s*$' && l:previousline !~ '\<End\>'
      return l:ind + &sw
    endif

  " current line begins with 'End':
  elseif l:currentline =~ '^\s*End\>'
    return l:ind - &sw

  " previous line has the form '|...'
  elseif l:previousline =~ '{\@1<!|\%([^}]\%(\.\|end\)\@!\)*$'
    return l:ind + &sw + &sw

  " previous line has '{|' or '{' with no matching '|}' or '}'
  elseif l:previousline =~ '{|\?[^}]*$'
    return l:ind + &sw

  " unterminated vernacular sentences
  elseif l:previousline =~ s:vernac.'.*[^.]$' && l:previousline !~ '^\s*$'
    return l:ind + &sw

  " back to normal indent after lines ending with '.'
  elseif l:previousline =~ '\.$'
    if synIDattr(synID(l:lnum, 1, 0), "name") =~? '\cproof\|tactic'
      return l:ind
    else
      return s:indent_of_previous(s:vernac)
    endif

  " previous line ends with 'with'
  elseif l:previousline =~ '\<with$'
    return l:ind + &sw

  " unterminated 'let ... in'
  elseif l:previousline =~ '\<let\>\%(.\%(\<in\>\)\@!\)*$'
    return l:ind + &sw

  " else
  else
    return l:ind
  endif
endfunction

" vim:sw=2
