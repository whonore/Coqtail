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

let s:inside_proof = 0

" Some useful patterns
let s:vernac = '\C\<\%(Abort\|About\|Add\|Admitted\|Arguments\|Axiom\|Back\|Bind\|Canonical\|Cd\|Check\|Close\|Coercion\|CoFixpoint\|CoInductive\|Combined\|Conjecture\|Context\|Corollary\|Declare\|Defined\|Definition\|Delimit\|Derive\|Drop\|End\|Eval\|Example\|Existential\|Export\|Extract\|Extraction\|Fact\|Fixpoint\|Focus\|Function\|Functional\|Goal\|Hint\|Hypothes[ie]s\|Identity\|Implicit\|Import\|Inductive\|Infix\|Inspect\|Lemma\|Let\|Load\|Locate\|Ltac\|Module\|Mutual\|Notation\|Opaque\|Open\|Parameters\=\|Print\|Program\|Proof\|Proposition\|Pwd\|Qed\|Quit\|Record\|Recursive\|Remark\|Remove\|Require\|Reserved\|Reset\|Restart\|Restore\|Resume\|Save\|Scheme\|Search\%(About\|Pattern\|Rewrite\)\=\|Section\|Set\|Show\|Structure\|SubClass\|Suspend\|Tactic\|Test\|Theorem\|Time\|Transparent\|Undo\|Unfocus\|Unset\|Variables\?\|Whelp\|Write\)\>'
let s:tactic = '\C\<\%(absurd\|apply\|assert\|assumption\|auto\|case_eq\|change\|clear\%(body\)\?\|cofix\|cbv\|compare\|compute\|congruence\|constructor\|contradiction\|cut\%(rewrite\)\?\|decide\|decompose\|dependent\|destruct\|discriminate\|do\|double\|eapply\|eassumption\|econstructor\|elim\%(type\)\?\|equality\|evar\|exact\|eexact\|exists\|f_equal\|fold\|functional\|generalize\|hnf\|idtac\|induction\|info\|injection\|instantiate\|intros\?\|intuition\|inversion\%(_clear\)\?\|lapply\|left\|move\|omega\|pattern\|pose\|proof\|quote\|red\|refine\|reflexivity\|rename\|repeat\|replace\|revert\|rewrite\|right\|ring\|set\|simple\?\|simplify_eqsplit\|split\|subst\|stepl\|stepr\|symmetry\|transitivity\|trivial\|try\|unfold\|vm_compute'
let s:proofstart = '^\s*\%(Proof\|\%(Next Obligation\|Obligation \d\+\)\( of [^.]\+\)\?\)\.$'

" Skipping pattern, for comments
" (stolen from indent/ocaml.vim, thanks to the authors)
function s:GetLineWithoutFullComment(lnum)
  let lnum = prevnonblank(a:lnum - 1)
  let previousline = substitute(getline(lnum), '(\*.*\*)\s*$', '', '')
  while previousline =~ '^\s*$' && lnum > 0
    let lnum = prevnonblank(lnum - 1)
    let previousline = substitute(getline(lnum), '(\*.*\*)\s*$', '', '')
  endwhile
  return lnum
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
  if searchFirst
    call search(a:pend, 'bW')
  endif
  return indent(searchpair(a:pstart, a:pmid, a:pend, 'bWn', 'synIDattr(synID(line("."), col("."), 0), "name") =~? "string\\|comment"'))
endfunction

" Main function
function GetCoqIndent()
  " Find a non-commented currentline above the current currentline.
  let lnum = s:GetLineWithoutFullComment(v:lnum)

  " At the start of the file use zero indent.
  if lnum == 0
    return 0
  endif

  let ind = indent(lnum)
  let previousline = substitute(getline(lnum), '(\*.*\*)\s*$', '', '')

  let currentline = getline(v:lnum)

  " current line begins with '.':
  if currentline =~ '^\s*\.'
    return s:indent_of_previous(s:vernac)

  " current line begins with 'end':
  elseif currentline =~ '\C^\s*end\>'
    return s:indent_of_previous_pair('\<match\>', '', '\<end\>', 1)

  " current line begins with 'in':
  elseif currentline =~ '^\s*\<in\>'
    return s:indent_of_previous_pair('\<let\>', '', '\<in\>', 1)

  " current line begins with '|':
  elseif currentline =~ '^\s*|}\@!'
    if previousline =~ '^\s*Inductive'
      return ind + &sw
    elseif previousline =~ '^\s*match'
      return ind
    elseif previousline =~ '^\s*end\>'
      return s:indent_of_previous_pair('\<match\>', '', '\<end\>', 0)
    else
      return s:indent_of_previous('^\s*|}\@!')
    endif

  " current line begins with terminating '|}'
  elseif currentline =~ '^\s*|}'
    return s:indent_of_previous_pair('{|', '', '|}', 1)

  " end of proof
  elseif currentline =~ '^\s*}'
    return s:indent_of_previous_pair('{', '', '}', 1)
  elseif currentline =~ '^\s*)'
    return s:indent_of_previous_pair('(', '', ')', 1)
  elseif currentline =~ '\<\%(Qed\|Defined\|Abort\|Admitted\)\>'
    let s:inside_proof = 0
    return s:indent_of_previous(s:vernac.'\&\%(\<\%(Qed\|Defined\|Abort\|Admitted\)\>\)\@!')

  " start of proof
  elseif previousline =~ s:proofstart
    let s:inside_proof = 1
    return ind + &sw

  " bullet in proof
  elseif currentline =~ '^\s*[-+*]' || previousline =~ '^\s*[-+*]'
    let proof_start = search(s:proofstart, 'bWn')

    if proof_start != 0
      " In proof

      if currentline =~ '^\s*[-+*]'
        " Bullet in a '{' section
        if previousline =~ '^\s*{'
          return ind + &sw
        endif

        let bullet = matchstr(currentline, '[-+*]\+')

        while 1
          " Find previous bullet of the same length
          let prev_bullet = search('\M^\s\*' . bullet . bullet[0] . '\@!', 'bW', proof_start)

          " If no previous ones to match, fall through and indent using another rule
          if prev_bullet != 0
            " Check for intervening unclosed '{' or '}'
            let brack_open = search('{', 'W', v:lnum)

            if brack_open == 0 || searchpair('{', '', '}', 'Wn', '', v:lnum) > 0
              " No '{' or it is matched
              call cursor(v:lnum, 1)
              let brack_close = search('}', 'bW', prev_bullet)

              if brack_close == 0 || searchpair('{', '', '}', 'bWn', '', prev_bullet) > 0
                " No '}'
                return indent(prev_bullet)
              endif
              " else '}', but no matching '{', look for another bullet
            endif

            " Restore position
            call cursor(prev_bullet, 1)
          else
            break
          endif
        endwhile
      endif

      " after a bullet in proof
      if previousline =~ '^\s*[-+*]'
        let bullet = matchstr(previousline, '[-+*]\+')

        return ind + len(bullet) + 1
      endif
    endif

    return ind

  " previous line begins with 'Section/Module':
  elseif previousline =~ '^\s*\%(Section\|Module\)\>'
    " don't indent if Section/Module is empty or is defined on one line
    if currentline !~ '^\s*End\>' && previousline !~ ':=.*\.\s*$' && previousline !~ '\<End\>'
      return ind + &sw
    endif

  " current line begins with 'End':
  elseif currentline =~ '^\s*End\>'
    return ind - &sw

  " previous line has the form '|...'
  elseif previousline =~ '{\@1<!|\%([^}]\%(\.\|end\)\@!\)*$'
    return ind + &sw + &sw

  " previous line has '{|' or '{' with no matching '|}' or '}'
  elseif previousline =~ '{|\?[^}]*$'
    return ind + &sw

  " unterminated vernacular sentences
  elseif previousline =~ s:vernac.'.*[^.]$' && previousline !~ '^\s*$'
    return ind + &sw

  " back to normal indent after lines ending with '.'
  elseif previousline =~ '\.$'
    if synIDattr(synID(line('.') - 1, col('.'), 0), "name") =~? '\cproof\|tactic'
      return ind
    else
      return s:indent_of_previous(s:vernac)
    endif

  " previous line ends with 'with'
  elseif previousline =~ '\<with$'
    return ind + &sw

  " unterminated 'let ... in'
  elseif previousline =~ '\<let\>\%(.\%(\<in\>\)\@!\)*$'
    return ind + &sw

  " else
  else
    return ind
  endif
endfunction

" vim:sw=2
