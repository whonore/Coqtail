" Author: Wolf Honore
" Original Maintainer: Laurent Georget <laurent@lgeorget.eu>
" Coq Goal panel syntax definitions.

" Only load this syntax file when no other was loaded and user didn't opt out.
if exists('b:current_syntax') || get(g:, 'coqtail_nosyntax', 0)
  finish
endif
let b:current_syntax = 'coq-goals'

" Helpers
execute printf('source %s/_coq_common.vim', expand('<sfile>:p:h'))
let s:h = g:CoqtailSyntaxHelpers()

" Various
" syn match   coqError             "\S\+"
syn match   coqVernacPunctuation ":=\|\.\|:"
syn match   coqIdent             contained "[_[:alpha:]][_'[:alnum:]]*"

" Number of goals
syn match   coqNumberGoals       "\d\+ subgoals\?"
syn match   coqNumberUnfocused   "(\d\+ unfocused at this level)"
syn match   coqNumberAdmitted    "\d\+ admitted"
syn match   coqNumberShelved     "\d\+ shelved"

" Hypothesis
syn region  coqHypothesisBlock  contains=coqHypothesis start="^[_[:alpha:]][_'[:alnum:]]*\s*:" end="^$" keepend
syn region  coqHypothesis       contained contains=coqHypothesisBody matchgroup=coqIdent start="^\([_[:alpha:]][_'[:alnum:]]*,\s*\)*[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="^\S"me=e-1
syn region  coqHypothesisBody   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="^\S"me=e-1

" Separator
syn match   coqGoalNumber       contained "(\s*\d\+\s*\/\s*\d\+\s*)"
syn region  coqGoalSep          matchgroup=coqGoalLine start="^=\+" matchgroup=NONE end="^$\n" contains=coqGoalSepNumber nextgroup=coqGoalBlock keepend
syn region  coqGoalSepNumber    matchgroup=coqGoalNumber start="(\s*\d\+\s*\/\s*\d\+\s*)" matchgroup=NONE end=")"
syn region  coqNextGoal         start="Next goal" end="^$\n" nextgroup=coqGoalBlock keepend

" Goals
syn region coqGoalBlock contained contains=@coqTerm start="\S" end="^$"

" Terms
syn cluster coqTerm            contains=coqKwd,coqTermPunctuation,coqKwdMatch,coqKwdLet,coqKwdParen
syn region coqKwdMatch         contained contains=@coqTerm matchgroup=coqKwd start="\<match\>" end="\<with\>"
syn region coqKwdLet           contained contains=@coqTerm matchgroup=coqKwd start="\<let\>"   end=":="
syn region coqKwdParen         contained contains=@coqTerm matchgroup=coqTermPunctuation start="(" end=")" keepend extend
syn keyword coqKwd             contained else end exists2 fix forall fun if in struct then as return
syn match   coqKwd             contained "\<where\>"
syn match   coqKwd             contained "\<exists!\?"
syn match   coqKwd             contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|-\|*\|=\|>\|<\|<="
syn match coqTermPunctuation   contained ":=\|:>\|:\|;\|,\|||\|\[\|\]\|@\|?\|\<_\>"

" Various (High priority)
syn region  coqString            start=+"+ skip=+""+ end=+"+ extend

" TERMS AND TYPES
hi def link coqTerm              Type
hi def link coqKwd               coqTerm
hi def link coqTermPunctuation   coqTerm

" WORK LEFT
hi def link coqNumberGoals       Todo
hi def link coqNumberUnfocused   Todo
hi def link coqNumberAdmitted    Error
hi def link coqNumberShelved     Todo
hi def link coqGoalLine          Todo

" GOAL IDENTIFIER
hi def link coqGoalNumber        Underlined
hi def link coqNextGoal          Underlined

" USUAL VIM HIGHLIGHTINGS
" Comments
hi def link coqComment           Comment

" Strings
hi def link coqString            String
