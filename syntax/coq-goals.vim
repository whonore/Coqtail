" Vim syntax file
" Language:     Coq-goals
" Filenames:    *.v
" Maintainer:  Laurent Georget <laurent@lgeorget.eu>
" Last Change: 2015 Jul 07 - Initial syntax coloring, pretty stable
" License:     public domain
" Modified By: Wolf Honore

" Only load this syntax file when no other was loaded and user didn't opt out.
if exists('b:current_syntax') || get(g:, 'coqtail_nosyntax', 0)
  finish
endif

" Keywords are alphanumeric, _, and '
setlocal iskeyword=@,48-57,192-255,_,'
syn iskeyword clear

" Coq is case sensitive.
syn case match

" Various
" syn match   coqError             "\S\+"
syn match   coqVernacPunctuation ":=\|\.\|:"
syn match   coqIdent             contained "[[:digit:]']\@!\k\k*"

" Number of goals
syn match   coqNumberGoals       "\d\+ subgoals\?"
syn match   coqNumberUnfocused   "(\d\+ unfocused at this level)"
syn match   coqNumberAdmitted    "\d\+ admitted"
syn match   coqNumberShelved     "\d\+ shelved"

" Hypothesis
syn region  coqHypothesisBlock  contains=coqHypothesis start="^[[:digit:]']\@!\k\k*\s*:" end="^$" keepend
syn region  coqHypothesis       contained contains=coqHypothesisBody matchgroup=coqIdent start="^\([[:digit:]']\@!\k\k*,\s*\)*[[:digit:]']\@!\k\k*" matchgroup=NONE end="^\S"me=e-1
syn region  coqHypothesisBody   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="^\S"me=e-1

" Separator
syn match   coqGoalNumber       contained "(\s*\d\+\s*\/\s*\d\+\s*)"
syn region  coqGoalSep          matchgroup=coqGoalLine start="^=\+" matchgroup=NONE end="^$\n" contains=coqGoalSepNumber nextgroup=coqGoalBlock keepend
syn region  coqGoalSepNumber    matchgroup=coqGoalNumber start="(\s*\d\+\s*\/\s*\d\+\s*)" matchgroup=NONE end=")"
syn region  coqNextGoal         start="Next goal" end="^$\n" nextgroup=coqGoalBlock keepend

" Goals
syn region coqGoalBlock contained contains=@coqTerm start="\S" end="^$"

" Terms
syn cluster coqTerm            contains=coqKwd,coqTermPunctuation,coqKwdMatch,coqKwdLet,coqKwdParen,coqString
syn region coqKwdMatch         contained contains=@coqTerm matchgroup=coqKwd start="\<match\>" end="\<with\>"
syn region coqKwdLet           contained contains=@coqTerm matchgroup=coqKwd start="\<let\>"   end=":="
syn region coqKwdParen         contained contains=@coqTerm matchgroup=coqTermPunctuation start="(" end=")" keepend extend
syn keyword coqKwd             contained else end exists2 fix forall fun if in struct then as return
syn match   coqKwd             contained "\<where\>"
syn match   coqKwd             contained "\<exists!\?\>"
syn match   coqKwd             contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|-\|*\|=\|>\|<\|<="
syn match coqTermPunctuation   contained ":=\|:>\|:\|;\|,\|||\|\[\|\]\|@\|?\|\<_\>"

" Various (High priority)
syn region  coqString            start=+"+ skip=+""+ end=+"+ extend

" Synchronization
syn sync minlines=50
syn sync maxlines=500

" Define the default highlighting.
command -nargs=+ HiLink hi def link <args>

" TERMS AND TYPES
HiLink coqTerm              Type
HiLink coqKwd               coqTerm
HiLink coqTermPunctuation   coqTerm

" WORK LEFT
HiLink coqNumberGoals       Todo
HiLink coqNumberUnfocused   Todo
HiLink coqNumberAdmitted    Error
HiLink coqNumberShelved     Todo
HiLink coqGoalLine          Todo

" GOAL IDENTIFIER
HiLink coqGoalNumber        Underlined
HiLink coqNextGoal          Underlined

" USUAL VIM HIGHLIGHTINGS
" Comments
HiLink coqComment           Comment

" Strings
HiLink coqString            String

delcommand HiLink

let b:current_syntax = 'coq-goals'
