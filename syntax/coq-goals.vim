" Vim syntax file
" Language:     Coq-goals
" Filenames:    *.v
" Maintainer:  Laurent Georget <laurent@lgeorget.eu>
" Last Change: 2015 Jul 07 - Initial syntax coloring, pretty stable
" License:     public domain
" Modified By: Wolf Honore

" Only load this syntax file when user didn't opt out
if exists('g:coqtail_nosyntax') && g:coqtail_nosyntax
  finish
endif

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "coq-goals"
  finish
endif

" Coq is case sensitive.
syn case match

" Various
" syn match   coqError             "\S\+"
syn match   coqVernacPunctuation ":=\|\.\|:"
syn match   coqIdent             contained "[_[:alpha:]][_'[:alnum:]]*"

" Number of goals
syn match   coqNumberGoals       '\d\+ subgoals\?'
syn match   coqNumberUnfocused   '(\d\+ unfocused at this level)'
syn match   coqNumberAdmitted    '\d\+ admitted'
syn match   coqNumberShelved     '\d\+ shelved'

" Hypothesis
syn region  coqHypothesisBlock  contains=coqHypothesis start="^[_[:alpha:]][_'[:alnum:]]*\s*:" end="^$" keepend
syn region  coqHypothesis       contained contains=coqHypothesisBody matchgroup=coqIdent start="^\([_[:alpha:]][_'[:alnum:]]*,\s*\)*[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="^\S"me=e-1
syn region  coqHypothesisBody   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="^\S"me=e-1

" Separator
syn match   coqGoalNumber       contained "(\s*\d\+\s*\/\s*\d\+\s*)"
syn region  coqGoalSep          matchgroup=coqGoalLine start='^=\+' matchgroup=NONE end='^$\n' contains=coqGoalSepNumber nextgroup=coqGoalBlock keepend
syn region  coqGoalSepNumber    matchgroup=coqGoalNumber start="(\s*\d\+\s*\/\s*\d\+\s*)" matchgroup=NONE end=")"
syn region  coqNextGoal         start='Next goal' end='^$\n' nextgroup=coqGoalBlock keepend

" Goals
syn region coqGoalBlock contained contains=@coqTerm start='\S' end='^$'

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

" Synchronization
syn sync minlines=50
syn sync maxlines=500

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_coq_goals_syntax_inits")
  if version < 508
    let did_coq_goals_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  " TERMS AND TYPES
  HiLink coqTerm                      Type
  HiLink coqKwd             coqTerm
  HiLink coqTermPunctuation coqTerm

  " WORK LEFT
  HiLink coqNumberGoals               Todo
  HiLink coqNumberUnfocused           Todo
  HiLink coqNumberAdmitted            Error
  HiLink coqNumberShelved             Todo
  HiLink coqGoalLine                  Todo

  " GOAL IDENTIFIER
  HiLink coqGoalNumber                Underlined
  HiLink coqNextGoal                  Underlined

  " USUAL VIM HIGHLIGHTINGS
  " Comments
  HiLink coqComment                   Comment

  " Strings
  HiLink coqString                    String

  delcommand HiLink
endif

let b:current_syntax = "coq-goals"
