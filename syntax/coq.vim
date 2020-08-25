" Author: Wolf Honore
" Original Maintainer: Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Coq syntax definitions.

" Define Coqtail-specific highlighting groups.
if !exists('b:coqtail_did_highlight') || !b:coqtail_did_highlight
  function! s:CoqtailHighlight() abort
    " Use user-defined colors if they exist
    if exists('*g:CoqtailHighlight')
      call g:CoqtailHighlight()
    elseif &t_Co > 16
      hi def CoqtailChecked ctermbg=17 guibg=LightGreen
      hi def CoqtailSent ctermbg=60 guibg=LimeGreen
    else
      hi def CoqtailChecked ctermbg=4 guibg=LightGreen
      hi def CoqtailSent ctermbg=7 guibg=LimeGreen
    endif
    hi def link CoqtailError Error
  endfunction

  call s:CoqtailHighlight()
  " N.B. Setting a colorscheme usually calls 'syntax reset' so have to set
  " Coqtail highlighting colors again
  augroup coqtail_highlight
    autocmd!
    autocmd ColorScheme * call s:CoqtailHighlight()
  augroup END
endif
let b:coqtail_did_highlight = 1

" Only load this syntax file when no other was loaded and user didn't opt out.
if exists('b:current_syntax') || get(g:, 'coqtail_nosyntax', 0)
  finish
endif
let b:current_syntax = 'coq'

" Helpers
execute printf('source %s/_coq_common.vim', expand('<sfile>:p:h'))
let s:h = g:CoqtailSyntaxHelpers()

syn cluster coqVernac contains=coqLoad,coqCheckCompute,coqEval,coqNotation,coqTacNotation,coqDecl,coqThm,coqGoal,coqLtacDecl,coqDef,coqCoercion,coqFix,coqInd,coqRec,coqCls,coqIns,coqShow,coqHint

" Various
syn match   coqError             "\S\+"
syn match   coqVernacPunctuation ":=\|\.\|:"
call s:h.match('coqIdent', s:h.ident, 'contained')
" TODO: update these lists
syn keyword coqTopLevel          Type Canonical Structure Cd Drop Existential
"...
syn keyword coqVernacCmd         Local Global Polymorphic Functional Scheme Back Combined
syn keyword coqFeedback          Show

syn region coqPrint matchgroup=coqVernacCmd start="\<\%(Print\%(\_s\+Assumptions\)\?\|About\)\>" contains=coqIdent end="\.\_s"
syn region coqPrintUniversesSubgraph matchgroup=coqVernacCmd start="\<Print\_s\+Universes\_s\+Subgraph\>" contains=coqIdent end="\.\_s"

" Modules
" TODO: highlight module name as ident
let s:mod_start = '\<Module\%(\_s\+Type\)\?\_s\+\z(' . s:h.ident . '\)'
call s:h.region('coqModule', 'coqVernacCmd',
  \ s:mod_start . '\%([^=]*\.\_s\)\@=',
  \ '\<End\_s\+\z1\_s*' . s:h.dot,
  \ 'contains=coqModule,coqSection,coqVernacPunctuation,coqModBinder,@coqVernac'
\)
call s:h.region('coqModule', 'coqVernacCmd',
  \ s:mod_start . '\%(.*:=\)\@=',
  \ [":=", 'me=e-2'],
  \ 'contains=coqVernacPunctuation,coqModBinder nextgroup=coqModVal'
\)
call s:h.region('coqModBinder', 'coqVernacPunctuation',
  \ '(', ')',
  \ 'contains=coqIdent keepend contained'
\)
call s:h.region('coqModVal', 'coqVernacPunctuation',
  \ ':=', s:h.dot,
  \ 'contains=coqIdent,coqTermPunctuation'
\)

" Terms
syn cluster coqTerm            contains=coqKwd,coqTermPunctuation,coqKwdMatch,coqKwdLet,coqKwdParen
call s:h.region('coqKwdMatch', 'coqKwd',
  \ s:h.atom('match'), s:h.atom('with'),
  \ 'contains=@coqTerm contained'
\)
call s:h.region('coqKwdLet', ['coqKwd', 'coqVernacPunctuation'],
  \ s:h.atom('let'), ':=',
  \ 'contains=@coqTerm contained'
\)
call s:h.region('coqKwdParen', 'coqTermPunctuation',
  \ '(', ')',
  \ 'contains=@coqTerm contained keepend extend'
\)
syn keyword coqKwd             contained else end exists2 fix cofix forall fun if in struct then as return
syn match   coqKwd             contained "\<where\>"
syn match   coqKwd             contained "\<exists!\?"
syn match   coqKwd             contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|-\|*\|=\|>\|<\|<="
syn match coqTermPunctuation   contained ":=\|:>\|:\|;\|,\|||\|\[\|\]\|@\|?\|\<_\>\|<+"

" Module Loading
syn cluster coqLoad contains=coqImport,coqInclude,coqRequire,coqFrom
call s:h.region('coqImport', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom(s:h.group(s:h.or('Export', 'Import'))), s:h.dot,
  \ 'contains=coqIdent'
\)
call s:h.region('coqInclude', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Include'), s:h.dot,
  \ 'contains=coqIdent'
\)
call s:h.region('coqRequire', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Require'), s:h.dot,
  \ 'contains=coqIdent,coqImport keepend'
\)
call s:h.region('coqFrom', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('From'), s:h.dot,
  \ 'contains=coqIdent,coqRequire keepend'
\)

" Various
" TODO: include Print, Search, etc here?
call s:h.region('coqCheckCompute', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom(s:h.group(s:h.or('Check', 'Compute'))), s:h.dot,
  \ 'contains=@coqTerm'
\)
call s:h.region('coqOpaque', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom(s:h.group(s:h.or('Opaque', 'Transparent'))), s:h.dot,
  \ ''
\)
" TODO: check this list
let s:shows = s:h.optional(s:h.atom(s:h.group(s:h.or(
  \ 'Implicits', 'Script', 'Tree', 'Proof', 'Conjectures', 'Intros\?', 'Existentials'
\))))
call s:h.region('coqShow', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Show') . s:h.spaces . s:shows, s:h.dot,
  \ ''
\)
call s:h.region('coqImplicitTypes', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atoms('Implicit', 'Types\?'), s:h.dot,
  \ ''
\)
let s:generalize_opts = s:h.optional(s:h.atom(s:h.group(s:h.or('All', 'No'))) . s:h.spaces)
call s:h.region('coqGeneralizable', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Generalizable') . s:h.spaces . s:generalize_opts . s:h.atom('Variables\?'),
  \ s:h.dot,
  \ ''
\)

" Sections
call s:h.region('coqSection', 'coqVernacCmd',
  \ '\<Section\_s\+\z(' . s:h.ident . '\)\_s*' . s:h.dot,
  \ '\<End\_s\+\z1\_s*' . s:h.dot,
  \ 'contains=coqSection,@coqVernac'
\)

" Obligations
call s:h.region('coqObligation', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom(s:h.group(s:h.or('Obligations', 'Preterm'))), s:h.dot,
  \ 'contains=coqOblOf keepend'
\)
call s:h.region('coqObligation', ['coqProofAdmit', 'coqVernacPunctuation'],
  \ s:h.atoms('Admit', 'Obligations'), s:h.dot,
  \ 'contains=coqOblOf keepend'
\)
call s:h.region('coqObligation', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atoms('Solve', 'Obligations'), s:h.dot,
  \ 'contains=coqOblOf,coqOblWith keepend'
\)
call s:h.region('coqObligation', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atoms('Solve', 'All', 'Obligations'), s:h.dot,
  \ 'contains=coqOblWith keepend'
\)
call s:h.region('coqOblOf', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('of'), s:h.dot,
  \ 'contains=coqIdent,coqOblWith keepend'
\)
call s:h.region('coqOblOfDelim', 'coqProofDot',
  \ s:h.atom('of'), s:h.dot,
  \ 'contains=coqIdent,coqOblWith keepend'
\)
call s:h.region('coqOblWith', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('with'), s:h.dot,
  \ 'contains=coqLtac,coqTactic'
\)
call s:h.region('coqObligation', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atoms('Obligation', 'Tactic'), s:h.dot,
  \ 'contains=coqOblExpr keepend'
\)
call s:h.region('coqOblExpr', 'coqVernacPunctuation',
  \ ':=', s:h.dot,
  \ 'contains=coqLtac, coqTactic'
\)

" Scopes
" TODO: fix these rules
call s:h.region('coqBind', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom(s:h.group(s:h.or('Bind', 'Delimit'))), s:h.dot,
  \ 'contains=coqScope keepend'
\)
call s:h.region('coqArgsScope', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Arguments'), s:h.dot,
  \ 'contains=coqScope keepend'
\)
call s:h.region('coqOpen', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Open'), s:h.dot,
  \ 'contains=coqScope keepend'
\)
call s:h.region('coqClose', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Close'), s:h.dot,
  \ 'contains=coqScope keepend'
\)
call s:h.region('coqScope', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atom('Scope'), s:h.dot,
  \ 'contained'
\)

" Hints
" TODO: handle Hint Extern, Resolve ->, precedence, missing cases, etc
let s:hints = s:h.group(s:h.or(
  \ 'Resolve', 'Immediate', 'Constructors', 'Unfold', 'Extern'
\))
call s:h.region('coqHint', ['coqVernacCmd', 'coqVernacPunctuation'],
  \ s:h.atoms('Hint', s:hints), s:h.dot,
  \ 'contains=coqIdent'
\)

" Add
syn region coqAdd       contains=coqAddOption,coqAddOption2 matchgroup=coqVernacCmd start="\<Add\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqAddOption         contained contains=coqAddPrintingOption matchgroup=coqVernacCmd start="\<Printing\>" end="\.\_s"
syn region coqAddPrintingOption contained matchgroup=coqVernacCmd start="\<\%(Let\|If\)\>" end="\.\_s"
syn region coqAddOption         contained contains=coqAddLegacyOption matchgroup=coqVernacCmd start="\<Legacy\>" end="\.\_s"
syn region coqAddLegacyOption   contained contains=coqAddRingOption,coqAddSemiRingOption matchgroup=coqVernacCmd start="\<Abstract\>" end="\.\_s"
syn region coqAddRingOption     contained matchgroup=coqVernacCmd start="\<Ring\>" end="\.\_s"
syn region coqAddSemiRingOption contained contains=coqAddRingOption matchgroup=coqVernacCmd start="\<Semi\>" end="\.\_s"
syn region coqAddLegacyOption   contained matchgroup=coqVernacCmd start="\<Field\>" end="\.\_s"
syn region coqAddOption         contained matchgroup=coqVernacCmd start="\<Field\>" end="\.\_s"
syn region coqAddOption         contained matchgroup=coqVernacCmd start="\<Relation\>" end="\.\_s"
syn region coqAddOption         contained matchgroup=coqVernacCmd start="\<Ring\>" end="\.\_s"
syn region coqAddOption         contained matchgroup=coqVernacCmd start="\<Setoid\>" end="\.\_s"
syn region coqAddOption         contained matchgroup=coqVernacCmd start="\<Morphism\>" end="\.\_s"
syn region coqAddOption         contained contains=coqAddOption2 matchgroup=coqVernacCmd start="\<Rec\>" end="\.\_s"
syn region coqAddOption2        contained contains=coqString matchgroup=coqVernacCmd start="\<LoadPath\>" end="\.\_s"
syn region coqAddOption2        contained contains=coqAddMLPath matchgroup=coqVernacCmd start="\<ML\>" end="\.\_s"
syn region coqAddMLPath         contained contains=coqString matchgroup=coqVernacCmd start="\<Path\>" end="\.\_s"

" Set
syn region coqSet       contains=coqSetOption matchgroup=coqVernacCmd start="\<Set\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqSetOption           contained contains=coqSetPrintingOption matchgroup=coqVernacCmd start="\<Printing\>" end="\.\_s"
syn region coqSetPrintingOption   contained matchgroup=coqVernacCmd start="\<\%(Coercions\|All\|Implicit\|Matching\|Notations\|Synth\|Universes\|Wildcard\)\>" end="\.\_s"
syn region coqSetPrintingOption   contained matchgroup=coqVernacCmd start="\<\%(Width\|Depth\)\>" end="\.\_s"
syn region coqSetPrintingOption   contained matchgroup=coqVernacCmd start="\<Coercion\>" end="\.\_s"
syn region coqSetOption           contained matchgroup=coqVernacCmd start="\<\%(Silent\|Virtual\_s\+Machine\)\>" end="\.\_s"
syn region coqSetOption           contained matchgroup=coqVernacCmd start="\<Undo\>" end="\.\_s"
syn region coqSetOption           contained matchgroup=coqVernacCmd start="\<Hyps\>" end="\.\_s"
syn region coqSetHypsOtion        contained matchgroup=coqVernacCmd start="\<Limit\>" end="\.\_s"
syn region coqSetOption           contained contains=coqContextOption matchgroup=coqVernacCmd start="\<\%(Contextual\|Strict\)\>" end="\.\_s"
syn region coqContextOption       contained matchgroup=coqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region coqSetOption           contained contains=coqExtractOption matchgroup=coqVernacCmd start="\<Extraction\>" end="\.\_s"
syn region coqExtractOption       contained matchgroup=coqVernacCmd start="\<\%(AutoInline\|Optimize\)\>" end="\.\_s"
syn region coqSetOption           contained contains=coqSetFirstorderOption matchgroup=coqVernacCmd start="\<Firstorder\>" end="\.\_s"
syn region coqSetFirstorderOption contained matchgroup=coqVernacCmd start="\<Depth\>" end="\.\_s"
syn region coqSetOption           contained contains=coqImplicitOption matchgroup=coqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region coqImplicitOption      contained matchgroup=coqVernacCmd start="\<Arguments\>" end="\.\_s"
syn region coqSetOption           contained contains=coqLtacOption matchgroup=coqVernacCmd start="\<Ltac\>" end="\.\_s"
syn region coqLtacOption          contained matchgroup=coqVernacCmd start="\<Debug\>" end="\.\_s"
syn region coqSetOption           contained contains=coqLtacOption matchgroup=coqVernacCmd start="\<Transparent\_s\+Obligations\>" end="\.\_s"

" Unset
syn region coqUnset       contains=coqUnsetOption matchgroup=coqVernacCmd start="\<Unset\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqUnsetOption           contained contains=coqUnsetPrintingOption matchgroup=coqVernacCmd start="\<Printing\>" end="\.\_s"
syn region coqUnsetPrintingOption   contained matchgroup=coqVernacCmd start="\<\%(Coercions\?\|All\|Implicit\|Matching\|Notations\|Synth\|Universes\|Wildcard\|Width\|Depth\)\>" end="\.\_s"
syn region coqUnsetOption           contained matchgroup=coqVernacCmd start="\<\%(Silent\|Virtual\_s\+Machine\)\>" end="\.\_s"
syn region coqUnsetOption           contained matchgroup=coqVernacCmd start="\<Undo\>" end="\.\_s"
syn region coqUnsetOption           contained matchgroup=coqVernacCmd start="\<Hyps\>" end="\.\_s"
syn region coqUnsetHypsOtion        contained matchgroup=coqVernacCmd start="\<Limit\>" end="\.\_s"
syn region coqUnsetOption           contained contains=coqContextOption matchgroup=coqVernacCmd start="\<\%(Contextual\|Strict\)\>" end="\.\_s"
syn region coqContextOption         contained matchgroup=coqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region coqUnsetOption           contained contains=coqExtractOption matchgroup=coqVernacCmd start="\<Extraction\>" end="\.\_s"
syn region coqExtractOption         contained matchgroup=coqVernacCmd start="\<\%(AutoInline\|Optimize\)\>" end="\.\_s"
syn region coqUnsetOption           contained contains=coqUnsetFirstorderOption matchgroup=coqVernacCmd start="\<Firstorder\>" end="\.\_s"
syn region coqUnsetFirstorderOption contained matchgroup=coqVernacCmd start="\<Depth\>" end="\.\_s"
syn region coqUnsetOption           contained contains=coqImplicitOption matchgroup=coqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region coqImplicitOption        contained matchgroup=coqVernacCmd start="\<Arguments\>" end="\.\_s"
syn region coqUnsetOption           contained contains=coqLtacOption matchgroup=coqVernacCmd start="\<Ltac\>" end="\.\_s"
syn region coqLtacOption            contained matchgroup=coqVernacCmd start="\<Debug\>" end="\.\_s"

" Eval
syn region coqEval      contains=coqEvalTac matchgroup=coqVernacCmd start="\<Eval\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqEvalTac   contained contains=coqEvalIn matchgroup=coqTactic start="\<\%(\%(vm_\)\?compute\|red\|hnf\|simpl\|fold\)\>" end="\.\_s" keepend
syn region coqEvalTac   contained contains=coqEvalFlag,coqEvalIn matchgroup=coqTactic start="\<\%(cbv\|lazy\)\>" end="\.\_s"
syn keyword coqEvalFlag contained beta delta iota zeta
syn region coqEvalFlag  contained start="-\?\[" end="\]"
syn region coqEvalTac   contained contains=@coqTerm,coqEvalIn matchgroup=coqTactic start="\<\%(unfold\|pattern\)\>" end="\.\_s"
syn region coqEvalIn    contained contains=@coqTerm matchgroup=coqVernacCmd start="in" matchgroup=coqVernacPunctuation end="\.\_s"

" Notations
syn region coqNSNotation matchgroup=coqVernacCmd start="\<\%(Numeral\|String\)\_s\+Notation\>" contains=coqIdent,coqNotationScope end="\.\_s" keepend
syn region coqNotation     contains=coqNotationDef start="\%(\%(\%(\<Reserved\>\_s*\)\?\<Notation\>\)\|\<Infix\>\)" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqNotationDef       contained contains=coqNotationString,coqNotationTerm matchgroup=coqVernacCmd start="\%(\%(\%(\<Reserved\>\_s*\)\?\<Notation\>\)\|\<Infix\>\)" end="\.\_s"
syn region coqNotationTerm      contained contains=coqNotationExpr matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqNotationExpr      contained contains=@coqTerm,coqNotationEndExpr matchgroup=coqTermPunctuation start="(" end="\.\_s"
syn region coqNotationEndExpr   contained contains=coqNotationFormat,coqNotationScope matchgroup=coqTermPunctuation start=")" end="\.\_s"
syn region coqNotationExpr      contained contains=@coqTerm,coqNotationFormat,coqNotationScope start="[^[:blank:](]" matchgroup=NONE end="\.\_s"
syn region coqNotationFormat    contained contains=coqNotationKwd,coqString,coqNotationEndFormat matchgroup=coqVernacPunctuation start="(" end="\.\_s"
syn region coqNotationEndFormat contained contains=coqNotationScope matchgroup=coqVernacPunctuation start=")" end="\.\_s"
syn region coqNotationScope     contained matchgroup=coqVernacPunctuation start=":" end="\.\_s"

syn match   coqNotationKwd contained "at \(next \)\?level"
syn match   coqNotationKwd contained "\(no\|left\|right\) associativity"
syn match   coqNotationKwd contained "only parsing"
syn match   coqNotationKwd contained "(\|,\|)\|:"
syn keyword coqNotationKwd contained ident global bigint format

syn region coqNotationString contained start=+"+ skip=+""+ end=+"+ extend

" Tactic notations
syn region coqTacNotation     contains=coqTacNotationDef start="\<Tactic\_s\+Notation\>" end="\.\_s" keepend
syn region coqTacNotationDef  contained contains=coqNotationString,coqTacNotationKwd,coqTacNotationTerm matchgroup=coqVernacCmd start="Tactic\_s\+Notation" end="\.\_s"
syn region coqTacNotationTerm contained contains=coqString,coqTactic,coqTacticKwd,coqLtac,coqProofPunctuation matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

syn keyword coqTacNotationKwd contained ident simple_intropattern hyp reference constr integer int_or_var tactic
syn match   coqTacNotationKwd contained "at level"

" Declarations
syn region coqDecl       contains=coqIdent,coqDeclTerm,coqDeclBinder matchgroup=coqVernacCmd start="\<\%(Axioms\?\|Conjectures\?\|Hypothes[ie]s\|Parameters\?\|Variables\?\|Context\)\>" matchgroup=coqVernacCmd end="\.\_s" keepend
syn region coqDeclBinder contained contains=coqIdent,coqDeclTerm matchgroup=coqVernacPunctuation start="(" end=")" keepend
syn region coqDeclTerm   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end=")"
syn region coqDeclTerm   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end="\.\_s"

" Theorems
syn region coqThm       contains=coqThmName matchgroup=coqVernacCmd start="\<\%(Program\_s\+\)\?\%(Theorem\|Lemma\|Example\|Corollary\|Remark\|Fact\|Proposition\)\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s" keepend
syn region coqThmName   contained contains=coqThmTerm,coqThmBinder matchgroup=coqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s"
syn region coqThmTerm   contained contains=@coqTerm,coqProofBody matchgroup=coqVernacCmd start=":" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>"
syn region coqThmBinder contained matchgroup=coqVernacPunctuation start="(" end=")" keepend

syn region coqGoal      contains=coqGoalTerm start="\<Goal\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>" keepend
syn region coqGoalTerm  contained contains=@coqTerm,coqProofBody matchgroup=coqVernacCmd start="Goal" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>" keepend

" Ltac
syn region coqLtacDecl     contains=coqLtacProfile start="\<Ltac\>" end="\.\_s" keepend
syn region coqLtacProfile  contained contains=coqLtacIdent,coqVernacPunctuation,coqLtacContents start="Ltac" end="\.\_s"
syn region coqLtacIdent    contained matchgroup=coqVernacCmd start="Ltac" matchgroup=coqIdent end="[_[:alpha:]][_'[:alnum:]]*"
syn region coqLtacContents contained contains=coqTactic,coqTacticKwd,coqLtac,coqProofPunctuation matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

syn keyword coqLtac contained do info progress repeat try
syn keyword coqLtac contained abstract constr context end external eval fail first fresh fun goal
syn keyword coqLtac contained idtac in let ltac lazymatch multimatch match of rec reverse solve type with
syn match   coqLtac contained "|-\|=>\|||\|\[\|\]\|\<_\>\||"

" Proofs
" TODO: The \ze in the start match is a terrible hack so coqProofDelim will still
" be matched and the dot will be highlighted as coqProofDot. I assume there is a
" better way but I don't know what it is.
syn region coqProofBody  contains=coqProofPunctuation,coqTactic,coqTacticKwd,coqProofComment,coqProofKwd,coqProofEnder,coqProofDelim,coqLtac matchgroup=coqProofDelim start="\<P\zeroof\>" start="\<\%(O\zebligation\_s\+\d\+\)\|\%(N\zeext\_s\+Obligation\)\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s" end="\<Save\>.*\.\_s" keepend
syn region coqProofDelim contained matchgroup=coqProofDelim start="\%(\<P\)\@1<=roof\>" matchgroup=coqProofDot end="\.\_s"
syn region coqProofDelim contained contains=coqOblOfDelim start="\%(\%(\<O\)\@1<=bligation\_s\+\d\+\)\|\%(\%(\<N\)\@1<=ext\_s\+Obligation\)\>" matchgroup=coqProofDot end="\.\_s" keepend
syn region coqProofEnder contained matchgroup=coqProofDelim start="\<\%(Qed\|Defined\)\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqProofEnder contained matchgroup=coqProofAdmit start="\<\%(Abort\|Admitted\)\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqProofEnder contained contains=coqIdent matchgroup=coqProofDelim start="\<Save\>" matchgroup=coqVernacPunctuation end="\.\_s"

syn keyword coqTactic    contained absurd apply assert assumption auto
syn keyword coqTactic    contained case[_eq] change clear[body] cofix cbn cbv compare compute congruence constructor contradiction cut[rewrite]
syn keyword coqTactic    contained decide decompose dependent destruct discriminate double
syn keyword coqTactic    contained eapply eassumption eauto econstructor elim[type] equality erewrite evar exact eexact exists eexists exfalso
syn keyword coqTactic    contained fix cofix f_equal fold functional generalize hnf
syn keyword coqTactic    contained idtac induction injection instantiate intro[s] intuition inversion[_clear]
syn keyword coqTactic    contained lapply left move omega pattern pose proof quote
syn keyword coqTactic    contained red refine reflexivity rename replace revert rewrite right ring
syn keyword coqTactic    contained set simpl[e] simplify_eq specialize split subst stepl stepr symmetry
syn keyword coqTactic    contained transitivity trivial unfold vm_compute
syn keyword coqTacticKwd contained as by in using with into after until return

" The following is just to help other plugins to detect via syntax groups that we are inside a proof
syn keyword coqProofKwd         contained else end exists exists2 forall fun if in match let struct then where with as return
syn match   coqProofKwd         contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|="
syn match   coqProofPunctuation contained "(\|)\|:=\|:>\|:\|\.\|;\|,\|||\|\[\|\]\|@\|?"
syn region  coqProofComment     contained contains=coqProofComment,coqTodo start="(\*" end="\*)" extend keepend

" Definitions
syn region coqDef          contains=coqDefName matchgroup=coqVernacCmd start="\<\%(Program\_s\+\)\?\%(Definition\|Let\|Example\)\>" matchgroup=coqVernacPunctuation end=":="me=e-2 end="\.$"me=e-1 end="\.\_s"me=e-2 nextgroup=coqDefContents1,coqProofBody keepend skipnl skipwhite skipempty
syn region coqDefName       contained contains=coqDefBinder,coqDefType,coqDefContents1 matchgroup=coqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="\.\_s" end=":="
syn region coqDefBinder     contained contains=coqDefBinderType matchgroup=coqVernacPunctuation start="(" end=")" keepend
syn region coqDefBinderType contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end=")"
syn region coqDefType       contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="\.\_s" end=":="
syn region coqDefContents1  contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":=" matchgroup=coqVernacPunctuation end="\.\_s"

" Coercions
syn region coqCoercion      contains=coqCoercionName,coqCoercionBody1,coqCoercionBody2 matchgroup=coqVernacCmd start="\<\%(Identity\_s\+\)\?Coercion\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqCoercionName  contained contains=coqDefBinder,coqDefType matchgroup=coqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end=":="me=e-2 end=">->"me=e-3 keepend
syn region coqCoercionBody1 contained contains=coqIdent matchgroup=coqVernacPunctuation start=">->" end="\.\_s""
syn region coqCoercionBody2 contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":=" end="\.\_s""

" Fixpoints
syn region coqFix     contains=coqFixBody start="\<\%(Program\_s\+\)\?\%(\%(\%(Co\)\?Fixpoint\)\|Fixpoint\|Function\)\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqFixBody       contained contains=coqFixName matchgroup=coqVernacCmd start="\%(\%(\%(Co\)\?Fixpoint\)\|Function\)" start="\<with\>" matchgroup=NONE end="\.\_s"
syn region coqFixName       contained contains=coqFixBinder,coqFixAnnot,coqFixTerm,coqFixContent matchgroup=coqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="\.\_s"
syn region coqFixBinder     contained contains=coqFixBinderType matchgroup=coqVernacPunctuation start="(" end=")" keepend
syn region coqFixBinderType contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end=")" keepend
syn region coqFixAnnot      contained contains=@coqTerm matchgroup=coqVernacPunctuation start="{\_s*struct" end="}" keepend
syn region coqFixTerm       contained contains=@coqTerm,coqFixContent matchgroup=coqVernacPunctuation start=":" end="\.\_s"
syn region coqFixContent    contained contains=coqFixBody,@coqTerm,coqKwdMatch,coqFixNot matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqFixNot        contained contains=coqNotationString,coqFixNotTerm matchgroup=coqVernacCmd start="\<where\>" end="\.\_s"
syn region coqFixNotTerm    contained contains=@coqTerm,coqFixBody,coqFixNotScope matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqFixNotScope   contained contains=coqFixBody matchgroup=coqVernacPunctuation start=":" end="\.\_s"

" Inductives
syn region coqInd            contains=coqIndBody start="\<\%(Co\)\?Inductive\>\|\<Variant\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqIndBody     contained contains=coqIdent,coqIndTerm,coqIndBinder matchgroup=coqVernacCmd start="\%(\%(Co\)\?Inductive\)\|Variant" start="\<with\>" matchgroup=NONE end="\.\_s"
syn region coqIndBinder      contained contains=coqIndBinderTerm matchgroup=coqVernacPunctuation start="("  end=")" keepend
syn region coqIndBinderTerm  contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end=")"
syn region coqIndTerm        contained contains=@coqTerm,coqIndContent matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="\.\_s"
syn region coqIndContent     contained contains=coqIndConstructor start=":=" end="\.\_s"
syn region coqIndConstructor contained contains=coqConstructor,coqIndBinder,coqIndConsTerm,coqIndNot,coqIndBody matchgroup=coqVernacPunctuation start=":=\%(\_s*|\)\?" start="|" matchgroup=NONE end="\.\_s"
syn region coqIndConsTerm    contained contains=coqIndBody,@coqTerm,coqIndConstructor,coqIndNot matchgroup=coqConstructor start=":" matchgroup=NONE end="\.\_s"
syn region coqIndNot         contained contains=coqNotationString,coqIndNotTerm matchgroup=coqVernacCmd start="\<where\>" end="\.\_s"
syn region coqIndNotTerm     contained contains=@coqTerm,coqIndNotScope,coqIndBody matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqIndNotScope    contained contains=coqIndBody matchgroup=coqVernacPunctuation start=":" end="\.\_s"
syn match  coqConstructor    contained "[_[:alpha:]][_'[:alnum:]]*"

" Records
syn region coqRec        contains=coqRecProfile start="\<Record\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqRecProfile contained contains=coqIdent,coqRecTerm,coqRecBinder matchgroup=coqVernacCmd start="Record" matchgroup=NONE end="\.\_s"
syn region coqRecBinder  contained contains=@coqTerm matchgroup=coqTermPunctuation start="("  end=")"
syn region coqRecTerm    contained contains=@coqTerm,coqRecContent matchgroup=coqVernacPunctuation start=":"  end="\.\_s"
syn region coqRecContent contained contains=coqConstructor,coqRecStart matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqRecStart   contained contains=coqRecField,@coqTerm start="{" matchgroup=coqVernacPunctuation end="}" keepend
syn region coqRecField   contained contains=coqField matchgroup=coqVernacPunctuation start="{" end=":"
syn region coqRecField   contained contains=coqField matchgroup=coqVernacPunctuation start=";" end=":"
syn match coqField       contained "[_[:alpha:]][_'[:alnum:]]*"

" Typeclasses
syn region coqCls        contains=coqClsProfile start="\<Class\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqClsProfile contained contains=coqIdent,coqRecTerm,coqRecBinder matchgroup=coqVernacCmd start="Class" matchgroup=NONE end="\.\_s"

" Typeclass instances
syn region coqIns contains=coqDefName matchgroup=coqVernacCmd start="\<\%(Declare\_s\+\)\?Instance\>" matchgroup=coqVernacPunctuation end=":="me=e-2 end="\.$"me=e-1 end="\.\_s"me=e-2 nextgroup=coqDefContents1,coqProofBody keepend skipnl skipwhite skipempty
syn region coqIns matchgroup=coqVernacCmd start="\<Existing\_s\+Instance\>" matchgroup=coqVernacPunctuation end="\.$"me=e-1 end="\.\s"me=e-2

" Equations
syn region coqEqn           contains=coqEqnProfile start="\<Equations?\?\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqEqnProfile    contained contains=coqIdent,coqEqnTerm,coqEqnBinder matchgroup=coqVernacCmd start="Equations?\?" matchgroup=NONE end="\.\_s"
syn region coqEqnBinder     contained contains=coqEqnOptions,@coqTerm matchgroup=coqTermPunctuation start="(" end=")"
syn region coqEqnTerm       contained contains=@coqTerm,coqEqnContent matchgroup=coqVernacPunctuation start=":" end="\.\_s"
syn region coqEqnContent    contained contains=coqEqnBrackClause,coqEqnWhereClause,coqEqnClause matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqEqnBrackClause contained contains=@coqTerm,coqEqnClause,coqEqnKwd matchgroup=coqVernacPunctuation start="{" end="}"
syn region coqEqnWhereClause contained contains=@coqTerm,coqEqnClause,coqEqnKwd matchgroup=coqEqnKwd start="\<where\>" matchgroup=coqVernacPunctuation end=":="
syn region coqEqnClause     contained contains=@coqTerm,coqEqnKwd matchgroup=coqVernacPunctuation start=";" start=":=" end=":=" end="=>"
syn keyword coqEqnKwd       contained with where
syn keyword coqEqnOptions   contained noind noeqns

syn region coqDerive        contains=coqDeriveCmds,coqIdent start="\<Derive\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqDeriveCmds    contained contains=coqDeriveCmd matchgroup=coqVernacCmd start="\<Derive\>" end="\<for\>"
syn keyword coqDeriveCmd    contained DependentEliminationPackage Signature NoConfusion
syn keyword coqDeriveCmd    contained NoConfusionHom EqDec Subterm

" Extraction
syn keyword coqExtrLangEnum contained OCaml Haskell Scheme
syn region coqExtrLang matchgroup=coqVernacCmd start="\<Extraction\_s\+Language\>" contains=coqExtrLangEnum end="\.\_s"
" TODO: ^ make typos/wrong languages stand out
syn region coqExtrBlacklist matchgroup=coqVernacCmd start="\<Extraction\_s\+Blacklist\>" contains=coqIdent end="\.\_s"
syn region coqExtr matchgroup=coqVernacCmd start="\<Extraction\>" contains=coqString,coqIdent end="\.\_s"
" TODO: ^ string only allowed at the beginning of 'Extraction'
syn region coqRSExtr matchgroup=coqVernacCmd start="\<\%(Recursive\_s\+\|Separate\_s\+\)Extraction\>" contains=coqIdent end="\.\_s"
syn region coqExtrLib matchgroup=coqVernacCmd start="\<\%(Recursive\_s\+\)\?Extraction\_s\+Library\>" contains=coqIdent end="\.\_s"
syn region coqExtrConst matchgroup=coqVernacCmd start="\<Extract\_s\+\%(Inlined\_s\+\)\?Constant\>" contains=coqIdent,coqBigArrow,coqString end="\.\_s"
" TODO: ^ Enforce order of tokens: ident => "string"
syn match coqBigArrow contained "=>"

" Various (High priority)
syn region  coqComment           containedin=ALL contains=coqComment,coqTodo start="(\*" end="\*)" extend keepend
syn keyword coqTodo              contained TODO FIXME XXX NOTE
syn region  coqString            start=+"+ skip=+""+ end=+"+ extend

" Define the default highlighting.
command -nargs=+ HiLink hi def link <args>

" PROOFS
HiLink coqTactic            Keyword
HiLink coqLtac              coqTactic
HiLink coqProofKwd          coqTactic
HiLink coqProofPunctuation  coqTactic
HiLink coqTacticKwd         coqTactic
HiLink coqTacNotationKwd    coqTactic
HiLink coqEvalFlag          coqTactic
HiLink coqEqnKwd            coqTactic
" Exception
HiLink coqProofDot          coqVernacular

" PROOF DELIMITERS ("Proof", "Qed", "Defined", "Save")
HiLink coqProofDelim        Underlined

" TERMS AND TYPES
HiLink coqTerm              Type
HiLink coqKwd               coqTerm
HiLink coqTermPunctuation   coqTerm

" VERNACULAR COMMANDS
HiLink coqVernacular        PreProc
HiLink coqVernacCmd         coqVernacular
HiLink coqVernacPunctuation coqVernacular
HiLink coqFeedback          coqVernacular
HiLink coqTopLevel          coqVernacular

" DEFINED OBJECTS
HiLink coqIdent             Identifier
HiLink coqNotationString    coqIdent

" CONSTRUCTORS AND FIELDS
HiLink coqConstructor       Keyword
HiLink coqField             coqConstructor

" NOTATION SPECIFIC ("at level", "format", etc)
HiLink coqNotationKwd       Special
HiLink coqEqnOptions        coqNotationKwd

" USUAL VIM HIGHLIGHTINGS
" Comments
HiLink coqComment           Comment
HiLink coqProofComment      coqComment

" Todo
HiLink coqTodo              Todo

" Errors
HiLink coqError             Error
HiLink coqProofAdmit        coqError

" Strings
HiLink coqString            String

delcommand HiLink
