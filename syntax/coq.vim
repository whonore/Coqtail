" Vim syntax file
" Language:     Coq
" Filenames:    *.v
" Maintainer:  Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Last Change: 2008 Dec 02 - Added the Program and Obligation constructions (in Coq v8.2) - with Serge Leblanc.
"              2008 Jan 30 - Applied the improvments for all constructions, added 'with' and 'where' for
"                            fixpoints and inductives, fixed some hard long standing bugs.
"              2008 Jan 27 - Changed the way things are coloured, improved the efficiency of colouring.
"              2008 Jan 25 - Added Ltac, added Notations, bugfixes.
"              2007 Dec 1 - Added Record's.
"              2007 Nov 28 - Added things to reuse (in other plugins) the knowledge that we are inside a proof.
"              2007 Nov 19 - Fixed bug with comments.
"              2007 Nov 17 - Various minor bugfixes.
"              2007 Nov 8 - Added keywords.
"              2007 Nov 8 - Fixed some ill-highlighting in the type of declarations.
"              2007 Nov 8 - Fixed pb with keywords ("\<...\>" had been forgotten)
"                           (thanks to Vasileios Koutavas)
"              2007 Nov 8 - Definition...Defined now works as expected,
"                           fixed a bug with tactics that were not recognized,
"                           fixed other bugs
"              2007 Nov 7 - Complete refactoring, (much) more accurate highlighting. Much bigger file...
"              2007 Nov 7 - Added tactic colouration, added other keywords (thanks to Tom Harke)
"              2007 Nov 6 - Added "Defined" keyword (thanks to Serge Leblanc)
"              2007 Nov 5 - Initial version.
" License:     public domain
" Modified By: Wolf Honore
" TODO: mark bad constructions (eg. Section ended but not opened)

" Define Coqtail-specific highlighting groups.
if !exists('b:coqtail_did_highlight') || !b:coqtail_did_highlight
  function! s:CoqtailHighlight() abort
    if exists('*g:CoqtailHighlight')
      " Use user-defined colors if they exist.
      " NOTE: This is only for backwards compatability. Use
      " `autocmd ColorScheme` instead.
      call g:CoqtailHighlight()
    elseif &t_Co > 16
      hi def CoqtailChecked ctermbg=17 guibg=LightGreen
      hi def CoqtailSent ctermbg=60 guibg=LimeGreen
    else
      hi def CoqtailChecked ctermbg=4 guibg=LightGreen
      hi def CoqtailSent ctermbg=7 guibg=LimeGreen
    endif
    hi def link CoqtailDiffAdded DiffText
    hi def link CoqtailDiffAddedBg DiffChange
    hi def link CoqtailDiffRemoved DiffDelete
    hi def link CoqtailDiffRemovedBg DiffDelete
    hi def link CoqtailError Error
    hi def link CoqtailOmitted coqProofAdmit
  endfunction

  call s:CoqtailHighlight()
  " NOTE: Setting a colorscheme usually calls 'syntax clear' so have to set
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

" NOTE: Must be here and not in ftplugin. The Verilog syntax file resets it and
" ftplugin is only sourced once so it is lost when a buffer is reloaded.
" Keywords are alphanumeric, _, and '
setlocal iskeyword=@,48-57,192-255,_,'
syn iskeyword clear

" Coq is case sensitive.
syn case match

" Various
syn match   coqError             "\S\+"
syn match   coqVernacPunctuation ":=\|\.\|:"
syn match   coqIdent             contained "[[:digit:]']\@!\k\k*"
syn keyword coqTopLevel          Type Structure Cd Drop Existential
"...
syn keyword coqVernacCmd         Local Global Polymorphic Functional Scheme Back Combined
syn keyword coqVernacCmd         Fail Succeed
syn keyword coqFeedback          Show

syn region coqQuery contains=@coqTerm matchgroup=coqVernacCmd start="\<\%(About\|Check\)\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqLocate matchgroup=coqVernacCmd start="\<Locate\%(\_s\+\%(Term\|Module\|Ltac\|Library\|File\)\)\?\>" contains=@coqTerm end="\.\_s"
syn region coqPrint matchgroup=coqVernacCmd start="\<Print\%(\_s\+\%(Term\|All\|Section\|Ltac\|Notation\)\)\?\>" contains=@coqTerm end="\.\_s"
syn region coqPrintDep matchgroup=coqVernacCmd start="\<Print\%(\_s\+\%(Assumptions\|\%(Opaque\|Transparent\|All\)\_s\+Dependencies\)\)\?\>" contains=@coqTerm end="\.\_s"
syn region coqPrintMisc matchgroup=coqVernacCmd start="\<Print\%(\_s\+\%(Canonical\_s\+Projections\|Classes\|Coercion\_s\+Paths\|Coercions\|Custom\_s\+Grammar\|Debug\_s\+GC\|Extraction\_s\+\%(Blacklist\|Inline\)\|Firstorder\_s\+Solver\|Grammar\|\|Graph\|Hint\|HintDb\|Implicit\|Instances\|Libraries\|LoadPath\|Ltac\_s\+Signatures\|ML\_s\+\%(Modules\|Path\)\|Options\|Rewrite\_s\+HintDb\|Rings\|Scopes\?\|Strateg\%(y\|ies\)\|Tables\?\|Typing\_s\+Flags\|Universes\%(\_s\+Subgraph\)\?\|Visibility\)\)\?\>" contains=@coqTerm end="\.\_s"
" TODO: recognize special search syntax (e.g., `inside`, `head:`, etc)
syn region coqSearch matchgroup=coqVernacCmd start="\<Search\%(Pattern\|Rewrite\)\?\>" contains=@coqTerm end="\.\_s"

" Modules
syn region coqModule contains=TOP matchgroup=coqVernacCmd start="\<Module\%(\_s\+\%(Type\|Import\|Export\)\)\?\_s\+\z(\%(\%(Type\|Import\|Export\)\_s\)\@![[:digit:]']\@!\k\k*\)\%([^=]*\.\_s\)\@=" end="\<End\_s\+\z1\_s*\.\_s" fold
syn region coqModule contains=TOP matchgroup=coqVernacCmd start="\<Module\%(\_s\+\%(Type\|Import\|Export\)\)\?\_s\+\z(\%(\%(Type\|Import\|Export\)\_s\)\@![[:digit:]']\@!\k\k*\)\%(.*:=\)\@=" end=":="me=e-2 nextgroup=coqModVal
syn region coqModBinder containedin=coqModule contains=coqIdent matchgroup=coqVernacPunctuation start="(" end=")" keepend
syn region coqModVal contains=coqIdent,coqTermPunctuation start=":=" end="\.\_s"

" Terms
syn cluster coqTerm            contains=coqKwd,coqTermPunctuation,coqKwdMatch,coqKwdLet,coqKwdParen,coqString,coqAttribute
syn region coqKwdMatch         contained contains=@coqTerm matchgroup=coqKwd start="\<match\>" end="\<with\>"
syn region coqKwdLet           contained contains=@coqTerm matchgroup=coqKwd start="\<let\>"   end=":="
syn region coqKwdParen         contained contains=@coqTerm matchgroup=coqTermPunctuation start="(" end=")" keepend extend
syn keyword coqKwd             contained else end exists2 fix cofix forall fun if in struct then as return
syn match   coqKwd             contained "\<where\>"
syn match   coqKwd             contained "\<exists!\?\>"
syn match   coqKwd             contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|-\|*\|=\|>\|<\|<="
syn match coqTermPunctuation   contained ":=\|:>\|:\|;\|,\|||\|\[\|\]\|@\|?\|\<_\>\|<+"

" Various
syn region coqRequire contains=coqString matchgroup=coqVernacCmd start="\<Require\>\%(\_s\+\%(Export\|Import\)\>\)\?" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqRequire matchgroup=coqVernacCmd start="\<Import\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqRequire matchgroup=coqVernacCmd start="\<Export\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqRequire matchgroup=coqVernacCmd start="\<Include\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqRequire contains=coqString,coqRequire matchgroup=coqVernacCmd start="\<From\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqCompute contains=@coqTerm matchgroup=coqVernacCmd start="\<Compute\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqOpaque  matchgroup=coqVernacCmd start="\%(\<Typeclasses\_s\+\)\?\<\%(Opaque\|Transparent\)\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqShow       matchgroup=coqVernacCmd start="\<Show\_s\+\%(\%(Implicits\|Script\|Tree\|Proof\|Conjectures\|Intros\?\|Existentials\)\>\)\?" end="\.\_s"
syn region coqImplicitTypes matchgroup=coqVernacCmd start="\<Implicit Types\?" end="\.\_s"
syn region coqGeneralizable matchgroup=coqVernacCmd start="\<Generalizable\_s\+\%(\%(All\|No\)\_s\+\)\?Variables\?" end="\.\_s"
syn region coqDeclareML contains=coqString matchgroup=coqVernacCmd start="\<Declare\_s\+ML\_s\+Module\>" end="\.\_s"

syn region  coqRegister contains=coqRegisterKwd matchgroup=coqVernacCmd start="\<Register\>" end="\.\_s"
syn region  coqRegister matchgroup=coqVernacCmd start="\<Register\_s\+Inline\>" end="\.\_s"
syn keyword coqRegisterKwd contained as

" Attributes
syn region coqAttribute contains=coqString,coqAttrBool,coqAttrPunc,coqIdent start="#\[" end="]"
syn keyword coqAttrBool contained yes no
syn match coqAttrPunc contained "=\|,\|(\|)"

" Sections
syn region coqSection contains=TOP matchgroup=coqVernacCmd start="\<Section\_s\+\z(\S\+\)\_s*\.\_s" end="\<End\_s\+\z1\_s*\.\_s" fold

" Obligations
syn region coqObligation contains=coqOblOf   matchgroup=coqVernacCmd start="\<\%(Obligations\)\|\%(Preterm\)\>" end="\.\_s" keepend
syn region coqObligation contains=coqOblOf   matchgroup=coqProofAdmit start="\<Admit\_s\+Obligations\>" matchgroup=coqVernacCmd end="\.\_s" keepend
syn region coqObligation contains=coqOblOf   matchgroup=coqVernacCmd start="\<Solve\_s\+Obligations\>" end="\.\_s" keepend
syn region coqOblOf      contains=coqIdent,coqOblUsing matchgroup=coqVernacCmd start="\<of\>" end="\.\_s" keepend
syn region coqOblOfDelim contains=coqIdent,coqOblUsing matchgroup=coqProofDelim start="\<of\>" matchgroup=coqProofDot end="\.\_s" keepend
syn region coqObligation contains=coqOblUsing   matchgroup=coqVernacCmd start="\<Solve\_s\+All\_s\+Obligations\>" end="\.\_s" keepend
syn region coqOblUsing   contains=coqLtac   matchgroup=coqVernacCmd start="\<using\>" end="\.\_s"
syn region coqObligation contains=coqOblExpr matchgroup=coqVernacCmd start="\<Obligation\_s\+Tactic\>" end="\.\_s" keepend
syn region coqOblExpr    contains=coqLtac   matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

" Scopes
syn region coqBind    contains=coqScope matchgroup=coqVernacCmd start="\<Bind\|Delimit\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqDeclareScope contains=coqIdent matchgroup=coqVernacCmd start="\<Declare\_s\+Scope\>" end="\.\_s"
syn region coqArgsScope contains=coqScope matchgroup=coqVernacCmd start="\<Arguments\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqOpen    contains=coqScope matchgroup=coqVernacCmd start="\<Open\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqClose   contains=coqScope matchgroup=coqVernacCmd start="\<Close\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqScope   contained matchgroup=coqVernacCmd start="\<Scope\>" end="\.\_s"

" Hints
syn region coqCreateHintDb matchgroup=coqVernacCmd start="\<Create\_s\+HintDb\>" contains=coqIdent end="\.\_s" keepend
syn region coqHint contains=coqHintOption start="\<Hint\>" end="\.\_s" keepend
syn region coqHintOption start="\<\%(Resolve\|Immediate\|Constructors\|Unfold\|Extern\)\>" end="\.\_s"

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
syn region coqNSNotation matchgroup=coqVernacCmd start="\<\%(Number\|Numeral\|String\)\_s\+Notation\>" contains=coqIdent,coqNotationScope end="\.\_s" keepend
syn region coqNotation     contains=coqNotationDef start="\%(\%(\%(\<Reserved\>\_s*\)\?\<Notation\>\)\|\<Infix\>\)" matchgroup=coqVernacPunctuation end="\.\@<!\.\_s" keepend
syn region coqNotationDef       contained contains=coqNotationString,coqNotationTerm matchgroup=coqVernacCmd start="\%(\%(\%(\<Reserved\>\_s*\)\?\<Notation\>\)\|\<Infix\>\)" end="\.\@<!\.\_s"
syn region coqDeclareEntry contains=coqIdent matchgroup=coqVernacCmd start="\<Declare\_s\+Custom\_s\+Entry\>" end="\.\_s"
syn region coqNotationTerm      contained contains=coqNotationExpr matchgroup=coqVernacPunctuation start=":=" end="\.\@\<!\.\_s"
syn region coqNotationExpr      contained contains=@coqTerm,coqNotationEndExpr matchgroup=coqTermPunctuation start="(" end="\.\@\<!\.\_s"
syn region coqNotationEndExpr   contained contains=coqNotationFormat,coqNotationScope matchgroup=coqTermPunctuation start=")" end="\.\@<!\.\_s"
syn region coqNotationExpr      contained contains=@coqTerm,coqNotationFormat,coqNotationScope start="[^[:blank:](]" matchgroup=NONE end="\.\@<!\.\_s"
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
syn region coqTacNotationTerm contained contains=coqString,coqTactic,coqTacticKwd,coqTacticAdmit,coqLtac,coqProofPunctuation matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

syn keyword coqTacNotationKwd contained ident simple_intropattern hyp reference constr integer int_or_var tactic
syn match   coqTacNotationKwd contained "at level"

" Binders
syn region coqBinder            contained contains=coqIdent,coqBinderTypeParen matchgroup=coqVernacPunctuation start="(" end=")" keepend
syn region coqBinder            contained contains=coqIdent,coqBinderTypeCurly matchgroup=coqVernacPunctuation start="`\?{" end="}" keepend
syn region coqBinderTypeParen   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end=")"
syn region coqBinderTypeCurly   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end="}"

" Declarations
syn region coqDecl       contains=coqIdent,coqDeclTerm,coqBinder matchgroup=coqVernacCmd start="\<\%(Axioms\?\|Conjectures\?\|Hypothes[ie]s\|Parameters\?\|Variables\?\|Context\)\>" matchgroup=coqVernacCmd end="\.\_s" keepend
syn region coqDeclTerm   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end=")"
syn region coqDeclTerm   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end="\.\_s"

" Theorems
syn region coqThm       contains=coqThmName matchgroup=coqVernacCmd start="\<\%(Program\_s\+\)\?\%(Theorem\|Lemma\|Example\|Corollary\|Remark\|Fact\|Proposition\)\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s" keepend fold
syn region coqThmName   contained contains=coqThmTerm,coqBinder matchgroup=coqIdent start="[[:digit:]']\@!\k\k*" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s"
syn region coqThmTerm   contained contains=@coqTerm,coqProofBody matchgroup=coqVernacCmd start=":" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>"

syn region coqGoal      contains=coqGoalTerm start="\<Goal\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>" keepend
syn region coqGoalTerm  contained contains=@coqTerm,coqProofBody matchgroup=coqVernacCmd start="Goal" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>" keepend

" Ltac
syn region coqLtacDecl     contains=coqLtacProfile start="\<Ltac\>" end="\.\_s" keepend
syn region coqLtacProfile  contained contains=coqLtacIdent,coqVernacPunctuation,coqLtacContents start="Ltac" end="\.\_s"
syn region coqLtacIdent    contained matchgroup=coqVernacCmd start="Ltac" matchgroup=coqIdent end="[[:digit:]']\@!\k\k*"
syn region coqLtacContents contained contains=coqTactic,coqTacticKwd,coqTacticAdmit,coqLtac,coqProofPunctuation matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

syn keyword coqLtac contained do info progress repeat try tryif
syn keyword coqLtac contained abstract constr context end external eval fail first fresh fun gfail goal guard
syn keyword coqLtac contained idtac in let ltac lazymatch multimatch match numgoals of rec revgoals reverse solve swap
syn keyword coqLtac contained timeout transparent_abstract type type_term with
syn keyword coqLtac contained has_evar is_cofix is_const is_constructor is_evar is_ground is_ind is_proj is_var
syn keyword coqLtac contained finish_timing restart_timer time time_constr
syn match   coqLtac contained "|-\|=>\|||\|\[\|\]\|\<_\>\||"

" Ltac2
syn region coqLtac2Decl contains=coqLtac2Ident,coqVernacPunctuation,coqLtacContents start="\<Ltac2\%(\_sType\)\?\>" end="\.\_s" keepend
syn region coqLtac2Decl contains=coqLtac2Eval start="\<Ltac2\_sEval\>" end="\.\_s" keepend
syn region coqLtac2Decl contains=coqLtac2Notation,coqLtacContents start="\<Ltac2\_sNotation\>" end="\.\_s" keepend
syn region coqLtac2Decl contains=coqIdent matchgroup=coqVernacCmd start="\<Print\_sLtac2\>" end="\.\_s" keepend

syn region coqLtac2Ident contained matchgroup=coqVernacCmd start="\<Ltac2\%(\_sType\)\?\>" matchgroup=coqIdent end="[[:digit:]']\@!\k\k*"

syn region coqLtac2Eval  contained contains=coqTerm,coqTactic,coqTacticKwd,coqTacticAdmit,coqLtac,coqProofPunctuation matchgroup=coqVernacCmd start="\<Ltac2\_sEval\>" matchgroup=coqIdent end="\.\_s"
syn region coqLtac2Notation contained contains=coqProofPunctuation,coqString matchgroup=coqVernacCmd start="\<Ltac2\_sNotation\>" end="\.\_s"

" Proofs
" TODO: The \ze in the start match is a terrible hack so coqProofDelim will still
" be matched and the dot will be highlighted as coqProofDot. I assume there is a
" better way but I don't know what it is.
syn region coqProofBody  contains=coqProofPunctuation,coqTactic,coqTacticKwd,coqTacticAdmit,coqProofComment,coqProofKwd,coqProofEnder,coqProofDelim,coqLtac,coqString,coqAttribute matchgroup=coqProofDelim start="\<P\zeroof\>" start="\<\%(O\zebligation\_s\+\d\+\)\|\%(N\zeext\_s\+Obligation\)\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s" end="\<Save\>.*\.\_s" keepend
syn region coqProofDelim contained matchgroup=coqProofDelim start="\%(\<P\)\@1<=roof\>" matchgroup=coqProofDot end="\.\_s"
syn region coqProofDelim contained contains=coqOblOfDelim start="\%(\%(\<O\)\@1<=bligation\_s\+\d\+\)\|\%(\%(\<N\)\@1<=ext\_s\+Obligation\)\>" matchgroup=coqProofDot end="\.\_s" keepend
syn region coqProofEnder contained matchgroup=coqProofDelim start="\<\%(Qed\|Defined\)\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqProofEnder contained matchgroup=coqProofAdmit start="\<\%(Abort\|Admitted\)\>" matchgroup=coqVernacPunctuation end="\.\_s"
syn region coqProofEnder contained contains=coqIdent matchgroup=coqProofDelim start="\<Save\>" matchgroup=coqVernacPunctuation end="\.\_s"
" NOTE: Don't expect a proof body after `Fail Proof` or `Fail Next Obligation`.
" Must come after `coqProofBody`.
syn region coqProofFail  matchgroup=coqProofDelim start="\%(\<Fail\>\_s\+\)\@<=\%(Proof\|\%(Obligation\_s\+\d\+\)\|\%(Next\_s\+Obligation\)\)\>" end="\.\_s" keepend

syn keyword coqTactic    contained abstract absurd apply assert assert_fails assert_succeeds assumption auto autoapply
syn keyword coqTactic    contained autorewrite autounfold autounfold_one
syn keyword coqTactic    contained btauto
syn keyword coqTactic    contained case case_eq casetype cbn cbv change change_no_check classical_left classical_right
syn keyword coqTactic    contained clear clearbody cofix compare compute congr congruence constr_eq constr_eq_nounivs
syn keyword coqTactic    contained constr_eq_strict constructor contradict contradiction cut cutrewrite cycle
syn keyword coqTactic    contained decompose destruct dintuition discriminate discrR done dtauto
syn keyword coqTactic    contained eapply eassert eassumption easy eauto ecase econstructor eelim eenough eexact eexists
syn keyword coqTactic    contained einduction einjection eintros eleft elim elimtype enough eremember erewrite eright
syn keyword coqTactic    contained eset esimplify_eq esplit etransitivity evar exact exact_no_check exactly_once exfalso
syn keyword coqTactic    contained exists
syn keyword coqTactic    contained f_equal field field_lookup field_simplify field_simplify_eq finish_timing firstorder
syn keyword coqTactic    contained fix fold
syn keyword coqTactic    contained generalize gintuition
syn keyword coqTactic    contained have hnf
syn keyword coqTactic    contained idtac induction info_auto info_eauto info_trivial injection instantiate intro[s]
syn keyword coqTactic    contained intuition inversion inversion_clear inversion_sigma
syn keyword coqTactic    contained lapply lazy left lia lra lra_Q lra_R
syn keyword coqTactic    contained move
syn keyword coqTactic    contained native_cast_no_check native_compute nia now now_show nra nsatz nsatz_compute
syn keyword coqTactic    contained omega once optimize_heap over
syn keyword coqTactic    contained pattern protect_fv psatz psatz_Q psatz_R psatz_Z
syn keyword coqTactic    contained quote
syn keyword coqTactic    contained rapply red refine reflexivity remember rename replace rewrite rewrite_db
syn keyword coqTactic    contained rewrite_strat right ring ring_lookup ring_simplify rtauto
syn keyword coqTactic    contained set setoid_etransitivity setoid_reflexivity setoid_replace setoid_rewrite
syn keyword coqTactic    contained setoid_symmetry setoid_transitivity shelve shelve_unifiable simpl simplify_eq
syn keyword coqTactic    contained solve_constraints sos_Q sos_R sos_Z specialize split split_Rabs split_Rmult stepl
syn keyword coqTactic    contained stepr subst substitute suff suffices symmetry
syn keyword coqTactic    contained tauto transitivity trivial
syn keyword coqTactic    contained under unfold unify unlock unshelve
syn keyword coqTactic    contained vm_cast_no_check vm_compute
syn keyword coqTactic    contained with_strategy wlog
syn keyword coqTactic    contained xlia xnlia xnqa xnra
syn keyword coqTactic    contained zify zify_elim_let zify_iter_let zify_iter_specs zify_op zify_saturate
syn match   coqTactic    contained "\<debug\_s\+\%(auto\|eauto\|trivial\)\>"
syn match   coqTactic    contained "\<decide\_s\+equality\>"
syn match   coqTactic    contained "\<dependent\_s\+\%(destruction\|induction\|inversion\|inversion_clear\|rewrite\|simple\_s\+inversion\)\>"
syn match   coqTactic    contained "\<dfs\_s+eauto\>"
syn match   coqTactic    contained "\<e\?pose\%(\_s\+proof\)\?\>"
syn match   coqTactic    contained "\<functional\_s\+\%(induction\|inversion\)\>"
syn match   coqTactic    contained "\<generally\_s\+have\>"
syn match   coqTactic    contained "\<notypeclasses\_s\+refine\>"
syn match   coqTactic    contained "\<revert\%(\_s\+dependent\)\?\>"
syn match   coqTactic    contained "\<\%(reset\|show\)\_s\+ltac\_s\+profile\>"
syn match   coqTactic    contained "\<\%(start\|stop\)\_s\+ltac\_s\+profiling\>"
syn match   coqTactic    contained "\<simple\_s\+\%(apply\|congruence\|destruct\|eapply\|induction\|injection\|inversion\|\%(notypeclasses\_s\+refine\)\|refine\|subst\)\>"
syn match   coqTactic    contained "\<soft\_s\+functional\_s\+induction\>"
syn match   coqTactic    contained "\<typeclasses\_s\+eauto\>"
syn match   coqTactic    contained "\<without\_s\+loss\>"
syn keyword coqTacticKwd contained as by in using with into after until return
syn keyword coqTacticAdmit contained admit give_up

" The following is just to help other plugins to detect via syntax groups that we are inside a proof
syn keyword coqProofKwd         contained else end exists exists2 forall fun if in match let struct then where with as return
syn match   coqProofKwd         contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|="
syn match   coqProofPunctuation contained "(\|)\|:=\|:>\|:\|\.\|;\|,\|||\|\[\|\]\|@\|?"
syn region  coqProofComment     contained contains=coqProofComment,coqTodo start="(\*" end="\*)" extend keepend

" Definitions
syn region coqDef          contains=coqDefName matchgroup=coqVernacCmd start="\<\%(Program\_s\+\)\?\%(Definition\|Let\|Example\)\>" matchgroup=coqVernacPunctuation end=":="me=e-2 end="\.$"me=e-1 end="\.\_s"me=e-2 nextgroup=coqDefContents1,coqProofBody keepend skipnl skipwhite skipempty
syn region coqDefName       contained contains=coqBinder,coqDefType,coqDefContents1 matchgroup=coqIdent start="[[:digit:]']\@!\k\k*" matchgroup=NONE end="\.\_s" end=":="
syn region coqDefType       contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="\.\_s" end=":="
syn region coqDefContents1  contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":=" matchgroup=coqVernacPunctuation end="\.\_s"

" Coercions
syn region coqCoercion      contains=coqCoercionName,coqCoercionBody1,coqCoercionBody2 matchgroup=coqVernacCmd start="\<\%(Identity\_s\+\)\?Coercion\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqCoercionName  contained contains=coqBinder,coqDefType matchgroup=coqIdent start="[[:digit:]']\@!\k\k*" matchgroup=NONE end=":="me=e-2 end=">->"me=e-3 keepend
syn region coqCoercionBody1 contained contains=coqIdent matchgroup=coqVernacPunctuation start=">->" end="\.\_s"
syn region coqCoercionBody2 contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

" Fixpoints
syn region coqFix     contains=coqFixBody start="\<\%(Program\_s\+\)\?\%(\%(\%(Co\)\?Fixpoint\)\|Fixpoint\|Function\)\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqFixBody       contained contains=coqFixName matchgroup=coqVernacCmd start="\%(\%(\%(Co\)\?Fixpoint\)\|Function\)" start="\<with\>" matchgroup=NONE end="\.\_s"
syn region coqFixName       contained contains=coqBinder,coqFixAnnot,coqFixTerm,coqFixContent matchgroup=coqIdent start="[[:digit:]']\@!\k\k*" matchgroup=NONE end="\.\_s"
syn region coqFixAnnot      contained contains=@coqTerm matchgroup=coqVernacPunctuation start="{\_s*struct" end="}" keepend
syn region coqFixTerm       contained contains=@coqTerm,coqFixContent matchgroup=coqVernacPunctuation start=":" end="\.\_s"
syn region coqFixContent    contained contains=coqFixBody,@coqTerm,coqKwdMatch,coqFixNot matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqFixNot        contained contains=coqNotationString,coqFixNotTerm matchgroup=coqVernacCmd start="\<where\>" end="\.\_s"
syn region coqFixNotTerm    contained contains=@coqTerm,coqFixBody,coqFixNotScope matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqFixNotScope   contained contains=coqFixBody matchgroup=coqVernacPunctuation start=":" end="\.\_s"

" Inductives
syn region coqInd            contains=coqIndBody start="\<\%(Co\)\?Inductive\>\|\<Variant\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqIndBody     contained contains=coqIdent,coqIndTerm,coqBinder matchgroup=coqVernacCmd start="\%(\%(Co\)\?Inductive\)\|Variant" start="\<with\>" matchgroup=NONE end="\.\_s"
syn region coqIndTerm        contained contains=@coqTerm,coqIndContent matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="\.\_s"
syn region coqIndContent     contained contains=coqIndConstructor start=":=" end="\.\_s"
syn region coqIndConstructor contained contains=coqConstructor,coqBinder,coqIndConsTerm,coqIndNot,coqIndBody matchgroup=coqVernacPunctuation start=":=\%(\_s*|\)\?" start="|" matchgroup=NONE end="\.\_s"
syn region coqIndConsTerm    contained contains=coqIndBody,@coqTerm,coqIndConstructor,coqIndNot matchgroup=coqConstructor start=":" matchgroup=NONE end="\.\_s"
syn region coqIndNot         contained contains=coqNotationString,coqIndNotTerm matchgroup=coqVernacCmd start="\<where\>" end="\.\_s"
syn region coqIndNotTerm     contained contains=@coqTerm,coqIndNotScope,coqIndBody matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqIndNotScope    contained contains=coqIndBody matchgroup=coqVernacPunctuation start=":" end="\.\_s"
syn match  coqConstructor    contained "[[:digit:]']\@!\k\k*"

" Records
syn region coqRec        contains=coqRecProfile start="\<Record\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqRecProfile contained contains=coqIdent,coqRecTerm,coqBinder matchgroup=coqVernacCmd start="Record" matchgroup=NONE end="\.\_s"
syn region coqRecTerm    contained contains=@coqTerm,coqRecContent matchgroup=coqVernacPunctuation start=":"  end="\.\_s"
syn region coqRecContent contained contains=coqConstructor,coqRecStart matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqRecStart   contained contains=coqRecField,@coqTerm start="{" matchgroup=coqVernacPunctuation end="}" keepend
syn region coqRecField   contained contains=coqField matchgroup=coqVernacPunctuation start="{" end=":"
syn region coqRecField   contained contains=coqField matchgroup=coqVernacPunctuation start=";" end=":"
syn match coqField       contained "[[:digit:]']\@!\k\k*"

" Typeclasses
syn region coqCls        contains=coqClsProfile start="\<Class\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqClsProfile contained contains=coqIdent,coqRecTerm,coqBinder matchgroup=coqVernacCmd start="Class" matchgroup=NONE end="\.\_s"

syn region coqCls matchgroup=coqVernacCmd start="\<Existing\_s\+Class\>" contains=coqIdent end="\.\_s"

" Typeclass instances
syn region coqIns contains=coqDefName matchgroup=coqVernacCmd start="\<\%(\%(Program\|Declare\)\_s\+\)\?Instance\>" matchgroup=coqVernacPunctuation end=":="me=e-2 end="\.$"me=e-1 end="\.\_s"me=e-2 nextgroup=coqDefContents1,coqProofBody keepend skipnl skipwhite skipempty
syn region coqIns matchgroup=coqVernacCmd start="\<Existing\_s\+Instances\?\>" matchgroup=coqVernacPunctuation end="\.$"me=e-1 end="\.\s"me=e-2

" Canonical structures
syn region coqCanon contains=coqIdent matchgroup=coqVernacCmd start="\<Canonical\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend

" Equations
syn region coqEqn           contains=coqEqnProfile start="\<Equations?\?\>" matchgroup=coqVernacPunctuation end="\.\_s" keepend
syn region coqEqnProfile    contained contains=coqIdent,coqEqnTerm,coqBinder,coqEqnOptions matchgroup=coqVernacCmd start="Equations?\?" matchgroup=NONE end="\.\_s"
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
syn region coqExtrInductive matchgroup=coqVernacCmd start="\<Extract\_s\+Inductive\>" contains=coqIdent,coqBigArrow,coqString,coqTermPunctuation end="\.\_s"
" TODO: ^ Enforce order of tokens: ident => "string"
syn match coqBigArrow contained "=>"

" Elpi

" User-defined commands
syn region coqElpi matchgroup=coqVernacCmd start="\<Elpi\>" end="\.\_s" keepend

syn region coqElpiCommand matchgroup=coqVernacCmd start="\<Elpi\_s\+Command\>" end="\.\_s" keepend
syn region coqElpiTypecheck matchgroup=coqVernacCmd start="\<Elpi\_s\+Typecheck\>" end="\.\_s" keepend
syn region coqElpiDebug matchgroup=coqVernacCmd start="\<Elpi\_s\+\%(Debug\|Trace\|Bound\_s\+Steps\)\>" end="\.\_s" keepend
syn region coqElpiAccumulate contains=elpiEmbed matchgroup=coqVernacCmd start="\<Elpi\_s\+\%(Accumulate\|Program\)\>" end="\.\_s" keepend
syn region coqElpiQuery contains=elpiEmbed matchgroup=coqVernacCmd start="\<Elpi\_s\+Query\>" end="\.\_s" keepend
syn region coqElpiDb matchgroup=coqVernacCmd start="\<Elpi\_s\+Db\>" contains=elpiEmbed end="\.\_s" keepend
syn region coqElpiAccumulateDb matchgroup=coqVernacCmd start="\<Elpi\_s\+Accumulate\_s\+Db\>" end="\.\_s" keepend

syn cluster elpiCode contains=elpiName,elpiQuote,elpiMetavar,elpiComment,elpiString,elpiKeyword,elpiSymbol,elpiMode,elpiNumber
syn keyword elpiKeyword contained pred type kind pi sigma is
syn match elpiSymbol contained ":-\|=>\|->\|[,|.=!\\(){}\[\]]"
syn region elpiEmbed contained contains=@elpiCode matchgroup=elpiPunctuation start="\<lp:{{"rs=e end="}}" extend
syn region elpiQuote contained contains=@elpiCode matchgroup=elpiPunctuation start="{{" end="}}" extend
syn match elpiName contained "[a-z_][a-zA-Z0-9_.!?<>-]*"
syn match elpiMetavar contained "[A-Z][a-zA-Z0-0_!?<>-]*"
syn region elpiComment contained start="%" end="$" extend
syn region elpiString contained start=+"+ skip=+\\"+ end=+"+ extend
syn match elpiMode contained "\<[io]:"
syn match elpiNumber contained "[0-9]\+"

" Various (High priority)
syn region  coqComment           containedin=ALL contains=coqComment,coqTodo,@Spell start="(\*" end="\*)" extend keepend
syn keyword coqTodo              contained TODO FIXME XXX NOTE
syn region  coqString            start=+"+ skip=+""+ end=+"+ extend

" Synchronization
syn sync minlines=50
syn sync maxlines=500

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
HiLink coqTacticAdmit       coqProofAdmit
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
HiLink coqHint              coqVernacular
HiLink coqFeedback          coqVernacular
HiLink coqTopLevel          coqVernacular
HiLink coqRegisterKwd       coqVernacular

" DEFINED OBJECTS
HiLink coqIdent             Identifier
HiLink coqNotationString    coqIdent

" CONSTRUCTORS AND FIELDS
HiLink coqConstructor       Keyword
HiLink coqField             coqConstructor

" NOTATION SPECIFIC ("at level", "format", etc)
HiLink coqNotationKwd       Special
HiLink coqEqnOptions        coqNotationKwd

" ATTRIBUTES
HiLink coqAttribute         coqVernacular
HiLink coqAttrBool          Boolean
HiLink coqAttrPunc          coqAttribute

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

" Elpi
HiLink elpiKeyword          Keyword
HiLink elpiMetavar          Identifier
HiLink elpiComment          Comment
HiLink elpiString           String
HiLink elpiSymbol           Operator
HiLink elpiMode             Special
HiLink elpiNumber           Number
HiLink elpiPunctuation      Type

delcommand HiLink

let b:current_syntax = 'coq'
