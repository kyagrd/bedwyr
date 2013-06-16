" Vim syntax file for Bedwyr
" Language:     Bedwyr
" Filenames:    *.def
" Maintainers:  Quentin Heath  <forename.surname@inria.fr>
"               David Baelde   <firstname.name@ens-lyon.org>
" URL:
" https://gforge.inria.fr/scm/viewvc.php/*checkout*/trunk/bedwyr/contrib/vim/syntax/bedwyr.vim?root=slimmer
" Last Change:  2013 May 17 - Add shbang

if version < 600
  set iskeyword+=33,35-36,38-39,42-43,45,58,60-64,94,95,96,124,126
  syntax clear
else
  setlocal iskeyword+=33,35-36,38-39,42-43,45,47,58,60-64,92,94,95,96,124,126
  " TODO vérifier ce que sont 37, 44 et 46
".96 .39 .36  .63 .33 .64 .35 .38 .95
".43 .45 .60 .62 .61 .126 .124 .58 .42 .94
  if exists("b:current_syntax")
    finish
  endif
endif

" Bedwyr is case sensitive.
syn case match

syn match       bedwyrFreeId    contained "\u[A-Za-z0-9`'$?!@#&_]*"
syn match       bedwyrDeclId    contained "[a-z`'$][A-Za-z0-9`'$?!@#&_]*"
syn match       bedwyrInternId  contained "_\([A-Za-z0-9`'$?!@#&_]\)\+"
"syn match       bedwyrInfixId   contained "\([+-<>=~|:]\|\*\|\^\)\+"
syn match       bedwyrInfixId   contained "\([+]\|-\|<\|>\|=\|\~\||\|:\|\*\|\^\)\+"

syn keyword     bedwyrCommentErr \*/
syn match       bedwyrMetaCommendErr "#[a-z_]*"
syn match       bedwyrPointErr  "\."
syn match       bedwyrDefineErr "\<Define\>"
syn match       bedwyrByErr     "\<by\>"
syn match       bedwyrThmErr    "\<Theorem\>"
syn match       bedwyrQedErr    "\<Qed\>"
syn match       bedwyrSemiColonErr ";"
syn match       bedwyrDefEqErr  "\<:=\>"
"syn keyword     bedwyrFormulaErr true false forall exists nabla \\ = /\\ \\/
syn match       bedwyrFormulaErr "\(\<\(true\|false\|forall\|exists\|nabla\)\>\)\|\\\|=\|/\\\|\\/"
syn match       bedwyrParenErr  "(\|)"
syn keyword     bedwyrImpErr    =>

syn cluster     bedwyrCommonErrs contains=bedwyrCommentErr,bedwyrMetaCommendErr,bedwyrPointErr,bedwyrDefineErr,bedwyrByErr,bedwyrThmErr,bedwyrQedErr,bedwyrSemiColonErr,bedwyrDefEqErr,bedwyrFormulaErr,bedwyrImpErr

syn match       bedwyrComment   "%.*" contains=bedwyrTodo extend
syn match       bedwyrComment   "#!.*" extend
syn region      bedwyrComment   start="/\*" end="\*/" contains=bedwyrComment,bedwyrTodo extend

syn keyword     bedwyrTodo      contained TODO XXX

syn region      bedwyrNone      matchgroup=bedwyrMetaCommand start="#[a-z_]*\>" matchgroup=bedwyrSymbol end="\." contains=@bedwyrCommonErrs,bedwyrParenErr,bedwyrComment,@bedwyrFormulae

syn region      bedwyrNone      matchgroup=bedwyrKeyword start="\<\(Kind\|Type\)\>" matchgroup=bedwyrSymbol end="\." contains=@bedwyrCommonErrs,bedwyrParenErr,bedwyrComment,bedwyrComma,@bedwyrTypes

syn region      bedwyrDefBlock  matchgroup=bedwyrKeyword start="\<Define\>" matchgroup=bedwyrSymbol end="\." contains=bedwyrPredDeclarations keepend
syn region      bedwyrPredDeclarations start="." matchgroup=bedwyrKeyword end="\<by\>" contained nextgroup=bedwyrPredDefinitions skipempty contains=@bedwyrCommonErrs,bedwyrParenErr,bedwyrComment,bedwyrFlavour,bedwyrComma,@bedwyrAnnotatedId
syn region      bedwyrPredDefinitions start="." matchgroup=bedwyrSymbol end="\." contained contains=@bedwyrCommonErrs,bedwyrParenErr,bedwyrComment,bedwyrDefEq,bedwyrSemiColon,@bedwyrFormulae

syn region      bedwyrLemma     matchgroup=bedwyrKeyword start="\<Theorem\>" matchgroup=bedwyrSymbol end="\." contains=bedwyrTheorem
syn region      bedwyrTheorem   start="." matchgroup=bedwyrSymbol end="\." contained nextgroup=bedwyrProof contains=bedwyrPredDefinitions keepend
syn region      bedwyrProof     start="." matchgroup=bedwyrKeyword end="Qed" contained

syn keyword     bedwyrFlavour   contained inductive coinductive
syn match       bedwyrComma     contained ","
syn keyword     bedwyrDefEq     :=
syn match       bedwyrSemiColon contained ";"
syn keyword     bedwyrColon     :

syn cluster     bedwyrFormulae  contains=bedwyrQString,bedwyrNat,bedwyrFreeId,bedwyrBoolean,bedwyrQuantifier,bedwyrBinder,bedwyrConnective,@bedwyrAnnotatedId,bedwyrFormulaeEncl
syn cluster     bedwyrAnnotatedId contains=bedwyrColon,@bedwyrTypes
syn cluster     bedwyrTypes     contains=bedwyrType,bedwyrFreeId,bedwyrDeclId,bedwyrInternId,bedwyrUnderscore,bedwyrInfixId,bedwyrTypesEncl

syn region      bedwyrTypesEncl contained transparent matchgroup=bedwyrKeyword start="(" matchgroup=bedwyrKeyword end=")" contains=@bedwyrCommonErrs,bedwyrComment,@bedwyrTypes
syn region      bedwyrFormulaeEncl contained transparent matchgroup=bedwyrKeyword start="(" matchgroup=bedwyrKeyword end=")" contains=@bedwyrCommonErrs,bedwyrComment,@bedwyrFormulae

syn keyword     bedwyrType      contained type prop string nat
syn region      bedwyrQString   contained start=+"+ skip=+\\\\\|\\"\|[^"]+ end=+"+ extend
syn match       bedwyrNat       contained "\<\d\+\>"
syn keyword     bedwyrBoolean   contained true false
syn keyword     bedwyrQuantifier contained forall exists nabla
syn match       bedwyrBinder    contained "\\\|,"
syn keyword     bedwyrConnective contained = /\\ \\/ ->
syn keyword     bedwyrUnderscore _


" Synchronization
syn sync minlines=50
syn sync maxlines=500

"syn sync match bedwyrCommentSync grouphere  bedwyrComment "/\*"
"syn sync match bedwyrCommentSync groupthere bedwyrComment "\*/"

syn sync match bedwyrDefSync    grouphere bedwyrPredDeclarations "\<Define\>"
syn sync match bedwyrDefSync    grouphere bedwyrPredDefinitions "\<by\>\|;"


if version >= 508 || !exists("did_bedwyr_syntax_inits")
  if version < 508
    let did_bedwyr_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink        bedwyrCommentErr Error
  HiLink        bedwyrMetaCommendErr Error
  HiLink        bedwyrPointErr  Error
  HiLink        bedwyrDefineErr Error
  HiLink        bedwyrByErr     Error
  HiLink        bedwyrThmErr    Error
  HiLink        bedwyrQedErr    Error
  HiLink        bedwyrSemiColonErr Error
  HiLink        bedwyrDefEqErr  Error
  HiLink        bedwyrFormulaErr Error
  HiLink        bedwyrParenErr  Error
  HiLink        bedwyrImpErr    Error

  HiLink        bedwyrComment   Comment
  HiLink        bedwyrProof     bedwyrComment

  HiLink        bedwyrTodo      Todo

  HiLink        bedwyrMetaCommand Preproc

  HiLink        bedwyrKeyword   Keyword
  HiLink        bedwyrFlavour   bedwyrKeyword

  HiLink        bedwyrSymbol    Delimiter
  HiLink        bedwyrComma     bedwyrSymbol
  HiLink        bedwyrDefEq     bedwyrSymbol
  HiLink        bedwyrSemiColon bedwyrSymbol
  HiLink        bedwyrColon     bedwyrSymbol

  HiLink        bedwyrType      Type
  HiLink        bedwyrQString   String
  HiLink        bedwyrNat       Number
  HiLink        bedwyrFreeId    Identifier
  HiLink        bedwyrDeclId    Normal
  HiLink        bedwyrInternId  Constant
  HiLink        bedwyrInfixId   SpecialChar
  HiLink        bedwyrBoolean   Boolean
  HiLink        bedwyrQuantifier Function
  HiLink        bedwyrBinder    Operator
  HiLink        bedwyrConnective Operator
  HiLink        bedwyrUnderscore bedwyrFreeId

  delcommand HiLink
endif
