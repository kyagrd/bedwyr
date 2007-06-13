exception SyntaxError of string
exception SemanticError of string

type term = Term.term

type formula =
    AndFormula of (formula * formula)
  | OrFormula of (formula * formula)
  | ImplicationFormula of (formula * formula)
  | EqualityFormula of (term * term)
  | PiFormula of formula
  | SigmaFormula of formula
  | NablaFormula of formula
  | MuFormula of string * formula
  | AbstractionFormula of string * formula
  | MuApplicationFormula of formula * term list
  | AtomicApplicationFormula of string * term list
  | DBFormula of int
  | AnonymousFormula

type predefinition =
  PreDefinition of (string * string list * formula)

type definition =
  Definition of (string * int * formula)

type unifyresult =
    UnifyFailed
  | UnifySucceeded
  | UnifyError of string
  
val mapFormula : (formula -> formula) -> (term -> term) -> formula -> formula
val abstract : term -> formula -> formula
val apply : term list -> formula -> formula
val applyMu : formula -> formula -> formula
val string_of_formula : formula -> string
val string_of_term : term -> string

val rightUnify : term -> term -> unifyresult
val leftUnify : term -> term -> unifyresult
val unifyList : (term -> term -> unifyresult) -> term list -> term list -> unifyresult
val containsAnonymous : formula -> bool
val matchFormula : formula -> formula -> bool


val getTermHead : term -> string option
val getTermHeadAndArgs : term -> (string * term list) option

val getDefinitionArity : definition -> int
val getDefinitionBody : definition -> formula