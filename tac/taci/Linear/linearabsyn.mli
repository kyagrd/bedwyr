exception SyntaxError of string
exception SemanticError of string

type term = Term.term

type formula =
    AndFormula of (formula * formula)
  | LinearAndFormula of (formula * formula)
  
  | OrFormula of (formula * formula)
  | LinearOrFormula of (formula * formula)
  
  | ImplicationFormula of (formula * formula)
  
  | EqualityFormula of (term * term)
  
  | PiFormula of formula
  | SigmaFormula of formula
  | NablaFormula of formula
  | MuFormula of string * formula
  | NuFormula of string * formula
  
  | AbstractionFormula of string * formula
  | ApplicationFormula of formula * term list
  
  | AtomicFormula of term
  | DBFormula of string * int
  
type fixpoint =
    Inductive
  | CoInductive

type predefinition =
  PreDefinition of (string * string list * formula * fixpoint)

type definition =
  Definition of (string * int * formula * fixpoint)

type unifyresult =
    UnifyFailed
  | UnifySucceeded
  | UnifyError of string
  
val mapFormula : (formula -> formula) -> (term -> term) -> formula -> formula
val abstract : string -> formula -> formula
val apply : term list -> formula -> formula
val renameAbstractions : formula -> formula
val applyFixpoint : (term list -> formula) -> formula -> formula
val string_of_definition : definition -> string
val string_of_formula : formula -> string
val string_of_formula_ast : formula -> string
val string_of_term : term -> string

val rightUnify : term -> term -> unifyresult
val leftUnify : term -> term -> unifyresult
val unifyList : (term -> term -> unifyresult) -> term list -> term list -> unifyresult
val matchFormula : formula -> formula -> bool


val getTermHead : term -> string option
val getTermHeadAndArgs : term -> (string * term list) option

val getDefinitionArity : definition -> int
val getDefinitionBody : definition -> formula