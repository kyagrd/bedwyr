exception SyntaxError of string
type term = Term.term
type formula =
    AndFormula of (formula * formula)
  | OrFormula of (formula * formula)
  | ImplicationFormula of (formula * formula)
  | EqualityFormula of (term * term)
  | PiFormula of formula
  | SigmaFormula of formula
  | NablaFormula of formula
  | AtomicFormula of term

val abstract : term -> formula -> formula
val apply : term list -> formula -> formula
val string_of_formula : formula -> string
