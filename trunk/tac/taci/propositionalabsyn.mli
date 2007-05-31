exception SyntaxError of string

type tactic = (string * string)
type term =
    AndTerm of (term * term)
  | OrTerm of (term * term)
  | ImplicationTerm of (term * term)
  | NotTerm of term
  | ConstantTerm of string
  | TrueTerm
  | FalseTerm

val string_of_term : term -> string