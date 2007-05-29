exception SyntaxError of string

type term =
    AndTerm of (term * term)
  | OrTerm of (term * term)
  | ImplicationTerm of (term * term)
  | NotTerm of term
  | ConstantTerm of string
  | TrueTerm
  | FalseTerm
