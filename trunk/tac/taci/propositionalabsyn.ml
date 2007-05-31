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

let rec string_of_term = function
  | AndTerm(lhs, rhs) -> "(" ^ (string_of_term lhs) ^ " /\\ " ^ (string_of_term rhs) ^ ")"
  | OrTerm(lhs, rhs) -> "(" ^ (string_of_term lhs) ^ " \\/ " ^ (string_of_term rhs) ^ ")"
  | ImplicationTerm(lhs, rhs) -> "(" ^ (string_of_term lhs) ^ " -> " ^ (string_of_term rhs) ^ ")"
  | NotTerm(t) -> "~" ^ (string_of_term t)
  | ConstantTerm(s) -> s
  | TrueTerm -> "true"
  | FalseTerm -> "false"
