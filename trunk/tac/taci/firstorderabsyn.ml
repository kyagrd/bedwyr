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

let rec string_of_formula f =
  match f with
      AndFormula(l,r) -> "(" ^ (string_of_formula l) ^ ", " ^ (string_of_formula r) ^ ")"
    | OrFormula(l,r) -> "(" ^ (string_of_formula l) ^ "; " ^ (string_of_formula r) ^ ")"
    | ImplicationFormula(l,r) -> "(" ^ (string_of_formula l) ^ " -> " ^ (string_of_formula r) ^ ")"
    | EqualityFormula(l,r) -> "(" ^ (Pprint.term_to_string l) ^ " = " ^ (Pprint.term_to_string r) ^ ")"
    | PiFormula(f) -> "pi " ^ (string_of_formula f)
    | SigmaFormula(f) -> "sigma " ^ (string_of_formula f)
    | NablaFormula(f) -> "nabla " ^ (string_of_formula f)
    | AtomicFormula(t) -> Pprint.term_to_string t

let rec abstract var formula =
  match formula with
      AndFormula(l,r) -> AndFormula(abstract var l, abstract var r)
    | OrFormula(l,r) -> OrFormula(abstract var l, abstract var r)
    | ImplicationFormula(l,r) -> ImplicationFormula(abstract var l, abstract var r)
    | EqualityFormula(l,r) -> EqualityFormula(Term.abstract_var var l, Term.abstract_var var r)
    | PiFormula(f) -> PiFormula(abstract var f)
    | SigmaFormula(f) -> SigmaFormula(abstract var f)
    | NablaFormula(f) -> NablaFormula(abstract var f)
    | AtomicFormula(t) -> AtomicFormula(Term.abstract_var var t)

let rec apply terms formula =
  match formula with
      AndFormula(l,r) -> AndFormula(apply terms l, apply terms r)
    | OrFormula(l,r) -> OrFormula(apply terms l, apply terms r)
    | ImplicationFormula(l,r) -> ImplicationFormula(apply terms l, apply terms r)
    | EqualityFormula(l,r) -> EqualityFormula(Term.app l terms, Term.app r terms)
    | PiFormula(f) -> PiFormula(apply terms f)
    | SigmaFormula(f) -> SigmaFormula(apply terms f)
    | NablaFormula(f) -> NablaFormula(apply terms f)
    | AtomicFormula(t) -> AtomicFormula(Term.app t terms)
