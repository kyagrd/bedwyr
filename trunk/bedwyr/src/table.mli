type tag = Proved | Working of bool ref | Disproved | Unset
type t
    
val create : unit -> t

val add : allow_eigenvar:bool -> t -> Term.term list -> tag ref -> unit

val find : t -> Term.term list -> tag ref option

val print : Term.term -> t -> unit

val fprint : out_channel -> Term.term -> t -> unit

val reset : t -> unit

val iter_fun : t -> (Term.term -> tag -> unit) -> unit

val nabla_abstract : Term.term -> Term.term
