type tag = Proven | Working of bool ref | Disproven | Unset
type t
    
val create : unit -> t

val add : t -> Term.term list -> tag ref -> unit

val find : t -> Term.term list -> tag ref option

val print : t -> unit
