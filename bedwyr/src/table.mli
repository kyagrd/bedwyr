type tag = Proven | Working
type t
    
val create : unit -> t

val add : t -> Term.term list -> tag -> unit

val find : t -> Term.term list -> tag option

val remove : t -> Term.term list -> unit


