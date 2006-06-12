type 'a t

exception Cannot_table

val empty  : 'a t
val find   : 'a t -> Term.term list -> 'a option
val add    : 'a t -> Term.term list -> 'a -> 'a t
val remove : 'a t -> Term.term list -> 'a t
