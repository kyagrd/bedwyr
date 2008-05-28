(**********************************************************************
* Listutils
***********************************************************************
* Simple functions operating on lists... I actually thought there would
* be more of them!
**********************************************************************)
val empty : 'a list -> bool
val split3 : ('a * 'b * 'c) list -> ('a list * 'b list * 'c list)
val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list