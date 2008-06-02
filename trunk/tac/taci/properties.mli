val getBool : string -> bool
val getInt : string -> int
val getString : string -> string
val getValue : string -> (string -> 'a) -> 'a

val setString : string -> string -> unit
val setInt : string -> int -> unit
val setBool: string -> bool -> unit
val setValue : string -> 'a -> ('a -> string) -> unit
