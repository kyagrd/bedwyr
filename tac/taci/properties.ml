let properties = ref []

let getString s =
  try
    !(List.assoc s !properties)
  with
    Not_found -> failwith ("Properties.get: '" ^ s ^ "' not found.")

let getBool s = bool_of_string (getString s)
let getInt s = int_of_string (getString s)
let getValue s f = f (getString s)

let setString s v =
  try
    (List.assoc s !properties) := v
  with
    Not_found -> properties := (s, ref v) :: (!properties)
    
let setInt s v = setString s (string_of_int v)
let setBool s v = setString s (string_of_bool v)
let setValue s v f = setString s (f v)
