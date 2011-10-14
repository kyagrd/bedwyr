type simple_kind =
  | KRArrow of simple_kind' * simple_kind'
  | Ki      of string
and simple_kind' = simple_kind

type simple_type =
  | TRArrow of simple_type' * simple_type'
  | Ty      of string
and simple_type' = simple_type


module NS = Map.Make(struct type t = string let compare = compare end)

let type_symbols = ref NS.empty


let atom name =
  try
    NS.find name !type_symbols
  with
    | Not_found ->
        assert (name <> "");
        let t = ref (Ty name) in
        type_symbols := NS.add name t !type_symbols ;
        t
