type tag = Proven | Working of bool ref | Disproven | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag
  
let find table args = Index.find !table args

let print table = Format.printf "Not yet implemented for term-indexes.\n"
  (* Hashtbl.iter
    (fun args tag -> Printf.printf "%s: %s\n"
      (match tag with
        | Proven -> "Proven"
        | Disproven -> "Disproven"
        | Working b -> assert false (* No working goals at toplevel *))
      (String.concat " " (List.map Pprint.term_to_string args)))
    table *)
