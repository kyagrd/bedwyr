type tag = Proven | Working of bool ref | Disproven
type t = (Term.term list, tag) Hashtbl.t
    
let create () = Hashtbl.create 100

let add table args tag = Hashtbl.replace table args tag
  
let find table args = try Some (Hashtbl.find table args) with Not_found -> None

let remove table args = Hashtbl.remove table args

let print table =
  Hashtbl.iter
    (fun args tag -> Printf.printf "%s: %s\n"
      (match tag with
        | Proven -> "Proven"
        | Disproven -> "Disproven"
        | Working b -> assert false (* No working goals at toplevel *))
      (String.concat " " (List.map Pprint.term_to_string args)))
    table
