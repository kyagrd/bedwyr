type tag = Proven | Working
type t = (Term.term list, tag) Hashtbl.t
    
let create () = Hashtbl.create 100

let add table args tag = Hashtbl.replace table args tag
  
let find table args = try Some (Hashtbl.find table args) with Not_found -> None

let remove table args = Hashtbl.remove table args

let print table =
  Hashtbl.iter
    (fun args tag -> Printf.printf "%s\n"
      (String.concat " " (List.map Pprint.term_to_string args)))
    table
