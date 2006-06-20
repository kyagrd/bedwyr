type tag = Proven | Working of bool ref | Disproven | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag

let find table args = Index.find !table args

let print head table =
  Printf.printf "Table for %s contains (P=Proven, D=Disproven):\n" head ;
  let d = Term.const head 0 in
  Index.iter !table
    (fun t tag ->
       let t = Term.app t [d] in
       match !tag with
         | Proven    -> Format.printf " [P] %a\n" Pprint.pp_term t
         | Disproven -> Format.printf " [D] %a\n" Pprint.pp_term t
         | _     -> () (* Garbage can happen in case of user interrupt *))

let reset x = x := Index.empty
