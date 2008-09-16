type tag = Proved | Working of bool ref | Disproved | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag

let find table args = Index.find !table args

let print head table =
  Format.printf
    "Table for %a contains (P=Proved, D=Disproved):\n"
    Pprint.pp_term head ;
  Index.iter !table
    (fun t tag ->
       let t = Term.app t [head] in
       match !tag with
         | Proved    -> Format.printf " [P] %a\n" Pprint.pp_term t
         | Disproved -> Format.printf " [D] %a\n" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false)

let reset x = x := Index.empty
