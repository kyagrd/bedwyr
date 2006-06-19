type tag = Proven | Working of bool ref | Disproven | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag

let find table args = Index.find !table args

let print table =
  Index.iter !table
    (fun t tag ->
         Format.printf " %s: %a\n"
           (match !tag with
              | Proven    -> "Proven   "
              | Disproven -> "Disproven"
              | Unset     -> "Unset    "
              | Working b -> assert false)
           Pprint.pp_term t)
