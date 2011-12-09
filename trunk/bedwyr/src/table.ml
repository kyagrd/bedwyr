type tag = Proved | Working of bool ref | Disproved | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag

let find table args = Index.find !table args

(* Abstract nabla variables in a term. If equivariant tabling is used
   then use only nabla variables appearing in the term. Otherwise,
   add vacuous nabla's as neccessary. The maximum index of the nabla variables
   in the term determine the number of nabla's needed to be added (in case
   of non-equivariant tabling). For non-equivariant tabling, this use of maximum index will
   cause us to miss vacuous nablas that appear inner most in a proved atomic goal.
   For example, if a query like  (nabla x\ nabla y\ p x) succeeds, then
   the table will only display (nabla x\ p x), because the vacuous y is
   forgotten in the table.
   This behavior is strictly speaking unsound. For example, if p is defined as

   p X := sigma Y\ (X = Y -> false).

   That is, p X is true if there exists a term distinct from X.
   Assuming that the types are vacuous, then (nabla x\ p x)  is not provable
   in Linc, but (nabla x\ nabla y\ p x) is.
   Suppose the latter were proved by Bedwyr (currently it's impossible because we can't
   yet handle logic variables on the left), then the table will instead display
   (nabla x\ p x) as provable, which is wrong.

   This unsoundness may never arise in the goals tabled by Bedwyr, because
   to produce this behavior, it seems that we need unification of logic variables on
   the left, which is not handled in Bedwyr anyway. But it'd be good if this can
   be fixed, if we want to be faithful to the Linc logic.
*)

let nabla_abstract t =
  let t = Norm.deep_norm t in
  let l = Term.get_nablas t in
  let max = List.fold_left (fun a b -> if (a < b) then b else a) 0 l in
  let rec make_list = function 0 -> [] | n -> n::make_list (n-1) in
  let bindings = if !Index.eqvt_tbl then l else make_list max in
  Term.binder
    Term.Nabla
    (List.length bindings)
    (List.fold_left (fun s i -> (Term.abstract (Term.nabla i) s)) t bindings)


(* Printing a table to standard output. Nabla variables are abstracted and explicitly quantified. *)
let print head table =
  Format.printf
    "Table for %a contains (P=Proved, D=Disproved):@\n"
    Pprint.pp_term head ;
  Index.iter !table
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       match !tag with
         | Proved    -> Format.printf " [P] %a@\n" Pprint.pp_term t
         | Disproved -> Format.printf " [D] %a@\n" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false)

let iter_fun table f =
  Index.iter !table (fun t tag -> f t !tag)


(* Printing a table to a file. Nabla variables are abstracted and explicitly quantified. *)
let fprint fout head table =
  let fmt = (Format.formatter_of_out_channel fout) in
  Format.fprintf fmt
    "%% Table for %a contains :@\n"
    Pprint.pp_term head ;
   Index.iter !table
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       match !tag with
         | Proved    -> Format.fprintf fmt "proved %a.\n" Pprint.pp_term t
         | Disproved -> Format.fprintf fmt "disproved %a.\n" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false)

let reset x = x := Index.empty
