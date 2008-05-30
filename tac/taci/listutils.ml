(********************************************************************
*empty:
* Check if a list is empty.
********************************************************************)
let empty = function
    [] -> true
  | _::_ -> false

let rec split3 l = match l with
    [] -> ([], [], [])
  | (h1,h2,h3)::tl ->
      let (t1,t2,t3) = split3 tl in
      (h1::t1, h2::t2, h3::t3)

let rec combine3 l1 l2 l3 =
  match l1,l2,l3 with
    [],[],[] -> []
  | (h1::t1, h2::t2, h3::t3) -> (h1,h2,h3)::(combine3 t1 t2 t3)
  | _ -> failwith "Listutils.split3: invalid arguments"

let mapi f =
  let rec aux n = if n = 0 then [] else f n :: aux (n-1) in
    aux
