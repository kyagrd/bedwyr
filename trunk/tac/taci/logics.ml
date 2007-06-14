let tables = Logics_gen.tables

let logics =
  let getInfo (key, (name,_)) = (key, name) in
  let (_,table) = (List.hd tables) in
  List.map getInfo table

let logicExists key =
  (List.mem_assoc key logics)

let outputExists key =
  (List.mem_assoc key tables)

let rec getLogicInterpreter outputname logicname =
  try
    let table = List.assoc outputname tables in
    let (_,interpreter) = (List.assoc logicname table) in
    Some interpreter
  with
    Not_found -> None

and printLogics output =
  let get (key, (name, _)) =
    key ^ (String.make (20 - (String.length key)) ' ') ^ ":  " ^ name
  in
  let (_, table) = List.hd tables in
  output ("Logics:\n\t" ^ (String.concat "\n\t" (List.map get table)) ^ "\n")

and printOutputs output =
  let get (key, _) =
    key
  in
  output ("Outputs:\n\t" ^ (String.concat "\n\t" (List.map get tables)) ^ "\n")
