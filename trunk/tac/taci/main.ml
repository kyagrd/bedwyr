let xmlOutput = ref false
let logicName = ref ""
let debug = ref false
    
(**********************************************************************
*parseArgs:
**********************************************************************)
let parseArgs =
  fun () ->
    let speclist = [("--xml", Arg.Set(xmlOutput), "output xml");
                    ("--logic", Arg.Set_string(logicName), "logic");
                    ("--debug", Arg.Set(debug), "enable debugging")] in
    (Arg.parse speclist (fun s -> ()) "Usage: taci --logic \"logic name\"")

let consoleTable =
  let module O = Output.ConsoleOutput in
  
  let module P = Propositional.Propositional (O) in
  let module PInterp = Interpreter.Make (O) (P) in
  let module PI = Interface.Make (PInterp) in
  
  let module N = Nologic.Nologic in
  let module NInterp = Interpreter.Make (O) (N) in
  let module NI = Interface.Make (NInterp) in
  
  let module FO = Firstorder.Firstorder (O) in
  let module FOInterp = Interpreter.Make (O) (FO) in
  let module FOI = Interface.Make (FOInterp) in
  
  [("propositional", PI.interpret);
  ("firstorder", FOI.interpret);
  ("none", NI.interpret)]

let xmlTable =
  let module O = Output.XmlOutput in
  
  let module P = Propositional.Propositional (O) in
  let module PInterp = Interpreter.Make (O) (P) in
  let module PI = Interface.Make (PInterp) in
  
  let module N = Nologic.Nologic in
  let module NInterp = Interpreter.Make (O) (N) in
  let module NI = Interface.Make (NInterp) in
  
  let module FO = Firstorder.Firstorder (O) in
  let module FOInterp = Interpreter.Make (O) (FO) in
  let module FOI = Interface.Make (FOInterp) in
  
  [("propositional", PI.interpret);
  ("firstorder", FOI.interpret);
  ("none", NI.interpret)]

(**********************************************************************
*main:
**********************************************************************)
let main () =
  (*  Parse the command line arguments. *)
  let _ = parseArgs () in
  
  if !xmlOutput then
    let () = Output.XmlOutput.showDebug := !debug in
    try
      (List.assoc !logicName xmlTable) ()
    with
      Not_found ->
        if !logicName = "" then
          Output.XmlOutput.error ("No logic specified.\n")
        else
          Output.XmlOutput.error ("Invalid logic name: " ^ !logicName ^ ".\n")
  else
    let () = Output.ConsoleOutput.showDebug := !debug in
    try
      (List.assoc !logicName consoleTable) ()
    with
      Not_found ->
        if !logicName = "" then
          Output.ConsoleOutput.error ("No logic specified.\n")
        else
          Output.ConsoleOutput.error ("Invalid logic name: " ^ !logicName ^ ".\n")

(*  Execute main  *)
let _ = main ()
