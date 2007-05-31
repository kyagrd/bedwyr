let xmlOutput = ref false
let logicName = ref ""
    
(**********************************************************************
*parseArgs:
**********************************************************************)
let parseArgs =
  fun () ->
    let speclist = [("--xml", Arg.Set(xmlOutput), "output xml");
                    ("--logic", Arg.Set_string(logicName), "logic")] in
    (Arg.parse speclist (fun s -> ()) "Usage: taci --logic \"logic name\"")

(**********************************************************************
*main:
**********************************************************************)
let main () =
  (*  Parse the command line arguments. *)
  let _ = parseArgs () in
  
  if !xmlOutput then
    let module Interp = Interpreter.Make (Output.XmlOutput) (Propositional.Propositional (Output.XmlOutput)) in
    let module Int = Interface.Make (Interp) in
    (Int.interpret ())
  else
    let module Interp = Interpreter.Make (Output.ConsoleOutput) (Propositional.Propositional (Output.ConsoleOutput)) in
    let module Int = Interface.Make (Interp) in
    (Int.interpret ())

  
(*  Execute main  *)
let _ = main ()
