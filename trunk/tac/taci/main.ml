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
    let module XmlInterp = Interpreter.Make (Output.XmlOutput) (Nologic.Nologic) in
    let module Int = Interface.Make (XmlInterp) in
    (Int.interpret ())
  else
    let module OutputInterp = Interpreter.Make (Output.ConsoleOutput) (Nologic.Nologic) in
    let module Int = Interface.Make (OutputInterp) in
    (Int.interpret ())

(*  Execute main  *)
let _ = main ()
