let xmlOutput = ref false
let logicName = ref ""
let debug = ref false
let printLogicInformation = ref false

let consoleTable =
  let module O = Output.ConsoleOutput in
  
  let module P = Propositional.Propositional (O) in
  let module PInterp = Interpreter.Make (O) (P) in
  let module PI = Interface.Make (PInterp) in
  
  let module N = Nologic.Nologic in
  let module NInterp = Interpreter.Make (O) (N) in
  let module NI = Interface.Make (NInterp) in
  
  let module FO = Firstorder.Firstordernonstrict (O) in
  let module FOInterp = Interpreter.Make (O) (FO) in
  let module FOI = Interface.Make (FOInterp) in
  
  let module FOS = Firstorder.Firstorderstrict (O) in
  let module FOSInterp = Interpreter.Make (O) (FO) in
  let module FOSI = Interface.Make (FOInterp) in
  
  [("firstorder", (FO.name, FOI.interpret));
  ("firstorder-strict", (FOS.name, FOSI.interpret));
  ("none", (N.name, NI.interpret));
  ("propositional", (P.name, PI.interpret))]


let xmlTable =
  let module O = Output.XmlOutput in
  
  let module P = Propositional.Propositional (O) in
  let module PInterp = Interpreter.Make (O) (P) in
  let module PI = Interface.Make (PInterp) in
  
  let module N = Nologic.Nologic in
  let module NInterp = Interpreter.Make (O) (N) in
  let module NI = Interface.Make (NInterp) in
  
  let module FO = Firstorder.Firstordernonstrict (O) in
  let module FOInterp = Interpreter.Make (O) (FO) in
  let module FOI = Interface.Make (FOInterp) in
  
  let module FOS = Firstorder.Firstorderstrict (O) in
  let module FOSInterp = Interpreter.Make (O) (FO) in
  let module FOSI = Interface.Make (FOInterp) in
  
  [("firstorder", (FO.name, FOI.interpret));
  ("firstorder-strict", (FOS.name, FOSI.interpret));
  ("none", (N.name, NI.interpret));
  ("propositional", (P.name, PI.interpret))]

let rec getLogicInterpreter error table name=
  try
    let (_,interpreter) = (List.assoc name table) in
    Some interpreter
  with
    Not_found ->
      if !logicName = "" then
        (error ("No logic specified.\n");
        printHelp ();
        None)
      else
        (error ("Invalid logic name: " ^ !logicName ^ ".\n");
        None)

and printLogics () =
  let get (key, (name, _)) =
    key ^ (String.make (20 - (String.length key)) ' ') ^ ":  " ^ name
  in
  if (!xmlOutput) then
    (Output.XmlOutput.output ("Logics:\n\t" ^ (String.concat "\n\t" (List.map get consoleTable)) ^ "\n");
    exit 0)
  else
    (Output.ConsoleOutput.output ("Logics:\n\t" ^ (String.concat "\n\t" (List.map get consoleTable)) ^ "\n");
    exit 0)

(**********************************************************************
*parseArgs:
**********************************************************************)
and printHelp () = (Arg.usage speclist usage; exit 0)
and speclist = [("--debug", Arg.Set(debug), "enable debugging");
                ("-help", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "print usage information");
                ("--logic", Arg.Set_string(logicName), "logic");
                ("--logics", Arg.Set(printLogicInformation), "list logics");
                ("--xml", Arg.Set(xmlOutput), "output xml")]
and usage = "Usage: taci --logic \"logic name\"\n\nOptions:"

let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)

(**********************************************************************
*main:
**********************************************************************)
let main () =
  (*  Parse the command line arguments. *)
  let _ = parseArgs () in
  
  if !printLogicInformation then
    printLogics ()
  else  
    if !xmlOutput then
      let () = Output.XmlOutput.showDebug := !debug in
      let i = getLogicInterpreter (Output.XmlOutput.error) xmlTable !logicName in
      if Option.isSome i then
        (Option.get i) ()
      else
        ()
    else
      let () = Output.ConsoleOutput.showDebug := !debug in
      let i = getLogicInterpreter (Output.ConsoleOutput.error) consoleTable !logicName in
      if Option.isSome i then
        (Option.get i) ()
      else
        ()

(*  Execute main  *)
let _ = main ()
