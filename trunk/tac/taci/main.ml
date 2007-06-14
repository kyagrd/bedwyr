let outputName = ref ""
let logicName = ref ""
let debug = ref false
let printLogicInformation = ref false
let printOutputInformation = ref false



(**********************************************************************
*parseArgs:
**********************************************************************)
let rec printHelp () = (Arg.usage speclist usage; exit 0)
and speclist = [("--debug", Arg.Set(debug), "enable debugging");
                ("-help", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "print usage information");
                ("--logic", Arg.Set_string(logicName), "logic");
                ("--logics", Arg.Set(printLogicInformation), "list logics");
                ("--output", Arg.Set_string(outputName), "output");
                ("--outputs", Arg.Set(printOutputInformation), "list outputs")]
and usage = "Usage: taci --logic \"logic name\"\n\nOptions:"

let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)

let interpret interp =
  (interp ();
  0)

(**********************************************************************
*main:
**********************************************************************)
let main () =
  (*  Parse the command line arguments. *)
  let _ = parseArgs () in
  
  if !printLogicInformation || !printOutputInformation then
    (if !printLogicInformation then
      Logics.printLogics (print_string)
    else
      ();
    if !printOutputInformation then
      Logics.printOutputs (print_string)
    else
      ();
    0)
  else  
    if not (Logics.outputExists !outputName) then
      (print_endline "Error: undefined output.";
      1)
    else
    
    if not (Logics.logicExists !logicName) then
      (print_endline "Error: undefined logic.";
      1)
    else
    
    let interp = Logics.getLogicInterpreter (!outputName) (!logicName) in
    if (Option.isSome interp) then
      (interpret (Option.get interp))
    else
      (print_endline "Error: unable to load logic.";
      1)

(*  Execute main  *)
let _ = main ()
