let rec printHelp () = (Arg.usage speclist usage; exit 0)
and speclist = [("-help", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "print usage information");
                ("--input", Arg.Set_string(inFileName), "input file");
                ("--output", Arg.Set_string(outFileName), "output file")]

and usage = "Usage: taci --logic \"logic name\"\n\nOptions:"

let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)

let output logics outputs =
  let makeLogic output (Logic(logicname,logicmod)) =
    let arg n = "(" ^ n ^ ")" in
    let name = generate () in
    let interpname = name ^ "Interpreter" in
    let interfacename = name ^ "Interface" in
    
    let header =
      "  let module " ^ name ^ " = " ^ logicmod ^ (arg output) ^ " in\n" ^
      "  let module " ^ interpname ^ " = " ^ interpMake ^ (arg output) ^ (arg name) ^ " in\n" ^
      "  let module " ^ interfacename ^ " = " ^ interfaceMake ^ (arg interpname) ^ " in\n\n"
    in
    
    let table =
      "(\"" ^ logicname ^ "\", (" ^ name ^ ".name, " ^ interfacename ^ ".interpret))"
    in
    (header, table)

  let makeOutput logics output =
    (output, (List.map (makeLogic output) logics))
  in
  
  let outputOutput outline =
    
  let outtable = (List.map (outputOutput logics) outputs) in
  (List.map outputOutput outtable)
  
let main () =
  let _ = parseArgs () in
  
  let (logics, outputs) = parse fileName in
  (output logics outputs)

let _ = main ()