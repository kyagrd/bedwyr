let inFilename = ref ""
let outModuleName = ref ""

let rec printHelp () = (Arg.usage speclist usage; exit 0)
and speclist = [("-help", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "print usage information");
                ("--input", Arg.Set_string(inFilename), "input file");
                ("--output", Arg.Set_string(outModuleName), "output module")]

and usage = "Usage: logics_gen --input \"input filename\" --output \"output filename\" \n\nOptions:"

let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)

let currentId = ref 0
let generate () =
  let s = "Gen_" ^ (string_of_int (!currentId)) in
  let () = currentId := !currentId + 1 in
  s

(**********************************************************************
*parse:
* Parse an input file into a list of outputs and logics.
**********************************************************************)
let parse infile =
  let inchannel = open_in infile in
  let lexbuf = Lexing.from_channel inchannel in
  try
    let result = (Parser.toplevel_file Lexer.command lexbuf) in
    let (os,ls) = result in
    if (List.length os = 0) then
      (print_endline "Error: no outputs specified.";
      None)
    else if  (List.length ls = 0) then
      (print_endline "Error: no logics specified.";
      None)
    else
      Some result
  with
    Parsing.Parse_error -> (None)

(**********************************************************************
*outputModule:
* 
**********************************************************************)
let outputModule outputs logics =
  let interpMake = "Interpreter.Make" in
  let interfaceMake = "Interface.Make" in
  let outputName o = "O" ^ o in
  let makeLogic (Absyn.Output(oname, outputmod)) (Absyn.Logic(logicname,logicmod)) =
    let outputname = outputName oname in
    let arg n = "(" ^ n ^ ")" in
    let name = generate () in
    let interpname = name ^ "Interpreter" in
    let interfacename = name ^ "Interface" in
    
    let header =
      "  let module " ^ name ^ " = " ^ logicmod ^ (arg outputname) ^ " in\n" ^
      "  let module " ^ interpname ^ " = " ^ interpMake ^ (arg outputname) ^ (arg name) ^ " in\n" ^
      "  let module " ^ interfacename ^ " = " ^ interfaceMake ^ (arg interpname) ^ " in\n\n"
    in
    
    let table =
      "(\"" ^ logicname ^ "\", (" ^ name ^ ".name, " ^ interfacename ^ ".interpret))"
    in
    (header, table)
  in
  
  let makeOutput logics output =
    (output, (List.map (makeLogic output) logics))
  in
  
  let outputMLI=
    "val tables : (string * (string * (string * (unit->unit))) list) list\n"
  in
  
  let outputTableName name =
    name ^ "Table"
  in
  let outputMLHeader ((Absyn.Output(name,omod)), logics) =
    let outputLogicHeader (header,_) =
      header
    in
    
    let outputLogicTable (_,table) =
      table
    in
    
    let outputTable logics = 
      "  [" ^ (String.concat ";\n  " (List.map outputLogicTable logics)) ^ "]"
    in
    
    let outtable = outputTableName name in
    "let " ^ outtable ^ " =\n" ^
    "  let module " ^ (outputName name) ^ " = " ^ omod ^ " in\n\n" ^
    (String.concat "\n" (List.map outputLogicHeader logics)) ^ "\n" ^
    (outputTable logics) ^ "\n\n"
  in
  
  let outputMLTable outputs =
    let outputTable (Absyn.Output(name,_)) =
      "(\"" ^ name ^ "\", " ^ (outputTableName name) ^ ")"
    in
    "let tables = [" ^ (String.concat "; " (List.map outputTable outputs)) ^ "]\n"
  in
  
  let outtable = (List.map (makeOutput logics) outputs) in
  let mli = outputMLI in
  let ml = (String.concat "\n\n" (List.map outputMLHeader outtable)) ^ (outputMLTable outputs) in
  (mli,ml)
  
let main () =
  let _ = parseArgs () in
  
  if !inFilename = "" then
    (print_endline "Error: no input file specified.";
    1)
  else if !outModuleName = "" then
    (print_endline "Error: no output file specified.";
    1)
  else
    let result = parse !inFilename in
    match result with
      Some(outputs, logics) ->
        let (mli,ml) = (outputModule outputs logics) in
        let mlioutfile = open_out (!outModuleName ^ ".mli") in
        let () = output_string mlioutfile mli in
        let () = close_out mlioutfile in
        let mloutfile = open_out (!outModuleName ^ ".ml") in
        let () = output_string mloutfile ml in
        let () = close_out mloutfile in
        (print_endline "Done.";
        0)
    | None ->
        (print_endline "Error: unable to parse input.";
        1)

let _ = main ()