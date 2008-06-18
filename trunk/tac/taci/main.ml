(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde                     *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************)
(*  Global properties *)
let () = Properties.setString "taci.version" "0.9.0"
let () = Properties.setBool "taci.timing" false

let debug () =
  (print_endline "Debugging enabled.";
  Properties.setBool "output.debug" true;
  Pprint.debug := true) (*  Can't use a property because Pprint is part of ndcore.  *)

let () = Properties.setBool "output.batch" false
let batchMode s =
  Properties.setBool "output.batch" true;
  Properties.setString "output.batchfile" s

let outputName = ref "console"
let logicName = ref "none"
let printLogicInformation = ref false
let printOutputInformation = ref false


let printVersion () =
  (print_endline ("Taci version " ^ (Properties.getString "taci.version"));
  exit 0)

(**********************************************************************
*printHelp:
* Simply prints the usage information based on the speclist.
**********************************************************************)
let rec printHelp () = (Arg.usage speclist usage; exit 0)

(**********************************************************************
parseArgs:
* Parse the command line arguments, seting any necessary flags.
* The supported flags are:
*   debug: sets the global debug flag (see output.mli)
*   help: prints help/usage information
*   logic: specifies the logic to load
*   logics: lists all logics
*   output: specifies the output module to load
*   outputs: lists all output modules
**********************************************************************)
and speclist = [("-b", Arg.String(batchMode), "batch mode");
                ("--batch", Arg.String(batchMode), "batch mode");
                ("--debug", Arg.Unit(debug), "enable debugging");
                ("-help", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "print usage information");
                ("--logic", Arg.Set_string(logicName), "logic");
                ("--logics", Arg.Set(printLogicInformation), "list logics");
                ("--output", Arg.Set_string(outputName), "output");
                ("--outputs", Arg.Set(printOutputInformation), "list outputs");
                ("-v", Arg.Unit(printVersion), "print version information");
                ("--version", Arg.Unit(printVersion), "print version information")]
and usage = "Usage: taci --logic \"logic name\"\n\nOptions:"
let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)

(**********************************************************************
*interpret:
* Calls the interpreter with the list of logics.  If the interpreter
* returns it simply returns 0 (success).  If the logic raises an
* Interface.Logic exception (see interface.mli) it loads the specified
* logic and the recursively calls itself.  This allows the user to load
* a logic from the toplevel loop.
**********************************************************************)
let rec interpret interp =
  try
    (interp Logics.logics;
    0)
  with
    Interface.Logic (s) ->
      let interp = Logics.getLogicInterpreter (!outputName) (s) in
      if (Option.isSome interp) then
        (interpret (Option.get interp))
      else
        (print_endline "Error: unable to load logic.";
        1)
  | Interface.BatchFailure ->
      (print_endline "Error: batch file contains errors.";
      2)
  | Interface.BatchSuccess ->
      (print_endline "Batch file executed successfully.";
      0)

(**********************************************************************
*main:
* Main driver function.  Parses the arguments.  If the user wants a list
* of logics or outputs they are printed and 0 (success) is returned.
* If an undefined output module or logic is specified an error is
* raised.  Otherwise it loads the appropriate interpreter based on the
* logic and output name and calls the interpret function with the loaded
* interpreter.
**********************************************************************)
let main () =
  (*  Parse the command line arguments. *)
  let _ = parseArgs () in
  
  (*  List outputs and logics if requested. *)
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
    if !outputName = "" then
      (print_endline ("Error: no output specified.");
      1)
    else
    
    (*  Ensure the output module exists.  *)
    if not (Logics.outputExists !outputName) then
      (print_endline ("Error: undefined output '" ^ !outputName ^ "'.");
      1)
    else
    
    if !logicName = "" then
      (print_endline ("Error: no logic specified.");
      1)
    else
    
    (*  Ensure the logic module exists. *)
    if not (Logics.logicExists !logicName) then
      (print_endline ("Error: undefined logic '" ^ !logicName ^ "'.");
      1)
    else
    
    (*  Load the requested logic's interpreted and start it up. *)
    let interp = Logics.getLogicInterpreter (!outputName) (!logicName) in
    if (Option.isSome interp) then
      (interpret (Option.get interp))
    else
      (print_endline "Error: unable to load logic.";
      1)

(*  Execute main  *)
let _ = main ()
