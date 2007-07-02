(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007 Zach Snow, David Baelde                          *
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

let debug () =
  (print_endline "Debugging enabled.";
  Output.showDebug := true;
  Pprint.debug := true)

let outputName = ref "console"
let logicName = ref "none"
let printLogicInformation = ref false
let printOutputInformation = ref false



(**********************************************************************
*parseArgs:
**********************************************************************)
let rec printHelp () = (Arg.usage speclist usage; exit 0)
and speclist = [("--debug", Arg.Unit(debug), "enable debugging");
                ("-help", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "print usage information");
                ("--logic", Arg.Set_string(logicName), "logic");
                ("--logics", Arg.Set(printLogicInformation), "list logics");
                ("--output", Arg.Set_string(outputName), "output");
                ("--outputs", Arg.Set(printOutputInformation), "list outputs")]
and usage = "Usage: taci --logic \"logic name\"\n\nOptions:"

let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)

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
    if !outputName = "" then
      (print_endline ("Error: no output specified.");
      1)
    else
    
    if not (Logics.outputExists !outputName) then
      (print_endline ("Error: undefined output '" ^ !outputName ^ "'.");
      1)
    else
    
    if !logicName = "" then
      (print_endline ("Error: no logic specified.");
      1)
    else
    
    if not (Logics.logicExists !logicName) then
      (print_endline ("Error: undefined logic '" ^ !logicName ^ "'.");
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
