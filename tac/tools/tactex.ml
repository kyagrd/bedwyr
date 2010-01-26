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

(**********************************************************************
*tactex:
* This program converts the xml proof output from taci to a tex file.
* It also can perform 'outlining' to make the proof a bit more legible.
**********************************************************************)

(**********************************************************************
*getInputChannel/getOutputChannel:
* Open input/output file, exit if there's a failure.  If the output
* file isn't specified, use the input file with a .tex extension.
**********************************************************************)
let inputName = ref ""
let outputName = ref ""
let outline = ref false

(**********************************************************************
* Versioning Information:
**********************************************************************)
let version = "0.9.2"
let printVersion () =
  (print_endline ("Tactex version " ^ version ^ ".");
  exit 0)

let getInputChannel () =
  if !inputName = "" then
    (print_endline ("Error : no input file specified.");
    exit (-1))
  else
    try
      open_in !inputName
    with _ ->
      (print_endline ("Error : unable to open file '" ^ !inputName ^ "'");
      exit (-1))

let getOutputChannel () =
  let name =
    if !outputName = "" then
      try
        (Filename.chop_extension !inputName) ^ ".tex"
      with
        Invalid_argument _ -> !inputName ^ ".tex"
    else
      !outputName
  in
    try
      open_out name
    with _ ->
      (print_endline ("Error : unable to open file '" ^ name ^ "'");
      exit (-1))

(**********************************************************************
*header/footer:
* LaTeX to setup the document.  This is probably bad TeX, but I don't
* really know TeX...
**********************************************************************)
let header =
"% This file was generated by tactex, part of the Tac system.
\\documentclass[10pt]{article}
\\usepackage{proof}
\\usepackage{color}
\\pdfpagewidth 200in
\\pdfpageheight 100in
\\begin{document}
\\thispagestyle{empty}
"

let footer =
"\\end{document}
"

(*  fail: incredible error handling! *)
let fail expected x =
  prerr_endline ("Error : XML node is not a '" ^ expected ^ "': " ^ Xml.to_string x) ;
  exit (-1)

(**********************************************************************
*formula:
**********************************************************************)
type formula = string
type rule = {
  name : string ;
  level : int ;
  lhs : formula list ;
  rhs : formula list ;
  active : formula ;
  bound : string ;
  focused : bool ;
  sub : rule list
}

(**********************************************************************
*convertFormula:
* Converts a formula to LaTeX; total hackery.  In particular, uses
* regexes to convert some of the logical connectives and whatnot into
* 'pretty' symbols.  Also keeps hard spaces using '~'.
**********************************************************************)
let formulaRegexes =
    [(Str.regexp "\\", ".");
    (Str.regexp "#", "");
    (Str.regexp "+", "");
    (Str.regexp "-", "");
    (Str.regexp "\\*", "");
    (Str.regexp "_", "\\_");
    (Str.regexp " ", "~");
    (Str.regexp "=>", "\\rightarrow{}");
    (Str.regexp ",", " \\wedge{}");
    (Str.regexp ";", " \\vee{}");
    (Str.regexp "pi", "\\forall{}");
    (Str.regexp "sigma", "\\exists{}");
    (Str.regexp "\\([a-zA-Z]\\)\\([0-9]+\\)", "\\1_{\\2}");
    (Str.regexp "gamma", "\\gamma{}");
    (Str.regexp "Gamma", "\\Gamma{}")
    ]
let convertFormula s =
  List.fold_left
    (fun s (regex, replace) -> Str.global_replace regex replace s)
    s
    formulaRegexes

(**********************************************************************
*convertName:
* Converts a rule name; all it does is make sure that rule names ending
* with underscore followed by more than one character get treated
* correctly; total special case hackery.
**********************************************************************)
let nameRegexes =
  [(Str.regexp "_mu", "_{mu}");
  (Str.regexp "_nu", "_{nu}")
  ]
let convertRuleName s =
  List.fold_left
    (fun s (regex, replace) -> Str.global_replace regex replace s)
    s
    nameRegexes

(**********************************************************************
*parseFormula:
* Convert an xml node containing a formula to a string of LaTeX.
**********************************************************************)
let parseFormula = function
    Xml.Element ("formula",_,[_; Xml.PCData formula]) ->
      convertFormula formula
  | x -> fail "formula" x

(*  parseSide: convert a list of formulas.  *)
let parseSide side = List.map parseFormula side

(**********************************************************************
*parseRule:
* Parses a rule; assumes that the XML will fit a particular format
* *exactly*, which is really dumb.  Proceeds to recursively parse
* subrules.
**********************************************************************)
let rec parseRule = function
    Xml.Element ("rule",[],
      [ Xml.Element ("name",[],[Xml.PCData name]) ;
        Xml.Element ("sequent",[],[
          Xml.Element ("level",[],[Xml.PCData level]);
          Xml.Element ("lhs",[],lhs);
          Xml.Element ("rhs",[],rhs);
          Xml.Element ("focused", [], [Xml.PCData focused])
        ]) ;
        formula ;
        Xml.Element ("bound",[],bound) ;
        Xml.Element ("sub",[],sub) ]) ->
          {name = name ;
          level = int_of_string level ;
          lhs = parseSide lhs ;
          rhs = parseSide rhs ;
          active = parseFormula formula ;
          bound = (match bound with [Xml.PCData s] -> s | _ -> "") ;
          focused = bool_of_string focused ;
          sub = parseRules sub}
  | x -> fail "rule" x

(*  parseRules: duh.  *)
and parseRules rules = List.map parseRule rules

(**********************************************************************
*outline:
* Changes the given proof so that strings of asynchronous rules are
* shown only as a single 'async' rule.
**********************************************************************)
let outlineProof p =
  (*  phaseSwitch: returns true if the given rule corresponds to an
      asynchronous to synchronous phase shift; this has to special
      case the 'interesting' asynchronous connectives.  *)
  let phaseSwitch p =
    p.focused || p.name = "induction" || p.name = "coinduction"
  in
  
  (*  getAsyncSubs: get all subformulas of an async phase, by digging
      down until a synchronous-phase formula is found. *)
  let rec getAsyncSubs p =
    if phaseSwitch p then
      [p]
    else
      List.concat (List.map getAsyncSubs p.sub)
  in
  
  let rec outline p =
    if not (phaseSwitch p) then
      let subformulas = List.concat (List.map getAsyncSubs p.sub) in
      let subformulas' = List.map outline subformulas in
      {p with name = "async"; sub = subformulas'}
    else
      {p with sub = (List.map outline p.sub)}
  in
  outline p

(**********************************************************************
*convert:
* Convert a proof to a string; straightforward recursion over rules.
* The way it determines whether to 'highlight' a formula is by doing
* a string comparison to the rule's active formula; this can result in
* false positives (if the formula occurs twice), but this seems to only
* happen when the rule is 'axiom', which almost could be called a
* 'feature'.  Note that this makes heavy use of the proof.sty 'infer'
* macro; when proofs are large it seems to break and give funky output.
**********************************************************************)
let convert p =
  let processSide current formulas =
    let hilight f =
      if f = current then
        " \\textcolor{blue}{ " ^ f ^ " } "
      else
        f
    in
    let formulas' = List.map hilight formulas in
    String.concat ", " formulas'
  in
  
  let rec processProof p =
    "\\infer[" ^ (convertRuleName p.name) ^ "]{" ^
      (processSide p.active p.lhs) ^ " \\vdash " ^ (processSide p.active p.rhs) ^  "}{\n" ^
      (processProofs p.sub) ^ "}"
  
  and processProofs ps =
    String.concat " & " (List.map processProof ps)
  in
  let s = processProof p in
  header ^ "\\[\n" ^ s ^ "\n\\]\n" ^ footer

(**********************************************************************
*printHelp:
* Simply prints the usage information based on the speclist.
**********************************************************************)
let rec printHelp () = (Arg.usage speclist usage; exit 0)

(**********************************************************************
parseArgs:
* Parse the command line arguments.
* The supported options are:
*   input: specifies the input file.
*   output: specifies the output file.
*   outline: whether to perform outlining or not.
*   help: print usage information.
**********************************************************************)
and speclist = [("-h", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "");
                ("--input", Arg.Set_string(inputName), "input file");
                ("--outline", Arg.Set(outline), "outline the proof");
                ("--output", Arg.Set_string(outputName), "output file");
                ("-v", Arg.Unit(printVersion), "print version information");
                ("--version", Arg.Unit(printVersion), "print version information")]
and usage = "Usage: tactex --input \"input file\"\n\nOptions:"
let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)

(**********************************************************************
*main:
**********************************************************************)
let main () =
  (*  Parse the command line arguments. *)
  let () = parseArgs () in
  
  (*  Read input. *)
  let input = getInputChannel () in
  let xml = Xml.parse_in input in
  let () = close_in input in
  
  (*  Proof transformations.  *)
  let proof = parseRule xml in  (*  Assumption: there's just a single rule. *)
  let proof' = if !outline then outlineProof proof else proof in (*  Outline if requested. *)
  
  (*  Write output and exit.  *)
  let s = convert proof' in
  let output = getOutputChannel () in
  (output_string output s;
  close_out output;
  exit 0)
  

(*  Entrypoint  *)
let () =
  try
    main ()
  with
    Xml.Error(s1,s2) -> Printf.printf "%s(%i) : Error : %s" !inputName (Xml.line s2) (Xml.error_msg s1) 

