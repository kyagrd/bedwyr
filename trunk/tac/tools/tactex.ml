(**********************************************************************
*TacTex:
* This program converts the xml proof output from taci to a tex file.
**********************************************************************)

(**********************************************************************
*getInputChannel/getOutputChannel:
* Open input/output file, exit if there's a failure.  If the output
* file isn't specified, use the input file with a .tex extension.
**********************************************************************)
let inputName = ref ""
let outputName = ref ""

let getInputChannel () =
  if !inputName = "" then
    (print_endline ("Error: no input file specified.");
    exit (-1))
  else
    try
      open_in !inputName
    with _ ->
      (print_endline ("Error: unable to open file '" ^ !inputName ^ "'");
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
      (print_endline ("Error: unable to open file '" ^ name ^ "'");
      exit (-1))

(**********************************************************************
*header/footer: latex to setup the document.
**********************************************************************)
let header =
"% This file was generated by tactex, part of the Tac system.
\\documentclass[10pt]{article}
\\usepackage{proof}
\\pdfpagewidth 100in
\\pdfpageheight 50in
\\begin{document}
"

let footer =
"\\end{document}
"

(*  fail: incredible error handling! *)
let fail expected x = failwith ("Not a '" ^ expected ^ "':\n" ^ Xml.to_string x)

(**********************************************************************
*
**********************************************************************)
type formula = string
type rule = {
  name : string ;
  level : int ;
  lhs : formula list ;
  rhs : formula list ;
  active : formula ;
  bound : string ;
  sub : rule list
}

(**********************************************************************
*convertFormula:
* Converts a formula to LaTex; total hackery.
**********************************************************************)
let formulaRegexes =
    [(Str.regexp "\\", ".");
    (Str.regexp "# ", "");
    (Str.regexp "+", "");
    (Str.regexp "-", "");
    (Str.regexp "\\*", "");
    (Str.regexp " ", "~");
    (Str.regexp "=>", "\\rightarrow");
    (Str.regexp ", ", " \\wedge ");
    (Str.regexp "; ", " \\vee ");
    (Str.regexp "pi", "\\forall");
    (Str.regexp "sigma", "\\exists")
    ]
let convertFormula s =
  List.fold_left
    (fun s (regex, replace) -> Str.global_replace regex replace s)
    s
    formulaRegexes

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
* Convert an xml node containing a formula to a string of latex.
**********************************************************************)
let parseFormula = function
    Xml.Element ("formula",_,[Xml.PCData formula]) ->
      convertFormula formula
  | x -> fail "formula" x

(*  parseSide: convert a list of formulas.  *)
let parseSide side = List.map parseFormula side

(**********************************************************************
*parseRule:
*
**********************************************************************)
let rec parseRule = function
    Xml.Element ("rule",[],
      [ Xml.Element ("name",[],[Xml.PCData name]) ;
        Xml.Element ("sequent",[],[
          Xml.Element ("level",[],[Xml.PCData level]);
          Xml.Element ("lhs",[],lhs);
          Xml.Element ("rhs",[],rhs)
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
          sub = parseRules sub}
  | x -> fail "rule" x

and parseRules rules = List.map parseRule rules

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
*   help: print usage information.
**********************************************************************)
and speclist = [("-h", Arg.Unit(printHelp), "");
                ("--help", Arg.Unit(printHelp), "");
                ("--input", Arg.Set_string(inputName), "input");
                ("--output", Arg.Set_string(outputName), "output")]
and usage = "Usage: tactex --input \"input file\"\n\nOptions:"
let parseArgs output =
    (Arg.parse speclist (fun s -> ()) usage)
    
(**********************************************************************
*convert:
* 
**********************************************************************)
let convert p =
  let processSide forms = String.concat ", " forms in
  let rec processProof p =
    "\\infer[" ^ (convertRuleName p.name) ^ "]{" ^
      (processSide p.lhs) ^ " \\vdash " ^ (processSide p.rhs) ^  "}{\n" ^
      (processProofs p.sub) ^ "}"
  
  and processProofs ps =
    String.concat " & " (List.map processProof ps)
  in
  let s = processProof p in
  header ^ "\\[\n" ^ s ^ "\n\\]\n" ^ footer

let main () =
  (*  Parse the command line arguments. *)
  let () = parseArgs () in
  let input = getInputChannel () in
  let xml = Xml.parse_in input in
  let () = close_in input in
  let proof = parseRule xml in  (*  Assumption: there's just a single rule. *)
  let s = convert proof in
  let output = getOutputChannel () in
  (output_string output s;
  close_out output;
  exit 0)
  

(*  Entrypoint  *)
let () = main ()
