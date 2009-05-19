(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
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
exception Error of string

(**********************************************************************
*translate:
* Given an LP AST, returns a string containing the definitions 
* corresponding the LP module.
**********************************************************************)
let translate ast =
  let argument i = "a" ^ (string_of_int i) in  
  let translatePatterns ps body =
    let fvs = 
      Listutils.unique
        ((List.concat (List.map Lpabsyn.getTermFVS ps)) @
        Lpabsyn.getTermFVS body)
    in
    let rec translate i ps =
      match ps with
        [] -> Lpabsyn.string_of_term body
      | pattern::ps ->
          let p = Lpabsyn.string_of_term pattern in
          (argument i) ^ " = " ^ p ^ ", " ^ (translate (i + 1) ps)
    in
    if List.length fvs > 0 then
      let bindings = (String.concat "\\" fvs) ^ "\\" in
      "(sigma " ^ bindings ^ " " ^ (translate 0 ps) ^ ")"
    else
      "(" ^ (translate 0 ps) ^ ")"
  in
  
  let translateClause cl =
    let head = Lpabsyn.getClauseHead cl in
    let patterns = Lpabsyn.getApplicationArguments head in
    let matcher = translatePatterns patterns in
    let body = Lpabsyn.getClauseBody cl in
    if Option.isSome body then
      matcher (Option.get body)
    else
      matcher (Lpabsyn.AtomicTerm("true"))
  in
  
  let translateConstant c =
    let def head body = head ^ " :=\n" ^ body in
    let head name args = name ^ " " ^ args in
    let name = Lpabsyn.getConstantName c in
    let arity = Lpabsyn.getConstantArity c in
    let args arity = String.concat " " (Listutils.mapn argument arity) in
    let body = 
      let clauses = Lpabsyn.getConstantClauses c in
      "  " ^ (String.concat ";\n  " (List.map translateClause clauses))
    in
    def (head name (args arity)) body

  in
  List.map translateConstant ast

(**********************************************************************
*parse:
* Parse a string into an AST.
**********************************************************************)
let parse stream =
  try
   (Lpparser.lp_module
     Lplexer.token stream)
  with
    | Lpabsyn.Error(s) ->
        raise (Error(s))
    | Parsing.Parse_error ->
        raise (Error("syntax error"))

let parseString s =
  parse (Lexing.from_string s)

let parseFile filename =
  try
    parse (Lexing.from_channel (open_in filename))
  with
    Sys_error s -> raise (Error ("unable to open '" ^ filename ^ "'"))
    
let parseChannel c =
  parse (Lexing.from_channel c)
  
(**********************************************************************
*translateString/translateFile:
* Converts an LP module to a string containing a corresponding definition.
**********************************************************************)
let translateString s =
  translate (parseString s)

let translateFile f =
  translate (parseFile f)

let translateChannel c =
  translate (parseChannel c)
