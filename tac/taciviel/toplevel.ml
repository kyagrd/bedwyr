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
*position:
* Returns the position of the buffer.
**********************************************************************)
let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  if file = "" then
    "" (* lexbuf information is rarely accurate at the toplevel *)
  else
    Format.sprintf "%s(%d) : " file line

(**********************************************************************
*parseCommand:
* Parse a command from the given lex buffer.
**********************************************************************)
let parseCommand lexbuf s =
  try
    (Toplevelparser.toplevel_command Toplevellexer.command lexbuf)
  with
    Parsing.Parse_error ->
      raise (Absyn.SyntaxError ((position lexbuf) ^ "Syntax error" ^ s))

(**********************************************************************
*parseCommandList:
* Parses a command list from the given lexbuffer.
**********************************************************************)
let parseCommandList lexbuf s =
  try
    (Toplevelparser.toplevel_file Toplevellexer.command lexbuf)
  with
    Parsing.Parse_error ->
      raise (Absyn.SyntaxError ((position lexbuf) ^ "Syntax error" ^ s))

(**********************************************************************
*parseStringCommand:
* Parses a command from a string.
**********************************************************************)
let parseStringCommand s =
  let lexbuf = Lexing.from_string s in
  (parseCommand lexbuf (" in: " ^ s))

(**********************************************************************
*parseFile:
* Parses a command from a file.
**********************************************************************)
let parseFile s =
  let c = open_in s in
  let lexbuf = Lexing.from_channel c in
  (parseCommand lexbuf "")

(**********************************************************************
*parseStdinCommand:
* Parse a command from stdin.
**********************************************************************)
let parseStdinCommand () =
  let l = Lexing.from_channel stdin in
  (parseCommand l "")

(**********************************************************************
*parseStdinCommandList:
* Parse a command list from stdin.
**********************************************************************)
let parseStdinCommandList () =
  let l = Lexing.from_channel stdin in
  (parseCommandList l "")

(**********************************************************************
*parseChannelCommandList:
* Parse a command list from an in_channel.
**********************************************************************)
let parseChannelCommandList channel =
  let l = Lexing.from_channel channel in
  (parseCommandList l "")
