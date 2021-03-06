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
exception SyntaxError of string

type pretactical =
    ApplicationPreTactical of string * pretactical list
  | StringPreTactical of string

type 'a tactical =
    Tactical of 'a
  | String of string

type command =
    Exit
  | Reset
  | Open of string list
  | Include of string list
  | Help
  | Clear
  | Undo of int
  | Redo of int
  | ProofOutput of string

  | Lemma of string * string
  | Lemmas
  | Theorem of string * string
  | Definitions of string list

  | Tacticals
  | TacticalDefinition of string * pretactical

  | PreTactical of pretactical
  | Timing of bool
  | Debug of bool

  | Logic of string  
  | Logics

  | Set of string * string
  | Get of string
  
  | LogicDefined of string * string list

let rec string_of_pretactical tac =
  match tac with
      ApplicationPreTactical(name, []) ->
        name
    | ApplicationPreTactical(name, args) ->
        Printf.sprintf "%s(%s)"
          name
          (String.concat ", " (List.map string_of_pretactical args))
    | StringPreTactical(s) -> "\"" ^ s ^ "\""
