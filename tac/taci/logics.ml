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
let tables = Logics_gen.tables

let logics =
  let getInfo (key, (name,_)) = (key, name) in
  let (_,table) = (List.hd tables) in
  List.map getInfo table

let logicExists key =
  (List.mem_assoc key logics)

let outputExists key =
  (List.mem_assoc key tables)

let rec getLogicInterpreter outputname logicname =
  try
    let table = List.assoc outputname tables in
    let (_,interpreter) = (List.assoc logicname table) in
    Some interpreter
  with
    Not_found -> None

and printLogics output =
  let get (key, (name, _)) =
    key ^ (String.make (20 - (String.length key)) ' ') ^ ":  " ^ name
  in
  let (_, table) = List.hd tables in
  output ("Logics:\n\t" ^ (String.concat "\n\t" (List.map get table)) ^ "\n")

and printOutputs output =
  let get (key, _) =
    key
  in
  output ("Outputs:\n\t" ^ (String.concat "\n\t" (List.map get tables)) ^ "\n")
