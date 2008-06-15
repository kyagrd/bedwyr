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
type properties = (string * string) list
let properties = ref []

let getString s =
  try
    (List.assoc s !properties)
  with
    Not_found -> failwith ("Properties.get: '" ^ s ^ "' not found")

let getBool s = bool_of_string (getString s)
let getInt s = int_of_string (getString s)
let getValue s f = f (getString s)

let setString s v =
  properties := (s, v) :: (!properties)
    
let setInt s v = setString s (string_of_int v)
let setBool s v = setString s (string_of_bool v)
let setValue s v f = setString s (f v)

let state () = !properties
let update p = properties := p
