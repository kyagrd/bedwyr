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
*Accessor functions.
**********************************************************************)
let isSome = function
    Some _ -> true
  | None -> false
  
let isNone = function
    Some _ -> false
  | None -> true

let get = function
    Some value -> value
  | None -> failwith "Option.get: Invalid option"

(**********************************************************************
*string_of_option:
* Produces a printable string representation of the enclosed object
* by applying the given printer to it, if it exists, or by simply 
* returning "None" if the option is empty.
**********************************************************************)
let string_of_option v p =
  match v with
    Some a -> p a
  | None -> "None"
