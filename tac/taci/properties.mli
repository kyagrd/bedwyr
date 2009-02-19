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
* Properties:
***********************************************************************
* This module provides a uniform to access global properties.  An
* example of a property is 'output.debug', a boolean indicating
* whether to show debugging output.  Properties can be set from the 
* any of the interfaces using '#set "property.name" "value"'.
*
* Handles ints, strings, and booleans; if you want to use some other
* type it must be convertible to string.
**********************************************************************)
exception PropertyNotFound of string
exception InvalidPropertyFormat of string

val getBool : string -> bool
val getInt : string -> int
val getString : string -> string
val getValue : string -> (string -> 'a) -> 'a

val getDefault : (string -> 'a) -> string -> 'a -> 'a

val setString : string -> string -> unit
val setInt : string -> int -> unit
val setBool: string -> bool -> unit
val setValue : string -> 'a -> ('a -> string) -> unit

(*  In order to allow undoing/redoing of property settings.  Use
    'state' to get the current properties state, and then use 'update'
    to return to a previously stored state. *)
type properties
val state : unit -> properties
val update : properties -> unit
