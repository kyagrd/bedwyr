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
* Logics
***********************************************************************
* This module is intended to act as an interface to the generated module
* Logics_gen (see logics_gen.mli).  It contains functions for determining
* whether a particular logic or output module has been registered with
* Taci, for printing information about the registered modules, a table
* of the registered logics, and a function to construct an interpreter
* function based on a logic name and output module name. 
**********************************************************************)
val logicExists : string -> bool
val outputExists : string -> bool

val logics : (string * string) list
val getLogicInterpreter : string -> string -> ((string * string) list -> unit) option

val printLogics : (string -> unit) -> unit
val printOutputs : (string -> unit) -> unit
