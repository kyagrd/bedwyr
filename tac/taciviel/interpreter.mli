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
* Interpreter
***********************************************************************
* This functor builds an interpreter that uses the given output for
* writing and the given logic for reasoning.
**********************************************************************)
module type Interpreter =
sig
  type session
  exception Exit of session
  exception Logic of string * session
  
  val setLogics : (string * string) list -> unit
  val onStart : unit -> session
  val onEnd : session -> unit
  val onPrompt : session -> session
  val onInput : session -> session 
end
module Make : functor (O : Output.Output) -> functor (L : Logic.Logic) -> Interpreter
