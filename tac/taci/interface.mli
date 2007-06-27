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
*Interface:
* This functor contructs a toplevel interface using the given
* interpreter.  The interface implements the toplevel loop, reading
* input and passing it to the interpreter for processing.
**********************************************************************)
exception Logic of string
module type Interface =
sig
  (********************************************************************
  *interpret:
  * This is the toplevel loop.  It returns only when the interpreter
  * exits.  It raises Logic s if the user asks to load a logic s.  The
  * assumption is that s exists.
  ********************************************************************)
  val interpret : (string * string) list -> unit
end
module Make : functor (I : Interpreter.Interpreter) -> Interface
