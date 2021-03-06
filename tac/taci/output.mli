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
* Output
***********************************************************************
* This module provides the Output signature that output modules must
* match, as well as two default output modules, ConsoleOutput and
* XmlOutput.  Several functors in taci are paramaterized by the Output
* signature (see interface.mli, interpreter.mli, logic.mli) so that
* output may be formatted in different ways based on the way taci is
* being used.
**********************************************************************)
module type Output =
sig
  (*  beginComputation/endComputation: used to indicate the beginning
      and end of possibly long computations, so that the user interface
      (in particular StickyTaci) can indicate the state of taci.  *)
  val beginComputation : unit -> unit
  val endComputation : unit -> unit
  
  val prompt : string -> unit
  
  val impossible : string -> unit
  val error : string -> unit
  val warning : string -> unit
  val debug : string -> unit
  
  val output : string -> unit
  val goal : string -> unit
  val clear : unit -> unit
  
  val logics : (string * string) list -> unit
  val tacticals : string list -> unit
end

(**********************************************************************
* ConsoleOutput
***********************************************************************
* The ConsoleOutput module a default output module that is intended to
* handle output when taci is being used from the command line.
**********************************************************************)
module ConsoleOutput : Output

(**********************************************************************
* XmlOutput
***********************************************************************
* The XmlOutput module is intended to handle output when taci is being
* used in conjunction with StickyTaci.  It annotates output using XML
* so that it is easy to parse with an external tool.  Note: if you
* modify the format of the XML, you will probably need to update
* StickyTaci to reflect the change.
**********************************************************************)
module XmlOutput : Output
