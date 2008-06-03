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

exception Logic of string
exception BatchFailure
exception BatchSuccess

module type Interface =
sig
  val interpret : (string * string) list -> unit
end
module Make (I : Interpreter.Interpreter) =
struct
  (********************************************************************
  *interpret:
  * The main interface function, when invoked interpret first sets the
  * logic list of the given interpreter (necessary to avoid cyclic module
  * dependencies) and then creates a new session by calling the given
  * interpreter's onStart function (see interpreter.mli).  It loops,
  * calling onPrompt and then onInput in turn and always "threading"
  * the session through.  The loop ends only when either the Exit or Logic
  * exceptions are raised.  If Exit is raised the logic is terminated and
  * unit is returned.  If Logic is raised the logic is terminated and then
  * another exception is raised so that the main driver loop (see main.ml)
  * can load a new interface and interpreter.
  ********************************************************************)
  let interpret logics =
    let batch session =
      try
        let session' = (I.onBatch session) in
        (I.onEnd session')
      with
          I.Exit(session) -> ((I.onEnd session); raise BatchSuccess)
        | I.BatchFailure -> (raise BatchFailure)
    in
    
    let rec interp session =
      try
        let session' = I.onPrompt session in
        let session'' = I.onInput session' in
        (interp session'')   
      with
        I.Exit(session) ->
          (I.onEnd session)
      | I.Logic(s, session) ->
          (I.onEnd session;
          raise (Logic s))
    in
    (*  Hackery so that the logic knows the names of all logics.  *)
    let () = I.setLogics logics in
    let session = I.onStart () in
    
    if Properties.getBool "output.batch" then
      batch session
    else
      interp session
end
