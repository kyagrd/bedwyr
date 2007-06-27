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
module type Interface =
sig
  val interpret : (string * string) list -> unit
end
module Make (I : Interpreter.Interpreter) =
struct
  let interpret logics =
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
    let () = I.setLogics logics in
    let session = I.onStart () in
    (interp session)
end
