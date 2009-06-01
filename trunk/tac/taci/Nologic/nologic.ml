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
*NoLogic:
* A dummy logic module.
**********************************************************************)
module Nologic (O : Output.Output) =
struct
  let name = "No Logic"
  let info =
"
No Logic v0.0

No logic does nothing!
"

  let start = info
  type session = unit
  
  let incl files session =
    (print_endline (String.concat ", " files))

  let tacticals _ = Logic.Table.empty
  let defineTactical _ _ _ = ()

  let reset () = ()
  
  let lemma name s session =
    (print_endline ("No Logic can't prove lemma '" ^ name ^ "': " ^ s ^ ".");
    session)

  let theorem name s session =
    (print_endline ("No Logic can't prove '" ^ name ^ "': " ^ s ^ ".");
    session)

  let logicDefined id args session =
    (O.error ("unknown directive: " ^ id ^ ".\n");
    session)

  let lemmas session = session
  let proved session = session
  let definitions ds session = session
  let operator name fix prec session = session

  type sequent = unit
  let theoremName session = ""

  let validSequent session = true
  let sequent session = Some((), ())
  let sequents session = []
  let string_of_sequents session = "()"
  let update sequents builder session = ()
  let undo session = session
  let redo session = session
  
  type proof = unit
  let proof _ = fun l -> l
  let string_of_proofs session = "proofs: ()"
end
