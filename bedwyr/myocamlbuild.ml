(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2012-2014 Quentin Heath                                    *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

open Ocamlbuild_plugin ;;

let _ =
  dispatch begin function
    | After_rules ->
        flag ["ocaml" ; "compile"] (A "-annot") ;
        flag ["ocaml" ; "compile"] (S [A "-warn-error" ; A "A-3-28"]) ;
        flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
        flag ["ocaml" ; "doc"] (S [A "-stars" ; A "-m" ; A "A"]) ;

        ocaml_lib "src/ndcore/ndcore" ;
        ocaml_lib "src/batyping/batyping" ;
        ocaml_lib "src/interface/interface" ;
        ocaml_lib "src/prover/prover" ;

        ()
    | _ -> ()
  end
