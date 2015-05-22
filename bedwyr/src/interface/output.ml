(****************************************************************************)
(* Bedwyr -- prover output                                                  *)
(* Copyright (C) 2015 Quentin Heath                                         *)
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

let eprintf ?p ?(formatter=Format.err_formatter) f =
  begin match p with
    | None ->
        Format.fprintf formatter
          ("@[<hov>@;<0 1>@[" ^^ f ^^ "@]@]@.")
    | Some p ->
        Format.fprintf formatter
          ("@[<hov>%a@;<1 1>@[" ^^ f ^^ "@]@]@.")
          Preterm.Pos.pp p
  end

let wprintf ?p ?(formatter=Format.err_formatter) f =
  begin match p with
    | None ->
        Format.fprintf formatter
          ("@[<hov>Warning: @;<1 1>@[" ^^ f ^^ "@]@]@.")
    | Some p ->
        Format.fprintf formatter
          ("@[<hov>Warning: %a@;<1 1>@[" ^^ f ^^ "@]@]@.")
          Preterm.Pos.pp p
  end
