(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006 Nadathur, Linnell, Baelde, Ziegler                    *)
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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

open Term
open Format

exception Found of int

(* List of infix operators sorted by priority. *)
let infix : string list ref = ref []
let set_infix l = infix := l
let is_infix x = List.mem x !infix
let priority x =
  try
    ignore (List.fold_left
              (fun i e -> if e = x then raise (Found i) else i+1)
              1 !infix) ;
    0
  with
    | Found i -> i

let rec flatten_infix c = function
  | [] -> []
  | x::q ->
      begin match observe x with
        | App (t,rs) ->
            begin match Term.observe t with 
              | Var {name=d;tag=Constant} when c = d ->
                  (flatten_infix c rs)@(flatten_infix c q)
              | _ -> x::(flatten_infix c q)
            end
        | _ -> x::flatten_infix c q
      end

let rec flatten t = let t = Norm.hnorm t in match observe t with
  | Var _ | DB _ -> t
  | App (x,ts) ->
      assert (ts <> []) ;
      begin match observe x with
        | App(h,ts1) -> flatten (app h (ts1@ts))
        | Var {name=op;tag=Constant} when is_infix op ->
            if ts = [] then x 
            else app x (flatten_infix op ts)
        | _ -> app (flatten x) (List.map flatten ts)
      end
  | Lam (n,t) -> lambda n (flatten t)
  | Susp _ -> flatten (Norm.hnorm t)
  | Ptr _ -> assert false (* deref *)

exception Not_printable_term

(* Generic output function *)

let tag2str = function
  | Constant -> "c"
  | Eigen -> "e"
  | Logic -> "l"

let pp_term out t =
  let pre = getAbsName () in
  let rec output p n out t = match observe t with
    | Var {name=s;tag=t;ts=ts} -> fprintf out "%s" s
    | DB i -> fprintf out "%s%d" pre (n-i+1)
    | App (r,l) ->
        begin match observe r with
          | Var {name=op;tag=Constant} when is_infix op ->
              let op_p = priority op in
              let op = " "^op^" " in
                if op_p > p && p <> 0 then
                  fprintf out "%a" (out_ls op op_p n) l
                else
                  fprintf out "(%a)" (out_ls op op_p n) l
          | _ -> fprintf out "(%a)" (out_ls " " 0 n) (r::l)
        end
    | Lam (0,t) -> assert false
    | Lam (i,t) ->
        (* This is a bit too much parenthesis sometimes *)
        fprintf out "(%a%a)"
          (let rec arg n out i =
             if i>0 then begin
               fprintf out "%s%d\\" pre (n+1) ; arg (n+1) out (i-1)
             end
           in
             arg n) i
          (output 0 (n+i)) t
    | Ptr t -> assert false (* observe *)
    | Susp _ -> output p n out (Norm.hnorm t)
  and out_ls s p n out = function
    | [] -> ()
    | [t] -> output p n out t
    | t::q -> fprintf out "%a%s%a" (output p n) t s (out_ls s p n) q
  in
    output 0 0 out (flatten t)

(* Output to stdout *)
let print_term t = printf "%a" pp_term t

(* Output to string *)
let term_to_string t =
  pp_term str_formatter t ;
  flush_str_formatter ()
