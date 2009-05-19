(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
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
exception Error of string

type constant = Constant of string * int * clause list
and clause = Clause of term * term option
and term =
    AtomicTerm of string
  | VariableTerm of string
  | ApplicationTerm of term * term list
  | ConjunctionTerm of term * term
  | DisjunctionTerm of term * term
  | ImplicationTerm of term * term
  | AbstractionTerm of string * term
  | PiTerm of term
  | SigmaTerm of term

let getConstantName (Constant(n,_,_)) = n
let getConstantArity (Constant(_,a,_)) = a
let getConstantClauses (Constant(_,_,cls)) = cls

let getClauseHead (Clause(head,_)) = head
let getClauseBody (Clause(_, body)) = body

let rec substitute term id term' =
  let s x = substitute x id term' in
  match term with
    | AtomicTerm _ -> term
    | VariableTerm v -> if v = id then term' else term
    | ApplicationTerm(l, r) -> ApplicationTerm(s l, List.map s r)
    | ConjunctionTerm(l, r) -> ConjunctionTerm(s l, s r)
    | DisjunctionTerm(l, r) -> DisjunctionTerm(s l, s r)
    | ImplicationTerm(l, r) -> ImplicationTerm(s l, s r)
    | AbstractionTerm(b, t) ->
        if b = id then term else AbstractionTerm(b, s t)
    | PiTerm(t) -> PiTerm(s t)
    | SigmaTerm(t) -> SigmaTerm(s t)
 
let rec string_of_term t =
  let s t = "(" ^ (string_of_term t) ^ ")" in
  let rec ss t =
    match t with
      VariableTerm id
    | AtomicTerm id -> id
    | ApplicationTerm(l, args) ->
        "(" ^ (ss l) ^ " " ^ (String.concat " " (List.map ss args)) ^ ")"
    | _ -> s t
  in
  match t with
    VariableTerm id
  | AtomicTerm id -> id
  | ApplicationTerm(l, args) ->
      (ss l) ^ " " ^ (String.concat " " (List.map ss args))
  | ConjunctionTerm(l, r) -> (s l) ^ ", " ^ (s r)
  | DisjunctionTerm(l, r) -> (s l) ^ "; " ^ (s r)
  | ImplicationTerm(l, r) -> (s l) ^ " => " ^ (s r)
  | AbstractionTerm(b, t) -> b ^ "\\ " ^ (s t)
  | PiTerm(t) -> "pi " ^ (string_of_term t)
  | SigmaTerm(t) -> "sigma " ^ (string_of_term t)

let getTermFVS t =
  let rec fvs t bvs =
    let f t = fvs t bvs in
    match t with
      AtomicTerm _ -> []
    | VariableTerm(v) ->
        if List.exists ((=) v) bvs then
          []
        else
          [v]
    | ApplicationTerm(head,args) -> (f head) @ (List.concat (List.map f args))
    
    | ConjunctionTerm(l, r)
    | DisjunctionTerm(l, r)
    | ImplicationTerm(l, r) -> (f l) @ (f r)
    
    | AbstractionTerm(b, t) -> fvs t (b :: bvs)
    
    | PiTerm(t)
    | SigmaTerm(t) -> f t
  in
  Listutils.unique (fvs t [])

let getAtomName s = match s with
    (AtomicTerm(s)) -> s
  | _ -> raise (Error "Lpabsyn.getAtomName: invalid term")
  
let getApplicationHead app = match app with
    (ApplicationTerm(h,_)) -> h
  | _ -> raise (Error "Lpabsyn.getApplicationHead: invalid term")

let getApplicationArguments app = match app with
    (ApplicationTerm(_,args)) -> args
  | _ -> raise (Error "Lpabsyn.getApplicationArguments: invalid term")

let getVariableName t = match t with
    (VariableTerm(s)) -> s
  | _ -> raise (Error "Lpabsyn.getVariableName: invalid term")
