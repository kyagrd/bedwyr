/****************************************************************************
 * Bedwyr prover                                                            *
 * Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *
 *                                                                          *
 * This program is free software; you can redistribute it and/or modify     *
 * it under the terms of the GNU General Public License as published by     *
 * the Free Software Foundation; either version 2 of the License, or        *
 * (at your option) any later version.                                      *
 *                                                                          *
 * This program is distributed in the hope that it will be useful,          *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of           *
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *
 * GNU General Public License for more details.                             *
 *                                                                          *
 * You should have received a copy of the GNU General Public License        *
 * along with this code; if not, write to the Free Software Foundation,     *
 * Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *
 ****************************************************************************/

%{
  let eq   = Term.binop System.Logic.eq
  let andc = Term.binop System.Logic.andc
  let orc  = Term.binop System.Logic.orc
  let imp  = Term.binop System.Logic.imp

  let to_string t =
    match Term.observe t with
      | Term.Var {Term.name=s;Term.tag=Term.Constant} -> s
      | _ -> assert false

  let mkdef kind head params body =
    let vars = Term.logic_vars (body::params) in
    (* Replace the params by fresh variables and
     * put the constraints on the parameters in the body:
     * d (s X) X := ... --> d Y Z := (Y = s X), Z=X, ... *)
    (* Avoid useless intermediate parameters, such a Z on the example TODO *)
    let params,prolog =
      List.fold_left
        (fun (params,prolog) p ->
           let v = Term.fresh 0 in
             (v::params, (eq v p)::prolog))
        ([],[])
        params
    in
    (* Add prolog to the body *)
    let body = if prolog = [] then body else
      Term.app (Term.atom System.Logic.andc) (prolog@[body])
    in
    (* Abstract over the initial free variables,
     * and quantify existentially over them. *)
    let body =
      List.fold_left
        (fun body v ->
           Term.app (Term.atom System.Logic.exists)
             [Term.abstract_var v body])
        body
        vars
    in
    (* Finally, abstract over parameters *)
    let arity,body =
      if params = [] then 0,body else
        let body =
          List.fold_left (fun body v -> Term.abstract_var v body)
            body
            params
        in match Term.observe body with
          | Term.Lam (n,b) -> n,b
          | _ -> assert false
    in
      System.Def (kind, to_string head, arity, body)

%}

%token BSLASH LPAREN RPAREN DOT SHARP
%token EQ AND IMP RARROW LARROW OR PLUS MINUS TIMES
%token DEF IND COIND
%token <string> ID
%token <string> STRING

%nonassoc BSLASH
%right IMP
%left AND
%left OR
%nonassoc EQ
%right RARROW
%left LARROW
%left PLUS
%left MINUS
%left TIMES

%start input_def input_query
%type <System.input> input_def
%type <System.input> input_query

%%

input_def:
| defkind sexp DEF exp DOT { let h,t = $2 in mkdef $1 h t $4 }
| defkind sexp DOT         { let h,t = $2 in mkdef $1 h t (Term.atom "true") }
| DEF exp DOT              { System.Query $2 }
| SHARP sexp DOT           { let h,t = $2 in System.Command (to_string h,t) }
defkind:
|       { System.Normal      }
| IND   { System.Inductive   }
| COIND { System.CoInductive }

input_query:
| exp DOT          { System.Query $1 }
| SHARP sexp DOT   { let (h,t) = $2 in System.Command (to_string h,t) }

exp:
| exp EQ   exp { eq   $1 $3 }
| exp AND  exp { andc $1 $3 }
| exp OR   exp { orc  $1 $3 }
| exp IMP  exp { imp  $1 $3 }
| exp iexp exp { Term.app $2 [$1; $3] }
| sexp         { let (t,l) = $1 in Term.app t l }

sexp:
| lexp { match $1 with
          | [] -> assert false
          | t::l -> t,l }
lexp:
| aexp          { [$1] }
| ID BSLASH exp { [Term.abstract $1 $3] }
| aexp lexp     { $1::$2 }

aexp:
| LPAREN exp RPAREN { $2 }
| ID { Term.atom $1 }
| STRING { Term.string $1 }

iexp:
| LARROW { Term.atom "<-" }
| RARROW { Term.atom "->" }
| PLUS { Term.atom "+" }
| MINUS { Term.atom "-" }
| TIMES { Term.atom "*" }
