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
  let to_string t = Term.get_name t

  let mkdef head params body =
    (* Replace the params by fresh variables and
     * put the constraints on the parameters in the body:
     * d (s X) X := body --> d Y X := (Y = s X) /\ body
     * As an input we get: [head] (d) [params] ([s X;X]) and [body]. *)

    (* Free the registered names that are bound in the definition clause.
     * If one doesn't do that, a logic variable [X] could be left
     * in the namespace, and persist from one query to another.
     * There shouldn't be any risk to actually free something that was
     * allocated before the parsing of that clause. *)
    let () =
      let v = Term.logic_vars (body::params) in
      List.iter (fun v -> Term.free (Term.get_name v)) v
    in

    (* Create the prolog (new equalities added to the body) and the new set
     * of variables used as parameters.
     * A parameter can be left untouched if it's a variable which didn't
     * occur yet. *)
    let new_params,prolog =
      List.fold_left
        (fun (new_params,prolog) p ->
           match Term.observe p with
             | Term.Var {Term.tag=Term.Logic}
                 when List.for_all (fun v -> v!=p) new_params ->
                 p::new_params,prolog
             | _  ->
                 let v = Term.fresh ~ts:0 ~lts:0 Term.Logic in
                   (v::new_params, (Term.op_eq v p)::prolog))
        ([],[])
        params
    in
    (* Add prolog to the body *)
    let body = if prolog = [] then body else
      List.fold_left
        (fun acc term -> Term.op_and term acc)
        body
        prolog
    in
    (* Quantify existentially over the initial free variables. *)
    let body =
      List.fold_left
        (fun body v ->
           if List.exists (Term.eq v) new_params then body else
             Term.op_binder Term.Exists (Term.abstract v body))
        body
        (Term.logic_vars ([body]))
    in
    (* Finally, abstract over parameters *)
    let arity,body =
      if new_params = [] then 0,body else
        let body =
          List.fold_left (fun body v -> Term.abstract v body)
            body
            new_params
        in match Term.observe body with
          | Term.Lam (n,b) -> n,b
          | _ -> assert false
    in
    (head, arity, body)

  let mkabs (was_free,name,ty) term =
    let a = Term.atom name in
    let x = Term.abstract a term in
    if was_free then Term.free name ;
    x

  let mkquantif binder bindings term =
    List.fold_left
      (fun t b -> Term.op_binder binder (mkabs b t))
      term
      bindings

%}

%token SIG MODULE ACCUMSIG ACCUM END
%token KIND TYPE COMMA RARROW CLAUSEEQ DOT
%token IMP BSLASH LPAREN RPAREN CONS
%token KKIND TTYPE DEFINE INDUCTIVE COINDUCTIVE COLON BY DEFEQ SEMICOLON
%token PROP EQ AND OR FORALL EXISTS NABLA TRUE FALSE
%token CLOSE THEOREM QED QUERY IMPORT SPECIFICATION SSPLIT
%token SET SHOW QUIT
%token IND COIND INTROS CASE SEARCH APPLY BACKCHAIN UNFOLD
%token SPLIT SPLITSTAR LEFT RIGHT PERMUTE
%token INST CUT MONOTONE
%token UNDO SKIP ABORT CLEAR ABBREV UNABBREV
%token TO WITH ON AS KEEP
%token LBRACK RBRACK TURN STAR AT PLUS HASH
%token EXIT HELP INCLUDE RESET RELOAD SESSION DEBUG TIME
%token EQUIVARIANT SHOW_TABLE CLEAR_TABLES CLEAR_TABLE SAVE_TABLE
%token ASSERT ASSERT_NOT ASSERT_RAISE
%token UNDERSCORE

%token <int> NUM
%token <string> UPPER_ID LOWER_ID INFIX_ID QSTRING
%token EOF

/* Lower */

%nonassoc BSLASH
%nonassoc COMMA

%right RARROW
%left OR
%left AND
%nonassoc EQ

/* Higher */

%start input_def input_query
%type <System.input> input_def
%type <System.input> input_query

%%

/* commands */

input_def:
  | top_command                         { $1 }
  | meta_command                        { $1 }

input_query:
  | formula DOT                         { System.Query $1 }
  | meta_command                        { $1 }

top_command:
  | KKIND lower_clist ki DOT            { System.KKind ($2,$3) }
  | TTYPE const_clist ty DOT            { System.TType ($2,$3) }
  | DEFINE decls BY defs DOT            { System.Def ($2,$4) }
  | CLOSE                               { failwith "Abella command only" }
  | THEOREM                             { failwith "Abella command only" }
  | QED                                 { failwith "Abella command only" }
  | QUERY                               { failwith "Abella command only" }
  | IMPORT                              { failwith "Abella command only" }
  | SPECIFICATION                       { failwith "Abella command only" }
  | SSPLIT                              { failwith "Abella command only" }

meta_command:
  | SET                                 { failwith "Abella command only" }
  | SHOW                                { failwith "Abella command only" }
  | QUIT                                { failwith "Abella command only" }
  | HASH EXIT DOT                       { System.Command (System.Exit) }
  | HASH HELP DOT                       { System.Command (System.Help) }
  | HASH INCLUDE string_args DOT        { System.Command (System.Include $3) }
  | HASH RESET DOT                      { System.Command (System.Reset) }
  | HASH RELOAD DOT                     { System.Command (System.Reload) }
  | HASH SESSION string_args DOT        { System.Command (System.Session $3) }
  | HASH DEBUG opt_arg DOT              { System.Command (System.Debug $3) }
  | HASH TIME opt_arg DOT               { System.Command (System.Time $3) }
  | HASH EQUIVARIANT opt_arg DOT        { System.Command (System.Equivariant $3) }
  | HASH SHOW_TABLE lower_id DOT        { System.Command (System.Show_table $3) }
  | HASH CLEAR_TABLES DOT               { System.Command (System.Clear_tables) }
  | HASH CLEAR_TABLE lower_id DOT       { System.Command (System.Clear_table $3) }
  | HASH SAVE_TABLE lower_id QSTRING DOT{ System.Command (System.Save_table ($3,$4)) }
  | HASH ASSERT formula DOT             { System.Command (System.Assert $3) }
  | HASH ASSERT_NOT formula DOT         { System.Command (System.Assert_not $3) }
  | HASH ASSERT_RAISE formula DOT       { System.Command (System.Assert_raise $3) }
  | EOF                                 { raise End_of_file }

/* kinds, types */

lower_clist:
  | lower_id                            { [$1] }
  | lower_id COMMA lower_clist          { $1::$3 }

ki:
  | TYPE                                { Type.KType }
  | ki RARROW ki                        { Type.ki_arrow $1 $3 }
  | LPAREN ki RPAREN                    { $2 }

const_clist:
  | const_id                            { [$1] }
  | const_id COMMA const_clist          { $1::$3 }

ty:
  | PROP                                { Type.TProp }
  | lower_id			        { Type.Ty $1 }
  | ty RARROW ty                        { Type.ty_arrow $1 $3 }
  | LPAREN ty RPAREN                    { $2 }

/* definitions */

decls:
  | decl                                { [$1] }
  | decl COMMA decls                    { $1::$3 }

decl:
  | flavor alower_id                    { let name,ty = $2 in ($1, Term.atom name, ty) }

flavor:
  |                                     { System.Normal      }
  | INDUCTIVE                           { System.Inductive   }
  | COINDUCTIVE                         { System.CoInductive }

defs:
  | def                                 { [$1] }
  | def SEMICOLON defs                  { $1::$3 }

def:
  | term_list                           { let h,t = $1 in mkdef h t Term.op_true }
  | term_list DEFEQ formula             { let h,t = $1 in mkdef h t $3 }

term_list:
  | term_atom                           { $1,[] }
  | term_abs                            { $1,[] }
  | term_atom term_list                 { let t,l = $2 in $1,t::l }

term_atom:
  | LPAREN term RPAREN                  { $2 }
  | bound_id                            { Term.atom $1 }
  | QSTRING                             { Term.string $1 }

term_abs:
  | abound_id BSLASH term               { let name,ty = $1 in
                                          mkabs (Term.is_free name, name, ty) $3 }

term:
  | term_list                           { let t,l = $1 in Term.app t l }
  | bound_id INFIX_ID bound_id          { Term.app (Term.atom $2) [Term.atom $1; Term.atom $2] }

formula:
  | TRUE                                { Term.op_true }
  | FALSE                               { Term.op_false }
  | term EQ term                        { Term.op_eq $1 $3 }
  | formula AND formula                 { Term.op_and $1 $3 }
  | formula OR formula                  { Term.op_or $1 $3 }
  | formula RARROW formula              { Term.op_arrow $1 $3 }
  | binder pabound_list COMMA formula   { mkquantif $1 $2 $4 }
  | LPAREN formula RPAREN               { $2 }
  | term                                { $1 }

binder:
  | FORALL                              { Term.Forall }
  | EXISTS                              { Term.Exists }
  | NABLA                               { Term.Nabla }

pabound_list:
  | pabound_id                          { let name,ty = $1 in
                                          [Term.is_free name, name, ty] }
  | pabound_id pabound_list             { let name,ty = $1 in
                                          (Term.is_free name, name, ty)::$2 }

/* ids */

upper_id:
  | UPPER_ID                            { $1 }
  | UNDERSCORE                          { "_" }

lower_id:
  | LOWER_ID                            { $1 }
  | IND                                 { "induction" }
  | COIND                               { "coinduction" }
  | INTROS                              { "intros" }
  | CASE                                { "case" }
  | SEARCH                              { "search" }
  | APPLY                               { "apply" }
  | BACKCHAIN                           { "backchain" }
  | UNFOLD                              { "unfold" }
  | ASSERT                              { "assert" }
  | SPLIT                               { "split" }
  | SPLITSTAR                           { "split*" }
  | LEFT                                { "left" }
  | RIGHT                               { "right" }
  | PERMUTE                             { "permute" }
  | INST                                { "inst" }
  | CUT                                 { "cut" }
  | MONOTONE                            { "monotone" }
  | UNDO                                { "undo" }
  | SKIP                                { "skip" }
  | ABORT                               { "abort" }
  | CLEAR                               { "clear" }
  | ABBREV                              { "abbrev" }
  | UNABBREV                            { "unabbrev" }

bound_id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }

const_id:
  | lower_id                            { $1 }
  | INFIX_ID                            { $1 }

id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }
  | INFIX_ID                            { $1 }

alower_id:
  | lower_id                            { ($1, Type.fresh_tyvar ()) }
  | lower_id COLON ty                   { ($1, $3) }

abound_id:
  | bound_id                            { ($1, Type.fresh_tyvar ()) }
  | bound_id COLON ty                   { ($1, $3) }

pabound_id:
  | bound_id                            { ($1, Type.fresh_tyvar ()) }
  | LPAREN bound_id COLON ty RPAREN     { ($2, $4) }

/* misc (commands) */

string_args:
  |                                     { [] }
  | QSTRING string_args                 { $1::$2 }

opt_arg:
  |                                     { None }
  | id                                  { Some $1 }
  | TRUE                                { Some "true" }
  | FALSE                               { Some "false" }

%%
