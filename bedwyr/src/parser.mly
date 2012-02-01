/****************************************************************************
 * Bedwyr prover                                                            *
 * Copyright (C) 2006-2012 Baelde, Tiu, Ziegler, Heath                      *
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

  let pos i =
    if i = 0 then
      (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
    else
      (Parsing.rhs_start_pos i, Parsing.rhs_end_pos i)

%}

%token SIG MODULE ACCUMSIG ACCUM END
%token KIND TYPE COMMA RARROW CLAUSEEQ DOT
%token IMP BSLASH LPAREN RPAREN CONS
%token KKIND TTYPE DEFINE INDUCTIVE COINDUCTIVE COLON BY DEFEQ SEMICOLON
%token PROP STRING NAT EQ AND OR FORALL EXISTS NABLA TRUE FALSE
%token CLOSE THEOREM QED QUERY IMPORT SPECIFICATION SSPLIT
%token SET SHOW QUIT
%token IND COIND INTROS CASE SEARCH APPLY BACKCHAIN UNFOLD ASSERT_T
%token SPLIT SPLITSTAR LEFT RIGHT PERMUTE
%token INST CUT MONOTONE
%token UNDO SKIP ABORT CLEAR ABBREV UNABBREV
%token TO WITH ON AS KEEP
%token LBRACK RBRACK TURN STAR AT PLUS HASH
%token EXIT HELP INCLUDE RESET RELOAD SESSION DEBUG TIME
%token EQUIVARIANT ENV TYPEOF SHOW_TABLE CLEAR_TABLES CLEAR_TABLE SAVE_TABLE
%token ASSERT ASSERT_NOT ASSERT_RAISE
%token UNDERSCORE

%token <int> NUM
%token <string> UPPER_ID LOWER_ID INFIX_ID INTERN_ID
%token <(Typing.pos * string)> QSTRING
%token EOF

/* Lower */

%nonassoc LPAREN
%nonassoc RPAREN

%nonassoc COMMA
%right RARROW
%left OR
%left AND

%nonassoc BSLASH
%nonassoc EQ

%right INFIX_ID

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
  | KKIND type_clist ki DOT             { System.KKind ($2,$3) }
  | TTYPE const_clist ty DOT            { System.TType ($2,$3) }
  | DEFINE decls BY defs DOT            { System.Def ($2,$4) }
  | DEFINE decls DOT                    { System.Def ($2,[]) }
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
  | EXIT DOT                            { System.Command (System.Exit) }
  | HELP DOT                            { System.Command (System.Help) }
  | INCLUDE string_args DOT             { System.Command (System.Include $2) }
  | RESET DOT                           { System.Command (System.Reset) }
  | RELOAD DOT                          { System.Command (System.Reload) }
  | SESSION string_args DOT             { System.Command (System.Session $2) }
  | DEBUG opt_arg DOT                   { System.Command (System.Debug $2) }
  | TIME opt_arg DOT                    { System.Command (System.Time $2) }
  | EQUIVARIANT opt_arg DOT             { System.Command (System.Equivariant $2) }
  | ENV DOT                             { System.Command (System.Env) }
  | TYPEOF formula DOT                  { System.Command (System.Type_of $2) }
  | SHOW_TABLE lower_id DOT             { System.Command (System.Show_table (pos 2,$2)) }
  | CLEAR_TABLES DOT                    { System.Command (System.Clear_tables) }
  | CLEAR_TABLE lower_id DOT            { System.Command (System.Clear_table (pos 2,$2)) }
  | SAVE_TABLE lower_id QSTRING DOT     { let _,s = $3 in
                                          System.Command (System.Save_table (pos 2,$2,s)) }
  | ASSERT formula DOT                  { System.Command (System.Assert $2) }
  | ASSERT_NOT formula DOT              { System.Command (System.Assert_not $2) }
  | ASSERT_RAISE formula DOT            { System.Command (System.Assert_raise $2) }
  | EOF                                 { raise End_of_file }

/* kinds, types */

type_clist:
  | lower_id                            { [pos 1,$1] }
  | lower_id COMMA type_clist           { (pos 1,$1)::$3 }

ki:
  | TYPE                                { Type.KType }
  | ki RARROW ki                        { Type.ki_arrow $1 $3 }
  | LPAREN ki RPAREN                    { $2 }

const_clist:
  | const_id                            { [pos 1,$1] }
  | const_id COMMA const_clist          { (pos 1,$1)::$3 }

ty:
  | PROP                                { Type.TProp }
  | STRING                              { Type.TString }
  | NAT                                 { Type.TNat }
  | lower_id                            { Type.Ty $1 }
  | UNDERSCORE                          { Type.fresh_tyvar () }
  | ty RARROW ty                        { Type.ty_arrow $1 $3 }
  | LPAREN ty RPAREN                    { $2 }

/* definitions */

decls:
  | decl                                { [$1] }
  | decl COMMA decls                    { $1::$3 }

decl:
  | flavor apred_id                     { let p,name,ty = $2 in ($1,p,name,ty) }

flavor:
  |                                     { System.Normal      }
  | INDUCTIVE                           { System.Inductive   }
  | COINDUCTIVE                         { System.CoInductive }

defs:
  | def                                 { [$1] }
  | def SEMICOLON defs                  { $1::$3 }

def:
  | formula                             { pos 0,$1,Typing.pre_true (pos 0) }
  | formula DEFEQ formula               { pos 0,$1,$3 }

term_list:
  | term_atom                           { $1,[] }
  | term_abs                            { $1,[] }
  | term_atom term_list                 { let t,l = $2 in $1,t::l }

term_atom:
  | TRUE                                { Typing.pre_true (pos 0) }
  | FALSE                               { Typing.pre_false (pos 0) }
  | LPAREN formula RPAREN               { Typing.change_pos (pos 1) $2 (pos 3) }
  | LPAREN term RPAREN                  { $2 }
  | LPAREN INFIX_ID RPAREN              { Typing.pre_predconstid (pos 0) $2 }
  | token_id                            { $1 }
  | QSTRING                             { let p,s = $1 in
                                          Typing.pre_qstring p s }
  | NUM                                 { Typing.pre_nat (pos 1) $1 }

term_abs:
  | abound_id BSLASH term               { Typing.pre_lambda (pos 0) [$1] $3 }

term:
  | term_list %prec INFIX_ID            { let t,l = $1 in
                                          Typing.pre_app (pos 1) t l }
  | term INFIX_ID term                  { Typing.pre_app
                                            (pos 0)
                                            (Typing.pre_predconstid (pos 2) $2)
                                            [$1; $3] }

formula:
  | term EQ term                        { Typing.pre_eq (pos 0) $1 $3 }
  | formula AND formula                 { Typing.pre_and (pos 0) $1 $3 }
  | formula OR formula                  { Typing.pre_or (pos 0) $1 $3 }
  | formula RARROW formula              { Typing.pre_arrow (pos 0) $1 $3 }
  | binder pabound_list COMMA formula   { Typing.pre_binder (pos 0) $1 $2 $4 }
  | term %prec LPAREN                   { $1 }

binder:
  | FORALL                              { Term.Forall }
  | EXISTS                              { Term.Exists }
  | NABLA                               { Term.Nabla }

pabound_list:
  | pabound_id                          { [$1] }
  | pabound_id pabound_list             { $1::$2 }

/* ids */

/* base id types */
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
  | ASSERT_T                            { "assert" }
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

/* shortcuts for other id types */
bound_id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }

const_id:
  | lower_id                            { $1 }
  | INFIX_ID                            { $1 }

any_id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }
  | INFIX_ID                            { $1 }
  | INTERN_ID                           { $1 }

/* annotated id types */
apred_id:
  | lower_id                            { pos 1,$1,Type.fresh_tyvar () }
  | lower_id COLON ty                   { pos 1,$1,$3 }

abound_id:
  | bound_id                            { pos 1,$1,Type.fresh_tyvar () }
  | bound_id COLON ty                   { pos 1,$1,$3 }

pabound_id:
  | bound_id                            { pos 1,$1,Type.fresh_tyvar () }
  | LPAREN bound_id COLON ty RPAREN     { pos 2,$2,$4 }

/* predicate or constant in a term */
token_id:
  | upper_id                            { Typing.pre_freeid (pos 1) $1 }
  | lower_id                            { Typing.pre_predconstid (pos 1) $1 }
  | INTERN_ID                           { Typing.pre_internid (pos 1) $1 }

/* misc (commands) */

string_args:
  |                                     { [] }
  | QSTRING string_args                 { let _,s = $1 in
                                          s::$2 }

opt_arg:
  |                                     { None }
  | any_id                              { Some $1 }
  | ON                                  { Some "on" }
  | TRUE                                { Some "true" }
  | FALSE                               { Some "false" }

%%
