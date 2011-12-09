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

%nonassoc LPAREN
%nonassoc RPAREN

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
  | HASH EXIT DOT                       { System.Command (System.Exit) }
  | HASH HELP DOT                       { System.Command (System.Help) }
  | HASH INCLUDE string_args DOT        { System.Command (System.Include $3) }
  | HASH RESET DOT                      { System.Command (System.Reset) }
  | HASH RELOAD DOT                     { System.Command (System.Reload) }
  | HASH SESSION string_args DOT        { System.Command (System.Session $3) }
  | HASH DEBUG opt_arg DOT              { System.Command (System.Debug $3) }
  | HASH TIME opt_arg DOT               { System.Command (System.Time $3) }
  | HASH EQUIVARIANT opt_arg DOT        { System.Command (System.Equivariant $3) }
  | HASH SHOW_TABLE lower_id DOT        { System.Command (System.Show_table (pos 3,$3)) }
  | HASH CLEAR_TABLES DOT               { System.Command (System.Clear_tables) }
  | HASH CLEAR_TABLE lower_id DOT       { System.Command (System.Clear_table (pos 3,$3)) }
  | HASH SAVE_TABLE lower_id QSTRING DOT{ System.Command (System.Save_table (pos 3,$3,$4)) }
  | HASH ASSERT formula DOT             { System.Command (System.Assert $3) }
  | HASH ASSERT_NOT formula DOT         { System.Command (System.Assert_not $3) }
  | HASH ASSERT_RAISE formula DOT       { System.Command (System.Assert_raise $3) }
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
  | lower_id			        { Type.Ty $1 }
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
  | formula                             { pos 0,$1,Typing.True (pos 0) }
  | formula DEFEQ formula               { pos 0,$1,$3 }

term_list:
  | term_atom                           { $1,[] }
  | term_abs                            { $1,[] }
  | term_atom term_list                 { let t,l = $2 in $1,t::l }

term_atom:
  | LPAREN term RPAREN                  { $2 }
  | token_id                            { $1 }
  | QSTRING                             { Typing.QString (pos 1,$1) }

term_abs:
  | abound_id BSLASH term               { Typing.lambda' (pos 0) [$1] $3 }

term:
  | term_list                           { let t,l = $1 in
                                          Typing.app' (pos 1) t l }
  | token_id INFIX_ID token_id          { Typing.app'
                                            (pos 0)
                                            (Typing.PredConstID (pos 2,$2))
                                            [$1; $3] }

formula:
  | TRUE                                { Typing.True (pos 0) }
  | FALSE                               { Typing.False (pos 0) }
  | term EQ term                        { Typing.Eq (pos 0,$1,$3) }
  | formula AND formula                 { Typing.And (pos 0,$1,$3) }
  | formula OR formula                  { Typing.Or (pos 0,$1,$3) }
  | formula RARROW formula              { Typing.Arrow (pos 0,$1,$3) }
  | binder pabound_list COMMA formula   { Typing.Binder (pos 0,$1,$2,$4) }
  | LPAREN formula RPAREN               { Typing.change_pos (pos 1) $2 (pos 3) }
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
  | upper_id                            { Typing.FreeID (pos 1,$1) }
  | lower_id                            { Typing.PredConstID (pos 1,$1) }

/* misc (commands) */

string_args:
  |                                     { [] }
  | QSTRING string_args                 { $1::$2 }

opt_arg:
  |                                     { None }
  | any_id                              { Some $1 }
  | TRUE                                { Some "true" }
  | FALSE                               { Some "false" }

%%
