/****************************************************************************
(* Bedwyr -- parsing                                                        *)
 * Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler, Andrew Gacek *
 * Copyright (C) 2011-2013,2015 Quentin Heath                               *
 * Copyright (C) 2013 Alwen Tiu                                             *
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
 * You should have received a copy of the GNU General Public License along  *
 * with this program; if not, write to the Free Software Foundation, Inc.,  *
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *
 ****************************************************************************/

%{

open Preterm

  let pos = IO.Pos.of_token

  let generic_error i s =
    raise (Parse_error (pos i,"Unexpected input",s))

  let eof_error s =
    raise (Parse_error (pos 0,"Unexpected end of file",s))
%}

/* Punctuation */
%token COLON DEFEQ SEMICOLON COMMA DOT LPAREN RPAREN

/* Bedwyr meta-commands */
%token EXIT HELP INCLUDE RESET RELOAD SESSION
%token DEBUG TIME EQUIVARIANT FREEZING SATURATION
%token ENV TYPEOF SHOW_DEF
%token SHOW_TABLE CLEAR_TABLES CLEAR_TABLE SAVE_TABLE EXPORT
%token ASSERT ASSERT_NOT ASSERT_RAISE
/* Bedwyr keywords */
%token KKIND TTYPE DEFINE THEOREM QED
%token INDUCTIVE COINDUCTIVE BY
%token UNDERSCORE
/* Bedwyr primitives */
%token TYPE PROP STRING NAT FORALL EXISTS NABLA TRUE FALSE
%token RARROW STAR EQ AND OR BSLASH

/* Abella keywords, including tactics, apart from "exists" */
%token CLOSE QUERY IMPORT SPECIFICATION SSPLIT SET SHOW QUIT
%token TO WITH ON AS KEEP
%token IND_T COIND_T INTROS_T CASE_T SEARCH_T APPLY_T BACKCHAIN_T UNFOLD_T
%token ASSERT_T SPLIT_T SPLITSTAR_T LEFT_T RIGHT_T PERMUTE_T INST_T CUT_T
%token MONOTONE_T UNDO_T SKIP_T ABORT_T CLEAR_T ABBREV_T UNABBREV_T
/* Abella primitives */
%token TURN LBRACK RBRACK

/* Teyjus keywords and primitives */
%token TEYJUS_KEYWORD

%token <int> NUM
%token <string> UPPER_ID LOWER_ID INFIX_ID INTERN_ID
%token <(IO.Pos.t * string)> QSTRING
%token EOF

/* Lower */
%nonassoc BINDER
%right RARROW
%left OR
%left AND
%nonassoc EQ

%right COMMA STAR

%nonassoc BSLASH

%right INFIX_ID

%nonassoc LPAREN RPAREN
/* Higher */

%start skip skip_proof definition_mode toplevel term_mode
%type <unit> skip
%type <unit> skip_proof
%type <Preterm.definition_mode> definition_mode
%type <Preterm.toplevel> toplevel
%type <Preterm.term_mode> term_mode

%%

/* entry points */

skip:
  | DOT                                 { () }
  | EOF                                 { () }

skip_proof:
  | DOT skip_proof                      { $2 }
  | QED DOT                             { () }
  | EOF                                 { eof_error "an Abella proof" }

definition_mode:
  | command                             { `Command $1 }
  | meta_command                        { `MetaCommand $1 }
  | EOF                                 { raise Empty_command }
  | error DOT                           { generic_error 1 "a definition file" }
  | error EOF                           { eof_error "a definition file" }

toplevel:
  | term DOT                            { `Term (pos 1,$1) }
  | meta_command                        { `MetaCommand $1 }
  | EOF                                 { raise Empty_term }
  | error DOT                           { generic_error 1 "the toplevel" }
  | error EOF                           { eof_error "the toplevel" }

term_mode:
  | term DOT                            { `Term (pos 1,$1) }
  | EOF                                 { raise Empty_term }
  | error DOT                           { generic_error 1 "the term input" }
  | error EOF                           { eof_error "the term input" }

/* input type */

command:
  | KKIND type_clist ki DOT             { Preterm.Command.Kind ($2,$3) }
  | TTYPE const_clist ty DOT            { Preterm.Command.Type ($2,$3) }
  | DEFINE decls BY defs DOT            { Preterm.Command.Def ($2,$4) }
  | DEFINE decls DOT                    { Preterm.Command.Def ($2,[]) }
  | THEOREM theorem DOT                 { Preterm.Command.Theorem $2 }
  | QED DOT                             { Preterm.Command.Qed (pos 0) }
  | CLOSE                               { failwith "Abella command only." }
  | QUERY                               { failwith "Abella command only." }
  | IMPORT                              { failwith "Abella command only." }
  | SPECIFICATION                       { failwith "Abella command only." }
  | SSPLIT                              { failwith "Abella command only." }

meta_command:
  | EXIT DOT                            { Preterm.MetaCommand.Exit }
  | HELP DOT                            { Preterm.MetaCommand.Help }
  | INCLUDE string_args DOT             { Preterm.MetaCommand.Include $2 }
  | RESET DOT                           { Preterm.MetaCommand.Session [] }
  | RELOAD DOT                          { Preterm.MetaCommand.Reload }
  | SESSION string_args DOT             { Preterm.MetaCommand.Session $2 }
  | DEBUG opt_bool DOT                  { Preterm.MetaCommand.Debug $2 }
  | TIME opt_bool DOT                   { Preterm.MetaCommand.Time $2 }
  | EQUIVARIANT opt_bool DOT            { Preterm.MetaCommand.Equivariant $2 }
  | FREEZING opt_nat DOT                { Preterm.MetaCommand.Freezing $2 }
  | SATURATION opt_nat DOT              { Preterm.MetaCommand.Saturation $2 }
  | ENV DOT                             { Preterm.MetaCommand.Env }
  | TYPEOF term DOT                     { Preterm.MetaCommand.Type_of $2 }
  | SHOW_DEF lower_id DOT               { Preterm.MetaCommand.Show_def (pos 2,$2) }
  | SHOW_TABLE lower_id DOT             { Preterm.MetaCommand.Show_table (pos 2,$2) }
  | CLEAR_TABLES DOT                    { Preterm.MetaCommand.Clear_tables }
  | CLEAR_TABLE lower_id DOT            { Preterm.MetaCommand.Clear_table (pos 2,$2) }
  | SAVE_TABLE lower_id QSTRING DOT     { let _,s = $3 in
                                          Preterm.MetaCommand.Save_table (pos 2,$2,s) }
  | EXPORT QSTRING DOT                  { let _,s = $2 in
                                          Preterm.MetaCommand.Export s }
  | ASSERT term DOT                     { Preterm.MetaCommand.Assert $2 }
  | ASSERT_NOT term DOT                 { Preterm.MetaCommand.Assert_not $2 }
  | ASSERT_RAISE term DOT               { Preterm.MetaCommand.Assert_raise $2 }
  | SET                                 { failwith "Abella command only" }
  | SHOW                                { failwith "Abella command only" }
  | QUIT                                { failwith "Abella command only" }

/* kinds, types */

type_clist:
  | lower_id                            { [pos 1,$1] }
  | type_clist COMMA lower_id           { (pos 3,$3)::$1 }

ki:
  | TYPE RARROW ki                      { Preterm.Typing.Kind.arrow
                                            [Preterm.Typing.Kind.ktype] $3 }
  | TYPE                                { Preterm.Typing.Kind.ktype }
  | LPAREN ki RPAREN                    { $2 }

const_clist:
  | const_id                            { [pos 1,$1] }
  | const_clist COMMA const_id          { (pos 3,$3)::$1 }

ty_tuple:
  | ty_tuple STAR ty_singleton          { let ty1,ty2,tys = $1 in
                                          ty1,ty2,$3::tys }
  | ty_singleton STAR ty_singleton      { $1,$3,[] }

ty:
  | ty RARROW ty                        { Preterm.Typing.Type.arrow [$1] $3 }
  | ty_tuple                            { let ty1,ty2,tys = $1 in
                                          Preterm.Typing.Type.tuple ty1 ty2 tys }
  | ty_singleton                        { $1 }

ty_singleton:
  | ty_list                             { let p,n,l = $1 in
                                          Preterm.Typing.Type.const p n l }
  | ty_atom2                            { $1 }

ty_list:
  | lower_id                            { (pos 1),$1,[] }
  | ty_list ty_atom                     { let p,n,l = $1 in p,n,$2::l }

ty_atom:
  | lower_id                            { Preterm.Typing.Type.const (pos 1) $1 [] }
  | ty_atom2                            { $1 }

ty_atom2:
  | PROP                                { Preterm.Typing.Type.prop }
  | STRING                              { Preterm.Typing.Type.string }
  | NAT                                 { Preterm.Typing.Type.nat }
  | UNDERSCORE                          { Preterm.Typing.Type.fresh_param () }
  | UPPER_ID				{ Preterm.Typing.Type.get_param $1 }
  | LPAREN ty RPAREN                    { $2 }

/* definitions */

decls:
  | decl                                { [$1] }
  | decls COMMA decl                    { $3::$1 }

decl:
  | flavour apred_id                    { let p,n,ty = $2 in ($1,p,n,ty) }

flavour:
  |                                     { Normal      }
  | INDUCTIVE                           { Inductive   }
  | COINDUCTIVE                         { CoInductive }

defs:
  | def                                 { [$1] }
  | def SEMICOLON defs                  { $1::$3 }

def:
  | term                                { pos 0,$1,pre_true (pos 0) }
  | term DEFEQ term                     { pos 0,$1,$3 }

theorem:
  | lower_id COLON term                 { pos 1,$1,$3 }

/* terms (with or without logical connectives) */

term_tuple:
  | term_tuple COMMA singleton          { let t1,t2,l = $1 in
                                          t1,t2,$3::l }
  | singleton COMMA singleton           { $1,$3,[] }

term:
  | term EQ term                        { pre_eq (pos 0) $1 $3 }
  | term AND term                       { pre_and (pos 0) $1 $3 }
  | term OR term                        { pre_or (pos 0) $1 $3 }
  | term RARROW term                    { pre_arrow (pos 0) $1 $3 }
  | term_tuple                          { let t1,t2,l = $1 in
                                          pre_tuple (pos 0) t1 t2 l }
  | singleton                           { $1 }

singleton:
  | binder pabound_list COMMA term %prec BINDER
                                        { pre_binder (pos 0) $1 $2 $4 }
  | term_list %prec INFIX_ID            { let t,l = $1 in
                                          pre_app (pos 1) t l }

term_list:
  | term_atom                           { $1,[] }
  | term_list INFIX_ID term_list        { let hd =
                                            pre_predconstid
                                              ~infix:true (pos 2) $2
                                          in
                                          let t1,l1 = $1 in
                                          let t1 = pre_app (pos 1) t1 l1 in
                                          let t3,l3 = $3 in
                                          let t3 = pre_app (pos 3) t3 l3 in
                                          hd,[t3;t1] }
  | term_list term_atom                 { let t,l = $1 in t,$2::l }

term_atom:
  | QSTRING                             { let p,s = $1 in
                                          pre_qstring p s }
  | NUM                                 { pre_nat (pos 1) $1 }
  | token_id                            { $1 }
  | TRUE                                { pre_true (pos 0) }
  | FALSE                               { pre_false (pos 0) }
  | term_abs                            { $1 }
  | LPAREN term RPAREN                  { $2 }
  | LPAREN INFIX_ID RPAREN              { pre_predconstid
                                            ~infix:true (pos 0) $2 }

term_abs:
  | abound_id BSLASH term               { pre_lambda (pos 0) [$1] $3 }

binder:
  | FORALL                              { Ndcore.Term.Forall }
  | EXISTS                              { Ndcore.Term.Exists }
  | NABLA                               { Ndcore.Term.Nabla }

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
  | IND_T                               { "induction" }
  | COIND_T                             { "coinduction" }
  | INTROS_T                            { "intros" }
  | CASE_T                              { "case" }
  | SEARCH_T                            { "search" }
  | APPLY_T                             { "apply" }
  | BACKCHAIN_T                         { "backchain" }
  | UNFOLD_T                            { "unfold" }
  | ASSERT_T                            { "assert" }
  | SPLIT_T                             { "split" }
  | LEFT_T                              { "left" }
  | RIGHT_T                             { "right" }
  | PERMUTE_T                           { "permute" }
  | INST_T                              { "inst" }
  | CUT_T                               { "cut" }
  | MONOTONE_T                          { "monotone" }
  | UNDO_T                              { "undo" }
  | SKIP_T                              { "skip" }
  | ABORT_T                             { "abort" }
  | CLEAR_T                             { "clear" }
  | ABBREV_T                            { "abbrev" }
  | UNABBREV_T                          { "unabbrev" }

/* shortcuts for other id types */
bound_id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }

const_id:
  | lower_id                            { $1 }
  | INFIX_ID                            { ("("^$1^")") }

any_id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }
  | INFIX_ID                            { ("("^$1^")") }
  | INTERN_ID                           { $1 }

/* annotated id types */
apred_id:
  | lower_id                            { pos 1,$1,Preterm.Typing.Type.fresh_param () }
  | lower_id COLON ty                   { pos 1,$1,$3 }

abound_id:
  | bound_id                            { pos 1,$1,Preterm.Typing.Type.fresh_param () }
  | bound_id COLON ty                   { pos 1,$1,$3 }

pabound_id:
  | bound_id                            { pos 1,$1,Preterm.Typing.Type.fresh_param () }
  | LPAREN bound_id COLON ty RPAREN     { pos 2,$2,$4 }

/* predicate or constant in a term */
token_id:
  | upper_id                            { pre_freeid (pos 1) $1 }
  | lower_id                            { pre_predconstid (pos 1) $1 }
  | INTERN_ID                           { pre_internid (pos 1) $1 }

/* misc (commands) */

string_args:
  |                                     { [] }
  | QSTRING string_args                 { let _,s = $1 in
                                          s::$2 }

opt_bool:
  |                                     { None }
  | any_id                              { Some $1 }
  | ON                                  { Some "on" }
  | TRUE                                { Some "true" }
  | FALSE                               { Some "false" }

opt_nat:
  |                                     { -1 }
  | NUM                                 { $1 }

%%
