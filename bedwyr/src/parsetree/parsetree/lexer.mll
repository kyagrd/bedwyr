(****************************************************************************)
(* Bedwyr -- lexing                                                         *)
(* Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler, Andrew Gacek *)
(* Copyright (C) 2011-2013,2015 Quentin Heath                               *)
(* Copyright (C) 2013 Alwen Tiu                                             *)
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

{
  (** Wrapper around some Failures raised in Lexer. *)
  exception EOF_error of string

  (** No valid token could be parsed from the input.
    * It might contain a valid prefix, though,
    * and in particular the provided byte could be a valid character,
    * but it often is the first byte of a multibyte unicode character. *)
  exception Illegal_byte_sequence of char

  (** An unmatched "/*" or a "*/" was found in a quoted string.
    * In order to allow for commenting a block of valid code without
    * breaking the whole file, comment delimiters must be properly escaped
    * (for instance "/\*" and "*\/") or balanced.
    * Note that escaping the first character instead of the second
    * ("\/*" or "\*/") doesn't prevent this exception. *)
  exception Illegal_string_comment of IO.Pos.t

  (** Some characters that are only allowed in prefix names
    * were used next to some that are only allowed in infix names.
    * This happens to be forbidden for compatibility reasons;
    * a separating sequence (spaces, tabs, carriage returns, line feeds),
    * a comment or a quoted string is needed between two such names. *)
  exception Illegal_token of string * string

  (** The hash character was misused, or a meta-command was misspelled. *)
  exception Unknown_command of string

  open Parser
  open Lexing

  let flush_input lexbuf =
    flush_input lexbuf ;
    lexbuf.lex_curr_p <-
      { lexbuf.lex_curr_p with pos_bol = 0 ; pos_lnum = 1 }

  (* == Quoted strings ============================================== *)

  (* keep track of the content of a quoted string
   * across multiple lines *)
  let strbuf = Buffer.create 128

  let escape_table = Hashtbl.create 4
  let _ = List.iter (fun (k,t) -> Hashtbl.replace escape_table k t)
            [ (* standard escaping sequences *)
              'b',  '\b' ;
              't',  '\t' ;
              'n',  '\n' ;
              'r',  '\r' ;
            ]

  let addChar c = Buffer.add_char strbuf c
  let addEscapedChar c = addChar
                           (try Hashtbl.find escape_table c
                            with Not_found -> c)
  let addString s = Buffer.add_string strbuf s

  (* == Token tables ================================================ *)

  let command_table = Hashtbl.create 22
  let _ = List.iter (fun (k,t) -> Hashtbl.replace command_table k t)
            [ (* Bedwyr meta-commands *)
              "exit",           EXIT ;
              "help",           HELP ;
              "include",        INCLUDE ;
              "reset",          RESET ;
              "reload",         RELOAD ;
              "session",        SESSION ;
              "debug",          DEBUG ;
              "time",           TIME ;
              "equivariant",    EQUIVARIANT ;
              "freezing",       FREEZING ;
              "saturation",     SATURATION ;
              "env",            ENV ;
              "typeof",         TYPEOF ;
              "show_def",       SHOW_DEF ;
              "show_table",     SHOW_TABLE ;
              "clear_tables",   CLEAR_TABLES ;
              "clear_table",    CLEAR_TABLE ;
              "save_table",     SAVE_TABLE ;
              "export",         EXPORT ;
              "assert",         ASSERT ;
              "assert_not",     ASSERT_NOT ;
              "assert_raise",   ASSERT_RAISE ;
            ]
  let get_command n =
    try Hashtbl.find command_table n
    with Not_found -> raise (Unknown_command n)

  (* Upper-case tokens *)
  let ub_keyword_t = Hashtbl.create 5
  let _ = List.iter (fun (k,t) -> Hashtbl.replace ub_keyword_t k t)
            [ (* Bedwyr upper-case keywords *)
              "Kind",           KKIND ;
              "Type",           TTYPE ;
              "Define",         DEFINE ;
              "Theorem",        THEOREM ;
              "Qed",            QED ;
            ]
  let ua_keyword_t = Hashtbl.create 8
  let _ = List.iter (fun (k,t) -> Hashtbl.replace ua_keyword_t k t)
            [ (* Abella upper-case keywords *)
              "Close",          CLOSE ;
              "Query",          QUERY ;
              "Import",         IMPORT ;
              "Specification",  SPECIFICATION ;
              "Split",          SSPLIT ;
              "Set",            SET ;
              "Show",           SHOW ;
              "Quit",           QUIT ;
            ]
  let get_upper n =
    try Hashtbl.find ub_keyword_t n
    with Not_found -> begin
      try Hashtbl.find ua_keyword_t n
      (* free variable in a query, bound variable otherwise *)
      with Not_found -> UPPER_ID n
    end

  (* Lower-case tokens *)
  let lb_keyword_t = Hashtbl.create 3
  let _ = List.iter (fun (k,t) -> Hashtbl.replace lb_keyword_t k t)
            [ (* Bedwyr lower-case keywords *)
              "inductive",      INDUCTIVE ;
              "coinductive",    COINDUCTIVE ;
              "by",             BY ;
            ]
  let lb_primitive_t = Hashtbl.create 9
  let _ = List.iter (fun (k,t) -> Hashtbl.replace lb_primitive_t k t)
            [ (* Bedwyr lower-case primitive operators and constants *)
              "type",           TYPE ;
              "prop",           PROP ;
              "string",         STRING ;
              "nat",            NAT ;
              "forall",         FORALL ;
              "exists",         EXISTS ;
              "nabla",          NABLA ;
              "true",           TRUE ;
              "false",          FALSE ;
            ]
  let la_keyword_t = Hashtbl.create 5
  let _ = List.iter (fun (k,t) -> Hashtbl.replace la_keyword_t k t)
            [ (* Abella lower-case keywords, except for tactics *)
              "to",             TO ;
              "with",           WITH ;
              "on",             ON ;
              "as",             AS ;
              "keep",           KEEP ;
            ]
  let la_tactic_t = Hashtbl.create 23
  let _ = List.iter (fun (k,t) -> Hashtbl.replace la_tactic_t k t)
            [ (* Abella tactics, except for "exists" and "split*" *)
              "induction",      IND_T ;
              "coinduction",    COIND_T ;
              "intros",         INTROS_T ;
              "case",           CASE_T ;
              "search",         SEARCH_T ;
              "apply",          APPLY_T ;
              "backchain",      BACKCHAIN_T ;
              "unfold",         UNFOLD_T ;
              "assert",         ASSERT_T ;
              "split",          SPLIT_T ;
              "left",           LEFT_T ;
              "right",          RIGHT_T ;
              "permute",        PERMUTE_T ;
              "inst",           INST_T ;
              "cut",            CUT_T ;
              "monotone",       MONOTONE_T ;
              "undo",           UNDO_T ;
              "skip",           SKIP_T ;
              "abort",          ABORT_T ;
              "clear",          CLEAR_T ;
              "abbrev",         ABBREV_T ;
              "unabbrev",       UNABBREV_T ;
            ]
  let lt_keyword_t = Hashtbl.create 22
  let _ = List.iter (fun (k,t) -> Hashtbl.replace lt_keyword_t k t)
            [ (* Teyjus lower-case keywords *)
              "sig",            TEYJUS_KEYWORD ;
              "module",         TEYJUS_KEYWORD ;
              "accum_sig",      TEYJUS_KEYWORD ;
              "accumulate",     TEYJUS_KEYWORD ;
              "end",            TEYJUS_KEYWORD ;
              "kind",           TEYJUS_KEYWORD ;
              "closed",         TEYJUS_KEYWORD ;
              "exportdef",      TEYJUS_KEYWORD ;
              "import",         TEYJUS_KEYWORD ;
              "infix",          TEYJUS_KEYWORD ;
              "infixl",         TEYJUS_KEYWORD ;
              "infixr",         TEYJUS_KEYWORD ;
              "local",          TEYJUS_KEYWORD ;
              "localkind",      TEYJUS_KEYWORD ;
              "postfix",        TEYJUS_KEYWORD ;
              "posfixl",        TEYJUS_KEYWORD ;
              "prefix",         TEYJUS_KEYWORD ;
              "prefixr",        TEYJUS_KEYWORD ;
              "typeabbrev",     TEYJUS_KEYWORD ;
              "use_sig",        TEYJUS_KEYWORD ;
              "useonly",        TEYJUS_KEYWORD ;
              "!",              TEYJUS_KEYWORD ;
            ]
  let get_lower n =
    try Hashtbl.find lb_keyword_t n
    with Not_found -> begin
      try Hashtbl.find lb_primitive_t n
      with Not_found -> begin
        try Hashtbl.find la_keyword_t n
        with Not_found -> begin
          try Hashtbl.find la_tactic_t n
          with Not_found -> begin
            try Hashtbl.find lt_keyword_t n
            (* bound variable, type, prefix constant or predicate *)
            with Not_found -> LOWER_ID n
          end
        end
      end
    end

  (* Internal tokens *)
  let get_intern n =
    (* non-logical predefined constant *)
    INTERN_ID n

  (* Infix-case tokens *)
  let ib_primitive_t = Hashtbl.create 2
  let _ = List.iter (fun (k,t) -> Hashtbl.replace ib_primitive_t k t)
            [ (* Bedwyr infix-case primitive operators and constants *)
              "->",             RARROW ;
              "*",              STAR ;
              "=",              EQ ;
            ]
  let ia_primitive_t = Hashtbl.create 1
  let _ = List.iter (fun (k,t) -> Hashtbl.replace ia_primitive_t k t)
            [ (* Abella infix-case primitive operators and constants *)
              "|-",             TURN ;
            ]
  let it_primitive_t = Hashtbl.create 2
  let _ = List.iter (fun (k,t) -> Hashtbl.replace it_primitive_t k t)
            [ (* Teyjus infix-case primitive operators and constants *)
              ":-",             TEYJUS_KEYWORD ;
              "=>",             TEYJUS_KEYWORD ;
            ]
  let get_infix n =
    try Hashtbl.find ib_primitive_t n
    with Not_found -> begin
      try Hashtbl.find it_primitive_t n
      (* infix constant *)
      with Not_found -> INFIX_ID n
    end

  (* == Comments ==================================================== *)

  type comment_continuation =
    | Previous_token of token
    | Continuation of (lexbuf -> token)
}

let digit = ['0'-'9']
let number = digit+

let uchar = ['A'-'Z']
let lchar = ['a'-'z']

(* special symbols *)
let prefix_special       = ['?' '!' '`' '\'' '$']
let tail_special_noslash = ['_' '@' '#'] | digit
let infix_special_nostar = ['-' '^' '<' '>' '=' '~' '+' '&' ':' '|']
let infix_special        = infix_special_nostar | '*'

let safe_char_noslash =
  uchar | lchar |  prefix_special | tail_special_noslash
let safe_char = safe_char_noslash | '/'

let upper_name  = uchar safe_char*
let lower_name  = (lchar|prefix_special) safe_char*
let infix_name  = infix_special+
let intern_name = '_' safe_char+

let blank = ' ' | '\t' | '\r'

let in_comment = '/' | '*' | [^'/' '*' '\n']+
let in_qstring = [^'\\' '"' '\n' '/' '*']+

rule token = parse
  (* Multi-line and single-line comments *)
  | "/*"                        { comment 0 (Continuation token) lexbuf }
  | ('%'|"#!") [^'\n']* '\n'    { new_line lexbuf; token lexbuf }
  | ('%'|"#!") [^'\n']*         { token lexbuf }

  (* Separators *)
  | blank                       { token lexbuf }
  | '\n'                        { new_line lexbuf; token lexbuf }

  | '"'                         { Buffer.clear strbuf ;
                                  let pos_of_lexbuf =
                                    IO.Pos.of_lexbuf lexbuf
                                  in
                                  qstring pos_of_lexbuf [] None lexbuf }

  (* Punctuation *)
  | ":"                         { COLON }
  | ":="                        { DEFEQ }
  | ";"                         { SEMICOLON }
  | ","                         { COMMA }
  | "."                         { DOT }
  | "("                         { LPAREN }
  | ")"                         { RPAREN }

  (* Bedwyr meta-commands *)
  | '#' (lower_name as n)       { get_command n }

  (* Bedwyr primitive operators and constants *)
  | "/\\"                       { AND }
  | "\\/"                       { OR }
  | "\\"                	{ BSLASH }

  (* Abella tactics *)
  | "split*"                    { SPLITSTAR_T }

  (* Abella primitive operators and constants *)
  | "{"                         { LBRACK }
  | "}"                         { RBRACK }

  (* Upper-case prefix names *)
  | upper_name as n             { get_upper n }
  | (upper_name as n) "/*"      { comment 0 (Previous_token (get_upper n)) lexbuf }

  (* Lower-case prefix names *)
  | lower_name as n             { get_lower n }
  | (lower_name as n) "/*"      { comment 0 (Previous_token (get_lower n)) lexbuf }

  (* Internal prefix names *)
  | intern_name as n            { get_intern n }
  | (intern_name as n) "/*"     { comment 0 (Previous_token (get_intern n)) lexbuf }

  (* Infix-case names *)
  | infix_name as n             { get_infix n }

  (* Placeholder *)
  | '_'                         { UNDERSCORE }
  | "_/*"                       { comment 0 (Previous_token UNDERSCORE) lexbuf }

  | ('-'? number) as n          { NUM (int_of_string n) }

  (* Ambiguous names *)
  | ((safe_char* safe_char_noslash) as n1) (infix_name as n2)
  | (safe_char+ as n1) ((infix_special_nostar infix_special*) as n2)
  | (infix_name as n1) (safe_char+ as n2)
                                { raise (Illegal_token (n1,n2)) }

  (* misc *)
  | eof                         { EOF }

  | _ as c                      { raise (Illegal_byte_sequence c) }

and proof = parse
  | '\n'                        { new_line lexbuf ;
                                  proof lexbuf }
  | "Qed"                       { QED }
  | '.'                         { DOT }
  | eof                         { EOF }
  | upper_name
  | lower_name
  | intern_name
  | _                           { proof lexbuf }

and comment level cont = parse
  | in_comment                  { comment level cont lexbuf }
  | "/*"                        { comment (level + 1) cont lexbuf }
  | "*/"                        { if level = 0 then
                                    match cont with
                                      | Continuation k -> k lexbuf
                                      | Previous_token t -> t
                                  else
                                    comment (level - 1) cont lexbuf }
  | '\n'                        { new_line lexbuf ;
                                  comment level cont lexbuf }
  | eof                         { raise (EOF_error "comment not closed") }

and qstring pos_of_lexbuf starts finish = parse
  | "\\\n"                      { new_line lexbuf ;
                                  qstring pos_of_lexbuf starts finish lexbuf }
  | "\\/*" as s | "/*" as s     { addString s ;
                                  let pos = IO.Pos.of_lexbuf lexbuf () in
                                  let starts = pos :: starts in
                                  qstring pos_of_lexbuf starts finish lexbuf }
  | "\\*/" as s | "*/" as s     { addString s ;
                                  match starts,finish with
                                    | (_ :: starts),_ ->
                                        qstring pos_of_lexbuf starts finish lexbuf
                                    | [],None ->
                                        let pos = IO.Pos.of_lexbuf lexbuf () in
                                        qstring pos_of_lexbuf starts (Some pos) lexbuf
                                    | _ ->
                                        qstring pos_of_lexbuf starts finish lexbuf }
  | '\\' (_ as c)               { addEscapedChar c ;
                                  qstring pos_of_lexbuf starts finish lexbuf }
  | in_qstring as s             { addString s ;
                                  qstring pos_of_lexbuf starts finish lexbuf }
  | '"'                         { match starts,finish with
                                    | (pos :: _),_ | _,Some pos ->
                                        raise (Illegal_string_comment pos)
                                    | _ ->
                                        let pos = pos_of_lexbuf () in
                                        QSTRING (pos,Buffer.contents strbuf) }
  | '\n'                        { addChar '\n' ;
                                  new_line lexbuf ;
                                  qstring pos_of_lexbuf starts finish lexbuf }
  | (('/' | '*') as c)          { addChar c ;
                                  qstring pos_of_lexbuf starts finish lexbuf }
  | eof                         { raise (EOF_error "string not closed") }
