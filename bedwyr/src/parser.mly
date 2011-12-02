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
  let eq   a b = Term.app System.Logic.eq   [a;b]
  let andc a b = Term.app System.Logic.andc [a;b]
  let orc  a b = Term.app System.Logic.orc  [a;b]
  let imp  a b = Term.app System.Logic.imp  [a;b]

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
                   (v::new_params, (eq v p)::prolog))
        ([],[])
        params
    in
    (* Add prolog to the body *)
    let body = if prolog = [] then body else
      List.fold_left
        (fun acc term -> Term.app System.Logic.andc ([term;acc]))
        body
        prolog
    in
    (* Quantify existentially over the initial free variables. *)
    let body =
      List.fold_left
        (fun body v ->
           if List.exists (Term.eq v) new_params then body else
             Term.app System.Logic.exists [Term.abstract v body])
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

%}

%token SIG MODULE ACCUMSIG ACCUM END
%token KIND TYPE COMMA RARROW CLAUSEEQ DOT
%token IMP BSLASH LPAREN RPAREN CONS
%token KKIND TTYPE DEFINE INDUCTIVE COINDUCTIVE COLON BY DEFEQ SEMICOLON
%token EQ AND OR FORALL EXISTS NABLA TRUE FALSE
%token CLOSE THEOREM QUERY IMPORT SPECIFICATION SSPLIT
%token IND COIND INTROS CASE SEARCH APPLY BACKCHAIN UNFOLD ASSERT
%token SPLIT SPLITSTAR LEFT RIGHT PERMUTE
%token INST CUT MONOTONE
%token UNDO SKIP ABORT CLEAR ABBREV UNABBREV
%token TO WITH ON AS KEEP
%token SET SHOW QUIT
%token LBRACK RBRACK TURN STAR AT PLUS HASH

%token UNDERSCORE

%token <int> NUM
%token <string> UPPER_ID STRINGID QSTRING
%token EOF

/* Lower */

%nonassoc BSLASH
%nonassoc COMMA
%right RARROW
%right IMP
%left OR
%left AND
%nonassoc EQ
%left PLUS
%left TIMES

/* Higher */

%start input_def input_query
%type <System.input> input_def
%type <System.input> input_query

%%

input_def:
  | bedwyr_command                      { $1 }
  | abella_command                      { $1 }
bedwyr_command:
  | KKIND id_list ki DOT                { System.KKind ($2,$3) }
  | TTYPE id_list ty DOT                { System.TType ($2,$3) }
  | DEFINE decls BY defs DOT            { System.Def ($2,$4) }
  | HASH metaapp DOT                    { let h,t = $2 in
                                          System.Command (to_string h, t) }
  | EOF                                 { raise End_of_file }

id_list:
  | id                                  { [$1] }
  | id COMMA id_list                    { $1::$3 }

ki:
  | id			                { Type.Ki $1 }
  | ki RARROW ki                        { Type.ki_arrow $1 $3 }
  | LPAREN ki RPAREN                    { $2 }

ty:
  | id			                { Type.Ty $1 }
  | ty RARROW ty                        { Type.ty_arrow $1 $3 }
  | LPAREN ty RPAREN                    { $2 }

decls:
  | decl                                { [$1] }
  | decl COMMA decls                    { $1::$3 }

decl:
  | flavor aid                          { ($1, $2) }

flavor:
  |                                     { System.Normal      }
  | INDUCTIVE                           { System.Inductive   }
  | COINDUCTIVE                         { System.CoInductive }

aid:
  | id                                  { (Term.atom $1, Type.fresh_tyvar ()) }
  | id COLON ty                         { (Term.atom $1, $3) }

defs:
  | def                                 { [$1] }
  | def SEMICOLON defs                  { $1::$3 }

def:
  | metaapp                             { let h,t = $1 in mkdef h t (Term.atom "true") }
  | metaapp DEFEQ metaterm              { let h,t = $1 in mkdef h t $3 }

metaapp:
  | lexp                                { match $1 with
                                            | [] -> assert false
                                            | t::l -> t,l }
  | ASSERT lexp                         { Term.atom "assert",$2 }
                                        /* XXX virer ça, c'est dégueu
                                         * (ne serait-ce que parce que
                                         * ça autorise "assert" dans
                                         * une vrai expression), par
                                         * exemple en utilisant autre
                                         * chose que metaapp pour les
                                         * instructions */

lexp:
  | aexp                                { [$1] }
  | aexp lexp                           { $1::$2 }
  | binding metaterm                    { let was_free,name = $1 in
                                          let a = Term.atom name in
                                          let x = Term.abstract a $2 in
                                          if was_free then Term.free name ;
                                          [x] }

aexp:
  | LPAREN metaterm RPAREN              { $2 }
  | UNDERSCORE                          { Term.fresh ~name:"_" Term.Logic ~ts:0 ~lts:0 }
  | id                                  { Term.atom $1 }
  | QSTRING                             { Term.string $1 }

binding:
  | id BSLASH                           { (Term.is_free $1, $1) }

metaterm:
  | metaterm EQ metaterm                { eq   $1 $3 }
  | metaterm AND metaterm               { andc $1 $3 }
  | metaterm OR metaterm                { orc  $1 $3 }
  | metaterm RARROW metaterm            { imp  $1 $3 }
    /* XXX add types */
  | binder binding_list COMMA metaterm  { List.fold_left
                                            (fun t -> fun (was_free,id,ty) ->
                                               let a = Term.atom id in
                                               let x = Term.abstract a t in
                                               if was_free then Term.free id ;
                                               Term.app
                                                 $1
                                                 [x]
                                            )
                                            $4
                                            $2
                                        }
  | metaapp                             { let (t,l) = $1 in Term.app t l }

binder:
  | FORALL                              { System.Logic.forall }
  | EXISTS                              { System.Logic.exists }
  | NABLA                               { System.Logic.nabla }

binding_list:
  |                                     { [] }
  | paid binding_list                   { let name,ty = $1 in
                                          (Term.is_free name, name, ty)::$2 }

paid:
  | id                                  { ($1, Type.fresh_tyvar ()) }
  | LPAREN id COLON ty RPAREN           { ($2, $4) }
  | UNDERSCORE                          { ("_", Type.fresh_tyvar ()) }
  | LPAREN UNDERSCORE COLON ty RPAREN   { ("_", $4) }

abella_command:
  | CLOSE                               { failwith "Abella command only" }
  | THEOREM                             { failwith "Abella command only" }
  | QUERY                               { failwith "Abella command only" }
  | IMPORT                              { failwith "Abella command only" }
  | SPECIFICATION                       { failwith "Abella command only" }
  | SSPLIT                              { failwith "Abella command only" }
  | IND                                 { failwith "Abella command only" }
  | COIND                               { failwith "Abella command only" }
  | INTROS                              { failwith "Abella command only" }
  | CASE                                { failwith "Abella command only" }
  | SEARCH                              { failwith "Abella command only" }
  | APPLY                               { failwith "Abella command only" }
  | BACKCHAIN                           { failwith "Abella command only" }
  | UNFOLD                              { failwith "Abella command only" }
  | ASSERT                              { failwith "Abella command only" }
  | EXISTS                              { failwith "Abella command only" }
  | SPLIT                               { failwith "Abella command only" }
  | SPLITSTAR                           { failwith "Abella command only" }
  | LEFT                                { failwith "Abella command only" }
  | RIGHT                               { failwith "Abella command only" }
  | PERMUTE                             { failwith "Abella command only" }
  | INST                                { failwith "Abella command only" }
  | CUT                                 { failwith "Abella command only" }
  | MONOTONE                            { failwith "Abella command only" }
  | UNDO                                { failwith "Abella command only" }
  | SKIP                                { failwith "Abella command only" }
  | ABORT                               { failwith "Abella command only" }
  | CLEAR                               { failwith "Abella command only" }
  | ABBREV                              { failwith "Abella command only" }
  | UNABBREV                            { failwith "Abella command only" }
  | SET                                 { failwith "Abella command only" }
  | SHOW                                { failwith "Abella command only" }
  | QUIT                                { failwith "Abella command only" }

    /* XXX trouver comment prendre en compte les mots-clés
     * sans générer masse de conflicts reduce/reduce */
id:
  | UPPER_ID                            { $1 }
  | STRINGID                            { $1 }
  | TRUE                                { "true" }
  | FALSE                               { "false" }
/*| SIG                                 { failwith "Abella reserved keyword" }
  | MODULE                              { failwith "Abella reserved keyword" }
  | ACCUMSIG                            { failwith "Abella reserved keyword" }
  | ACCUM                               { failwith "Abella reserved keyword" }
  | END                                 { failwith "Abella reserved keyword" }
  | KIND                                { failwith "Abella reserved keyword" }*/
  | TYPE                                { "type" }
/*| CLAUSEEQ                            { failwith "Abella reserved keyword" }
  | IMP                                 { failwith "Abella reserved keyword" }
  | CONS                                { failwith "Abella reserved keyword" }
  | KKIND                               { failwith "Reserved keyword" }
  | TTYPE                               { failwith "Reserved keyword" }
  | DEFINE                              { failwith "Reserved keyword" }
  | INDUCTIVE                           { failwith "Reserved keyword" }
  | COINDUCTIVE                         { failwith "Reserved keyword" }
  | COLON                               { failwith "Reserved keyword" }
  | BY                                  { failwith "Reserved keyword" }
  | DEFEQ                               { failwith "Reserved keyword" }
  | SEMICOLON                           { failwith "Reserved keyword" }
  | EQ                                  { failwith "Reserved keyword" }
  | AND                                 { failwith "Reserved keyword" }
  | OR                                  { failwith "Reserved keyword" }
  | FORALL                              { failwith "Reserved keyword" }
  | EXISTS                              { failwith "Reserved keyword" }
  | NABLA                               { failwith "Reserved keyword" }
  | CLOSE                               { failwith "Abella reserved keyword" }
  | THEOREM                             { failwith "Abella reserved keyword" }
  | QUERY                               { failwith "Abella reserved keyword" }
  | IMPORT                              { failwith "Abella reserved keyword" }
  | SPECIFICATION                       { failwith "Abella reserved keyword" }
  | SSPLIT                              { failwith "Abella reserved keyword" }
  | IND                                 { failwith "Abella reserved keyword" }
  | COIND                               { failwith "Abella reserved keyword" }
  | INTROS                              { failwith "Abella reserved keyword" }
  | CASE                                { failwith "Abella reserved keyword" }
  | SEARCH                              { failwith "Abella reserved keyword" }
  | APPLY                               { failwith "Abella reserved keyword" }
  | BACKCHAIN                           { failwith "Abella reserved keyword" }
  | UNFOLD                              { failwith "Abella reserved keyword" }
  | ASSERT                              { failwith "Abella reserved keyword" }
  | SPLIT                               { failwith "Abella reserved keyword" }
  | SPLITSTAR                           { failwith "Abella reserved keyword" }
  | LEFT                                { failwith "Abella reserved keyword" }
  | RIGHT                               { failwith "Abella reserved keyword" }
  | PERMUTE                             { failwith "Abella reserved keyword" }
  | INST                                { failwith "Abella reserved keyword" }
  | CUT                                 { failwith "Abella reserved keyword" }
  | MONOTONE                            { failwith "Abella reserved keyword" }
  | UNDO                                { failwith "Abella reserved keyword" }
  | SKIP                                { failwith "Abella reserved keyword" }
  | ABORT                               { failwith "Abella reserved keyword" }
  | CLEAR                               { failwith "Abella reserved keyword" }
  | ABBREV                              { failwith "Abella reserved keyword" }
  | UNABBREV                            { failwith "Abella reserved keyword" }
  | TO                                  { failwith "Abella reserved keyword" }
  | WITH                                { failwith "Abella reserved keyword" }
  | ON                                  { failwith "Abella reserved keyword" }
  | AS                                  { failwith "Abella reserved keyword" }
  | KEEP                                { failwith "Abella reserved keyword" }
  | SET                                 { failwith "Abella reserved keyword" }
  | SHOW                                { failwith "Abella reserved keyword" }
  | QUIT                                { failwith "Abella reserved keyword" }
  | LBRACK                              { failwith "Abella reserved keyword" }
  | RBRACK                              { failwith "Abella reserved keyword" }
  | TURN                                { failwith "Abella reserved keyword" }
  | AT                                  { failwith "Abella reserved keyword" }*/

input_query:
  | metaterm DOT                        { System.Query $1 }
  | HASH metaapp DOT                    { let (h,t) = $2 in
                                          System.Command (to_string h,t) }
  | EOF                                 { raise End_of_file }

%%

(** Parse a .def file and return the abstract syntax tree as a term.
  * It doesn't have position information, and abstractions make some names
  * disappear, but this could be changed later.
  * [term_of_file] will recurse through #includes and inline them.
  * XXX commented out until updated/removed *)
(*let to_term ?incl:(incl=true) lexer file =
  let lam  = Term.atom "lam"  in
  let app  = Term.atom "app"  in
  let atom = Term.atom "atom" in
  let inclfiles = ref [] in
  let binder x =
    List.exists
      (Term.eq x)
      [System.Logic.forall;System.Logic.exists;System.Logic.nabla]
  in
  let logic x =
    List.exists
      (Term.eq x)
      [System.Logic.eq;System.Logic.andc;System.Logic.orc;System.Logic.imp]
  in
  let rec split acc = function
    | [] -> assert false
    | [x] -> x,List.rev acc
    | x::tl -> split (x::acc) tl
  in
  (* De-flatten conjunction, disjunctions and application,
   * add explicit abstractions, applications and atom constructors. *)
  let rec objectify term =
    match Term.observe term with
      | Term.Lam (0,x) -> objectify x
      | Term.Lam (n,x) ->
          Term.app lam [Term.lambda 1 (objectify (Term.lambda (n-1) x))]
      | Term.App (x,h::tl) ->
          if binder x then begin
            assert (tl = []) ;
            match Term.observe h with
              | Term.Lam (1,h) -> Term.app x [Term.lambda 1 (objectify h)]
              | _ -> assert false
          end else if logic x then
            if tl=[] then objectify h else
              Term.app x [ objectify h ;
                           objectify (Term.app x tl) ]
          else
            if tl=[] then Term.app app [ objectify x; objectify h ] else
              let y,l = split [] (h::tl) in
              Term.app app [ objectify (Term.app x l);
                             objectify y ]
      | _ -> Term.app atom [term]
  in
  let clause  = Term.atom "clause"  in
  let query   = Term.atom "query"   in
  let command = Term.atom "command" in
  let rec list_of_file file list =
    let lexbuf = Lexing.from_channel (open_in file) in
    let rec aux l =
      let input =
        try
          Some (input_def lexer lexbuf)
        with Failure "eof" -> None
      in
      match input with
        | None -> l
        | Some i ->
            List.fold_left
              (fun l -> function
                | System.Kind _ -> l
                | System.Type _ -> l
                | System.Typing (kind,head,stype) -> l
                | System.Def (head,arity,body) ->
                    let body = objectify (Term.lambda arity body) in
                    aux ((Term.app clause [ head;
                                            body ])::l)
                | System.Query a -> aux ((Term.app query [a])::l)
                | System.Command ("include",[file]) ->
                    let file = Term.get_name file in
                    let not_included fname =
                          if ((List.mem fname !inclfiles) || (not incl)) then false
                          else (
                                  inclfiles := fname :: !inclfiles ;
                                  true
                          )
                    in
                    if not_included file then aux (list_of_file file l)
                    (*  begin *)
                    (*  	    let cwd = Sys.getcwd () in *)
                    (*  	    Sys.chdir (Filename.dirname file) ; *)
                    (*  	    let l = list_of_file file l in *)
                    (*        Sys.chdir cwd ; *)
                    (*  	    aux l *)
                    (*  end *)
                    else aux l

                | System.Command ("assert",a) ->
                    aux ((Term.app command ((Term.atom "assert")::
                                              (List.map objectify a)))::l)
                (* [AT]: change parsing to type command to allow polymorphic types; *)
                (*       Free variables (eigen or logic) are abstracted. *)
                | System.Command ("type",[a;b]) ->
                    let b = Term.app (Term.atom "ty") [Norm.deep_norm b] in
                    let vs = (Term.logic_vars [b]) @ (Term.eigen_vars [b]) in
                    let ty = List.fold_left
                               (fun x v ->
                                 Term.app (Term.atom "all") [(Term.abstract v x)])
                               b vs in

                    aux ((Term.app command ((Term.atom "type")::[a;ty]))::l)
                | System.Command (c,a) ->
                    aux ((Term.app command ((Term.atom c)::a))::l)
              )
              l
              i
    in
    let cwd = Sys.getcwd () in
    Sys.chdir (Filename.dirname file) ;
    let l = aux list in
    Sys.chdir cwd ;
    l
  in
  let cons = Term.binop "cons" in
  let rec term_of_list t = function
    | [] -> t
    | hd::tl -> term_of_list (cons hd t) tl
  in
  inclfiles := [] ;
  term_of_list (Term.atom "nil") (list_of_file file [])*)
