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
     * d (s X) X := body --> d Y X := (Y = s X), body
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
      Term.app System.Logic.andc (prolog@[body])
    in
    (* Quantify existentially over the initial free variables. *)
    let body =
      List.fold_left
        (fun body v ->
           if List.exists (Term.eq v) new_params then body else
             Term.app System.Logic.exists [Term.abstract v body])
        body
        (Term.logic_vars (body::params))
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
    System.Def (head, arity, body)

%}

%token SHARP KIND TYPE DEFINE BY IND COIND
%token DEF DOT COMMA SMCLMN COLUMN
%token EQ AND OR IMP
%token <string> BINDER ID
%token RARROW LARROW PLUS MINUS TIMES
%token BSLASH LPAREN RPAREN
%token <string> STRING

%nonassoc BSLASH
%nonassoc COMMA
%right IMP
%left OR
%left AND
%nonassoc EQ
%right RARROW
%left LARROW
%left PLUS
%left MINUS
%left TIMES

%start input_def input_query
%type <System.input list> input_def
%type <System.input list> input_query

%%

input_def:
  | KIND types_list simple_kind DOT     { [System.Kind ($2, $3)] }
  | TYPE constants_list simple_type DOT { [System.Type ($2, $3)] }
  | DEFINE typing_list BY def_list DOT  { $2@$4 }
  | SHARP sexp DOT                      { let h,t = $2 in
                                          [System.Command (to_string h, t)] }
/* TODO raise an exception if a type isn't new */
types_list:
  | ID                  { [$1] }
  | ID COMMA types_list { ($1)::$3 }

simple_kind:
  | ID			            { Type.Ki $1 }
  | LPAREN simple_kind RPAREN       { $2 }
  | simple_kind RARROW simple_kind  { Type.KRArrow ($1, $3) }

/* TODO raise an exception if a constant isn't new */
constants_list:
  | ID                      { [$1] }
  | ID COMMA constants_list { ($1)::$3 }

simple_type:
  | ID			            { Type.type_atom $1 }
  | LPAREN simple_type RPAREN       { $2 }
  | simple_type RARROW simple_type  { Type.TRArrow ($1, $3) }

typing_list:
  | typing_item                     { [$1] }
  | typing_item COMMA typing_list   { ($1)::$3 }

typing_item:
  | defkind ID COLUMN pred_type { System.Typing ($1, Term.atom $2, Some $4) }
  | defkind ID                  { System.Typing ($1, Term.atom $2, None) }

pred_type:
  | ID			            { Type.prop_atom $1 }
  | LPAREN pred_type RPAREN         { $2 }
  | simple_type RARROW pred_type    { Type.TRArrow ($1, $3) }

defkind:
  |         { System.Normal      }
  | IND     { System.Inductive   }
  | COIND   { System.CoInductive }

def_list:
  | def_item                    { [$1] }
  | def_item SMCLMN def_list    { ($1)::$3}

def_item:
  | sexp DEF exp    { let h,t = $1 in mkdef h t $3 }
  | sexp            { let h,t = $1 in mkdef h t (Term.atom "true") }
  | DEF exp         { System.Query $2 }

input_query:
  | exp DOT         { [System.Query $1] }
  | SHARP sexp DOT  { let (h,t) = $2 in [System.Command (to_string h,t)] }

exp:
  | exp EQ   exp { eq   $1 $3 }
  | exp AND  exp { andc $1 $3 }
  | exp OR   exp { orc  $1 $3 }
  | exp IMP  exp { imp  $1 $3 }
  | BINDER id_list COMMA exp    { let binder = Term.atom $1 in
                                  List.fold_left
                                    (fun t -> fun (was_free,id) ->
                                       let a = Term.atom id in
                                       let x = Term.abstract a t in
                                       if was_free then Term.free id ;
                                       Term.app
                                         binder
                                         [x]
                                    )
                                    $4
                                    $2
                                }
  | sexp         { let (t,l) = $1 in Term.app t l }
  | iexp         { $1 }

id_list:
  | ID          { [Term.is_free $1, $1] }
  | ID id_list  { (Term.is_free $1, $1)::$2 }

/* simple expression (predicate and arguments) */
sexp:
  | lexp { match $1 with
             | [] -> assert false
             | t::l -> t,l }

/* list of expressions */
lexp:
  | aexp        { [$1] }
  | aexp lexp   { $1::$2 }
  | binding exp { let was_free,name = $1 in
                  let a = Term.atom name in
                  let x = Term.abstract a $2 in
                  if was_free then Term.free name ;
                  [x] }

binding:
  | ID BSLASH { (Term.is_free $1, $1) }

/* atomic expression*/
aexp:
  | LPAREN exp RPAREN   { $2 }
  | ID                  { if $1="_" then
                            Term.fresh ~name:"_" Term.Logic ~ts:0 ~lts:0
                          else
                            Term.atom $1 }
  | STRING              { Term.string $1 }

/* There is redundency here, but ocamlyacc seems to have problems
   with left associativity if we abstract it. */
iexp:
  | exp LARROW exp { Term.app (Term.atom "<-") [$1; $3] }
  | exp RARROW exp { Term.app (Term.atom "->") [$1; $3] }
  | exp PLUS   exp { Term.app (Term.atom "+")  [$1; $3] }
  | exp MINUS  exp { Term.app (Term.atom "-")  [$1; $3] }
  | exp TIMES  exp { Term.app (Term.atom "*")  [$1; $3] }

%%

(** Parse a .def file and return the abstract syntax tree as a term.
  * It doesn't have position information, and abstractions make some names
  * disappear, but this could be changed later.
  * [term_of_file] will recurse through #includes and inline them. *)
let to_term ?incl:(incl=true) lexer file =
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
  term_of_list (Term.atom "nil") (list_of_file file [])
