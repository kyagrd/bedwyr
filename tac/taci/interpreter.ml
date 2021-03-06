(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007 Zach Snow, David Baelde                          *
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
let () = Properties.setString "interpreter.proofoutput" ""

module type Interpreter =
sig
  type session
  exception BatchFailure
  exception Exit of session
  exception Logic of string * session

  val setLogics : (string * string) list -> unit
  val onStart : unit -> session
  val onEnd : session -> unit
  val onPrompt : session -> session
  val onInput : session -> session
  val onBatch : session -> session
end


module Make (O : Output.Output) (L : Logic.Logic) =
struct
  type session = L.session
  type proofbuilder = L.proof Logic.proofbuilder
  exception BatchFailure
  exception Exit of session
  exception Logic of string * session
  exception TacticalSuccess of session
  exception TacticalFailure

  (*  This list stores all logic names.  It is used to ensure the logic
      actually exists that when a user tries to change to a new logic
      before raising the appropriate exception. *)
  let logics = ref []
  let setLogics l = logics := l

  (*  errorHandler: called whenever an error that should break batch
      mode occurs.  *)
  let errorHandler session =
    if Properties.getBool "output.batch" then
      raise BatchFailure
    else
      session

  let startTime = ref 0.0
  let startTiming () =
    startTime := Sys.time ()
  let getTiming () =
    (Sys.time ()) -. !startTime

  (* Translate relative paths using the ~ UNIX notation to absolute ones. *)
  let home_unrelate =
    let home =
      try Some (Sys.getenv "HOME") with Not_found -> None
    in
    let unrel s =
      let len = String.length s in
        if len < 2 then
          match home with Some h when s = "~" -> h | _ -> s
        else
          match home, (s.[0] = '~'), (s.[1] = '/') with
            | Some home, true, true ->  (* Something like ~/data/file *)
                Filename.concat home (String.sub s 2 (len - 2))
            | _, true, false ->         (* Something like ~bob/data/file *)
                let index =
                  try String.index s '/' with Not_found -> len
                in
                let user = String.sub s 1 (index - 1) in
                  begin try
                    let home = (Unix.getpwnam user).Unix.pw_dir in
                      Filename.concat home (String.sub s index (len - index))
                  with
                    | Not_found -> s
                  end
            | _ -> s
    in
    unrel

  (********************************************************************
  *findTactical:
  * Given a tactical name and a session, retrieves the tactical from
  * the session's tactical table if it exists.
  ********************************************************************)
  let findTactical name session =
    try
      let tacticals = L.tacticals session in
      let tactical = Logic.Table.find name tacticals in
      Some tactical
    with
      Not_found -> None

  (*  helpMessage: delay so that taci.version gets set; yuck! *)
  let helpMessage () =
    "Taci version " ^ (Properties.getString "taci.version") ^ "!

#open \"<file>\".               Read commands from a file.
#define \"<definition>\".       Add a fixed point definition to the current session.
#include \"<file\".             Read definitions from a Lambda Prolog file.

#theorem <name> \"<theorem>\".  Start proving a theorem.
#lemma <name> \"<lemma>\".      Start proving a lemma.
#lemmas.                      List all available lemmas.

#tactical <name> <body>.      Define a new tactical.
#tacticals.                   List all available tacticals.

#undo.                        Undo last command.
#reset.                       Reset the current session,
                              removing all definitions and pending goals.

#help.                        Show this message.
#exit.                        Exit taci.

#clear.                       Clear the screen.
#debug <on|off>.              Enable/disable debugging.
#time  <on|off>.              Enable/disable timing.
#proof_output \"<dir>\".        Print proofs to <dir/theorem_name.xml>.

#logic \"<logic>\".             Load the given logic.
#logics.                      List all available logics.

#get \"<property>\".            Get the given property.
#set \"<property>\" \"<value>\".  Set the given property to a particular value.

"

  let startupMessage () = "Welcome to " ^ (helpMessage ())
  let showHelp () =
    (O.output ((helpMessage ()) ^ L.info))

  let showStartup () =
    (O.output ((startupMessage ()) ^ L.start))

  (********************************************************************
  *Undo/Redo:
  * There are two stacks; an undo stack and a redo stack.  Every action
  * but undo and redo puts a new item on the undo stack and clears the
  * redo stack.  Undo pops an item off of the undo stack and puts the
  * given session onto the redo stack.  Redo pops an item off of the
  * redo stack and pushes the given item onto the undo stack.
  ********************************************************************)
  type doable =
      Session of L.session
    | Properties of Properties.properties

  let undoList = ref []
  let redoList = ref []
  let resetLists () =
    undoList := []; redoList := []

  let store d =
    undoList := d :: (!undoList);
    redoList := [];
    ()

  let undo session =
    if not (Listutils.empty (!undoList)) then
      let d = List.hd (!undoList) in
      let () = redoList := Session(session) :: (!redoList) in
      let () = undoList := List.tl (!undoList) in
      match d with
          Session(session') -> (L.undo session')
        | Properties(p) -> (Properties.update p; session)
    else
      (O.error "nothing do undo.\n";
      errorHandler session)

  let redo session =
    if (List.length (!redoList) > 0) then
      let d = List.hd (!redoList) in
      let () = undoList := (Session session) :: (!undoList) in
      let () = redoList := List.tl (!redoList) in
      match d with
          Session(session') -> (L.redo session')
        | Properties(p) -> (Properties.update p; session)
    else
      (O.error "nothing do redo.\n";
      errorHandler session)

  (********************************************************************
  *applyTactical:
  * Given a abstract syntax tactical applyTactical extracts the sequents
  * from the current session and applies the tactical to the sequents
  * along with the given success continuation.
  ********************************************************************)
  let applyTactical tactical session sc fc =
    match tactical with
        Absyn.Tactical(tac) ->
          let seqs = L.sequents session in
          tac seqs (sc session) fc
      | Absyn.String(_) ->
          O.impossible "Interpreter.applyTactical: invalid quoted string"

  (********************************************************************
  *buildTactical:
  * Constructs a tactical from an absyn pretactical.  A pretactical
  * has the form of either a quoted or unquoted string.  A tactical
  * should have at its head only an ApplicationTactical (an unquoted
  * tactical name), and any kind of argument.
  ********************************************************************)
  let rec buildTactical tac session =
    let buildArg tac =
      match tac with
          Absyn.ApplicationPreTactical(_) -> (buildTactical tac session)
        | Absyn.StringPreTactical(s) -> Absyn.String(s)
    in
    match tac with
        Absyn.ApplicationPreTactical(name, args) ->
          let top = findTactical name session in
          if Option.isSome top then
            let t = Option.get top in
            Absyn.Tactical(t session (List.map buildArg args))
          else
            raise (Absyn.SyntaxError ("undefined tactical: " ^ name))
      | Absyn.StringPreTactical(s) ->
          raise (Absyn.SyntaxError ("unexpected quoted string: " ^ s))

  (********************************************************************
  *tactical:
  * Attempts to apply the given pretactical. A success continuation is
  * created that, when called, raises the TacticalSuccess exception to
  * return control to the toplevel loop.  A failure continuation that
  * raises TacticalFailure is also created.  Then, the tactical is
  * constructed from the pretactical.  Finally it is applied to the current
  * sequents.  The call to applyTactical never returns; instead one
  * of the continuations is called.  This ensures that the stack doesn't
  * get blown.
  ********************************************************************)
  let tactical pretactical session = (* TODO timing *)
    (******************************************************************
    *success:
    * The toplevel success continuation.  Note that, along with raising
    * the success exception, this updates the current proof builder by
    * composing the current and new builders, and updates the current
    * sequents by concatenating the new and old sequents.  For more
    * information about what new and old sequents are see Logic.mli.
    ******************************************************************)
    let success session newSequents oldSequents proofBuilder continue =
      let currentProof = L.proof session in
      let proof' = (Logic.composeProofBuilders proofBuilder currentProof) in
      let session' = L.update (newSequents @ oldSequents) proof' session in
      raise (TacticalSuccess(session'))
    in

    (******************************************************************
    *failure:
    * The toplevel failure continuation.  This simply raises the failure
    * exception.
    ******************************************************************)
    let failure () =
      raise TacticalFailure
    in

    try
      O.debug (Printf.sprintf "Pretactical: %s.\n"
                 (Absyn.string_of_pretactical pretactical)) ;
      let tactical = buildTactical pretactical session in
      let () = O.debug ("Built tactical.\n") in
      let () = startTiming () in
      let () = (applyTactical tactical session success failure) in
      assert false
    with
        Absyn.SyntaxError s ->
          (O.error (s ^ ".\n");
          errorHandler session)
      | TacticalSuccess s ->
          if Properties.getBool "taci.timing" then
            O.output ("Time: " ^ (string_of_float (getTiming ())) ^ " seconds.\n");

          O.output "Success.\n";
          if not (L.validSequent s) then
            (O.output "Proof completed.\n" ;
            O.goal "" ;

            (*  Save the proof output.  *)
            (match Properties.getString "interpreter.proofoutput" with
              | "" -> ()
              | dir ->
                  let name = L.theoremName s in
                  let name = if name = "" then "proof" else name in
                  let filename = Printf.sprintf "%s/%s.xml" dir name in
                  let chan = open_out filename in
                  output_string chan (L.string_of_proofs s) ;
                  close_out chan) ;
            L.proved s)
          else
            s
      | TacticalFailure ->
          O.output "Failure.\n";
          errorHandler session
      | Failure s ->
          O.error (Printf.sprintf "Internal Failure: %s.\n" s);
          errorHandler session
      | Logic.Interrupt ->
          O.output "Interrupted.\n";
          errorHandler session

  (********************************************************************
  *makeTactical:
  * Given a tactical name and a abstract syntax tactical, this function
  * wraps the tactical so that it has the type of a logic tactical.
  * This will allow it to be entered into the session tactical table.
  ********************************************************************)
  let makeTactical name t = fun session args ->
    match args with
      [] -> fun sequents sc fc -> (t sequents sc fc)
    | _ -> fun _ _ fc -> (O.error (name ^ ": invalid arguments.\n"); fc ())

  (********************************************************************
  *defineTactical:
  * Given a tactical name and an absyn pretactical, this function
  * creates a logic tactical from the pretactical and then enters it
  * into the session tactical table under the given name.
  ********************************************************************)
  let defineTactical name pretactical session =
    match (buildTactical pretactical session) with
        Absyn.Tactical(t) ->
          let t' = makeTactical name t in
          (L.defineTactical name t' session)
      | _ -> session

  (********************************************************************
  *showLogics:
  * Lists all logics available.
  ********************************************************************)
  let showLogics session =
    let compare' (_,n) (_,n') = compare n n' in
    (O.logics (List.sort compare' !logics))

  (********************************************************************
  *showTacticals:
  * Lists all tacticals available.
  ********************************************************************)
  let showTacticals session =
    let get k _ result =
      k::result
    in
    let tacticals = Logic.Table.fold get (L.tacticals session) [] in
    let tacticals' = List.sort compare tacticals in
    O.tacticals tacticals'

  (********************************************************************
  *loadLogic:
  * Loads the given logic.  It first ensures that said logic exists,
  * then raises the Logic exception which tells the interface to stop
  * the main loop and tell the driver to load a new interface (see
  * main.ml).
  ********************************************************************)
  let loadLogic l session =
    if (List.mem_assoc l !logics) then
      raise (Logic(l,session))
    else
      (O.error ("undefined logic '" ^ l ^ "'.\n");
      errorHandler session)

  (********************************************************************
  *openFiles:
  * Open each file and read each command in it.  If any error is
  * encountered the given session is returned unchanged.
  ********************************************************************)
  let rec openFiles session files =
    let executeCommand session command =
      handleInput command session
    in

    let executeFile session file =
      try
        let () = Sys.chdir (Filename.dirname file) in
        let infile = open_in (Filename.basename file) in
        let commands = Toplevel.parseChannelCommandList infile in
        List.fold_left executeCommand session commands
      with
        Sys_error(s) ->
          (O.error ("unable to open '" ^ file ^ "': " ^ s ^ "\n");
          errorHandler session)
      | Absyn.SyntaxError(s) ->
          (O.error ("in file '" ^ file ^ "': " ^ s ^ "\n");
          errorHandler session)
    in
    List.fold_left executeFile session files

  (********************************************************************
  *handleInputList:
  * Parses a list of commands and handles each in turn.
  ********************************************************************)
  and handleInputList inputlist session =
    let handle' session input =
      let session' = (handleInput input session) in
      if L.validSequent session' then
        (O.goal ((L.string_of_sequents session') ^ "\n");
        session')
      else
        session'
    in
    List.fold_left handle' session inputlist

  (********************************************************************
  *handleInput:
  * Given an absyn command, executes it and returns the new session.
  * Special care is taken to ensure that all functions except undo and
  * redo add the current session to the undo stack.  Undo and redo
  * do not change the stack in this way so that they work correctly:
  * if undo were to place the current session on the undo stack, it
  * only one level of undo would work.
  ********************************************************************)
  and handleInput input session =
    let handle input session =
      match input with
          Absyn.Exit -> raise (Exit session)
        | Absyn.Set(p,v) ->
            (*  Set doesn't actually get undone.  *)
            let props = Properties.state () in
            Properties.setString p v;
            (session, Some (Properties(props)))
        | Absyn.Get(p) ->
            O.output ("Property: " ^ p ^ " = " ^ (Properties.getString p) ^ "\n");
            (session, Some (Session(session)))
        | Absyn.Clear -> (O.clear (); (session, Some (Session(session))))
        | Absyn.Help -> (showHelp (); (session, Some (Session(session))))
        | Absyn.Undo(_) -> ((undo session), None)
        | Absyn.Redo(_) -> ((redo session), None)
        | Absyn.Reset ->
            let session' = L.reset () in
            (session', Some (Session(session)))
        | Absyn.ProofOutput name ->
            (*  Proof Output doesn't get undone.  *)
            let dir = (home_unrelate name) in
            let props = Properties.state () in
            (O.output ("Proof output set to '" ^ dir ^ "'\n");
            Properties.setString "interpreter.proofoutput" dir;
            (session, Some (Properties(props))))
        | Absyn.Lemma(name, t) ->
            (L.lemma name t session, Some (Session(session)))
        | Absyn.Lemmas ->
            (L.lemmas session, Some (Session(session)))
        | Absyn.Theorem(name, t) ->
            (L.theorem name t session, Some (Session(session)))
        | Absyn.Definitions(ds) ->
            (L.definitions ds session, Some (Session(session)))
        | Absyn.Timing(onoff) ->
            let props = Properties.state () in
            (Properties.setBool "taci.timing" onoff;
            (session, Some (Properties(props))))
        | Absyn.Debug(onoff) ->
            let props = Properties.state () in
            (Properties.setBool "output.debug" onoff;
            (session, Some (Properties(props))))
        | Absyn.Include(sl) ->
            (L.incl sl session, Some (Session(session)))
        | Absyn.Open(sl) ->
            let session' = openFiles session sl in
            (session', Some (Session(session)))
        | Absyn.Logics -> (showLogics session; (session, Some (Session(session))))
        | Absyn.Logic(s) -> (loadLogic s session, Some (Session(session)))
        | Absyn.Tacticals -> (showTacticals session; (session, Some (Session(session))))
        | Absyn.TacticalDefinition(name, pretactical) ->
            (defineTactical name pretactical session, Some (Session(session)))
        | Absyn.PreTactical(pretactical) ->
            if (L.validSequent session) then
              let () = O.beginComputation () in
              let session' = tactical pretactical session in
              let () = O.endComputation () in
              (session', Some (Session(session)))
            else
              (O.error "No valid sequent.\n";
              (errorHandler session, Some(Session(session))))
        | Absyn.LogicDefined(id, args) ->
            (L.logicDefined id args session, Some (Session(session)))
    in

    (*  Handle the input and then save the session in the undo stack
        only when it is not undo or redo. *)
    let (session', save) = handle input session in
    if Option.isSome save then
      (store (Option.get save);
      session')
    else
      (session')

  (********************************************************************
  *getLogicKey:
  * Given the print name of a logic, retrieves its associated key name.
  ********************************************************************)
  let getLogicKey name =
    let find = fun (_,n) -> n = name in
    let (k,_) = List.find find !logics in
    k

  (********************************************************************
  *onPrompt:
  * This function is called by the interface (see interface.ml) to print
  * the appropriate prompt.  In the console case it prints a prompt
  * indicating the current logic by key name.
  ********************************************************************)
  let onPrompt session =
    (O.prompt ("[tac <" ^ (getLogicKey L.name) ^ ">]- ");
    session)

  (********************************************************************
  *onStart:
  * This function is called by the interface (see interface.ml) when
  * a logic is first loaded.  It shows startup information and clears
  * the undo and redo lists, as well as creating and returning a new
  * session.
  *
  * Note the hackery with endComputation: this is so the GUI can reset
  * whatever it is using as an indicator that Tac is computing.
  ********************************************************************)
  let onStart () =
    (showStartup ();
    resetLists ();
    O.endComputation ();
    L.reset ())

  (********************************************************************
  *onEnd:
  * This function is called by the interface (see interface.ml) when
  * a logic is unloaded.  It is provided to allow a logic to clean itself
  * up if necessary, though as of now no cleanup function is provided by
  * the Logic.Logic module (see logic.mli) for onEnd to even call.
  ********************************************************************)
  let onEnd session = ()

  (********************************************************************
  *onBatch:
  ********************************************************************)
  let onBatch session =
    openFiles session [(Properties.getString "output.batchfile")]

  (********************************************************************
  *onInput:
  * This function is called once per iteration of the toplevel loop by
  * the interface (see interface.ml).  It reads an absyn command from
  * stdin and then handles it with respect to the given session,
  * returning the new session.
  ********************************************************************)
  let onInput session =
    try
      let input = Toplevel.parseStdinCommand () in
      let session' = handleInputList [input] session in
      session'
    with
      Absyn.SyntaxError(s) ->
        (O.error (s ^ ".\n");

        (*  Store the session if there was a parse error.
            This ensures that undo will always restore the
            previous state even in the case of a parse error. *)
        store (Session(session));
        errorHandler session)
end
