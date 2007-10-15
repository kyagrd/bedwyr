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
module type Interpreter =
sig
  type session
  exception Exit of session
  exception Logic of string * session

  val setLogics : (string * string) list -> unit
  val onStart : unit -> session
  val onEnd : session -> unit  
  val onPrompt : session -> session
  val onInput : session -> session 
end

module Make (O : Output.Output) (L : Logic.Logic) =
struct
  type session = L.session
  type proofbuilder = L.proof Logic.proofbuilder
  exception Exit of session
  exception Logic of string * session
  exception TacticalSuccess of session
  exception TacticalFailure
  
  (*  This list stores all logic names.  It is used to ensure the logic
      actually exists that when a user tries to change to a new logic
      before raising the appropriate exception. *)
  let logics = ref []
  let setLogics l = logics := l
  
  (*  A flag to determine whether timing is enabled.  *)
  let timing = ref false
  
  (* If set, indicates a directory in which proofs should be stored. *)
  let proof_output = ref None

  (* Name of the current theorem.
   * This is quick, ugly & limited.. TODO: Ask Zach how to make it clean. *)
  let theorem_name = ref ""

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
  
  let helpMessage =
"Taci v0.0

#clear.                     : Clear the screen.
#debug <on | off>.          : Turn debugging on or off.
#proof_output <dir>         : Print proofs to <dir/proof.xml>.
#define <definition>.       : Add the given quoted definition to the current session.
#exit.                      : Exit Taci.
#help.                      : Show this message.
#include <files>            : Add the definitions in the given files to the
                              current session.  File names should be quoted and
                              space separated.
#logic <name>.              : Load the specified logic.  The logic name should
                              be quoted.
#logics.                    : List all available logics.
#open <files>               : Read each line in the given files as a command.
                              File names should be quoted and space separated.
#redo                       : Redo.
#reset.                     : Reset the current session, removing all definitions
                              and removing all sequents.
#tactical <name> <tactical> : Define a tactical with the given name and body.
#tacticals.                 : List all available tacticals.
#theorem <name> <theorem>.  : Prove the given quoted theorem in the current logic.
#time <on | off>.           : Turn timing on or off.
#undo.                      : Undo.
"

  let startupMessage = "Welcome to " ^ helpMessage
  let showHelp () =
    (O.output (helpMessage ^ L.info))

  let showStartup () =
    (O.output (startupMessage ^ L.start))

  (********************************************************************
  *Undo/Redo:
  * There are two stacks; an undo stack and a redo stack.  Every action
  * but undo and redo puts a new item on the undo stack and clears the
  * redo stack.  Undo pops an item off of the undo stack and puts the
  * given session onto the redo stack.  Redo pops an item off of the
  * redo stack and pushes the given stack onto the undo stack.
  ********************************************************************)
  let undoList = ref []
  let redoList = ref []
  let resetLists () =
    undoList := []; redoList := []
  
  let storeSession session =
    undoList := session :: (!undoList);
    redoList := [];
    ()

  let undo session =
    if (List.length (!undoList) > 0) then
      let session' = List.hd (!undoList) in
      (redoList := session :: (!redoList);
      undoList := List.tl (!undoList);
      (L.undo session'))
    else
      (O.error "nothing do undo.\n";
      session)

  let redo session =
    if (List.length (!redoList) > 0) then
      let session' = List.hd (!redoList) in
      (undoList := session :: (!undoList);
      redoList := List.tl (!redoList);
      (L.redo session'))
    else
      (O.error "nothing do redo.\n";
      session)

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
  let tactical pretactical session =
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
      let () = (applyTactical tactical session success failure) in
      session
    with
        Absyn.SyntaxError s ->
          O.error (s ^ ".\n");
          session
      | TacticalSuccess s ->
          O.output "Success.\n";
          if not (L.validSequent s) then begin
            O.output "Proof completed.\n" ;
            O.goal "" ;
            match !proof_output with
              | None -> ()
              | Some dir ->
                  let name     = !theorem_name in
                  let filename = Printf.sprintf "%s/%s.xml" dir name in
                  let chan     = open_out filename in
                    output_string chan (L.string_of_proofs s) ;
                    close_out chan
          end ;
          s
      | TacticalFailure ->
          O.output "Failure.\n";
          session
      | Failure s ->
          O.error (Printf.sprintf "Internal Failure: %s.\n" s);
          session
      | Logic.Interrupt ->
          O.output "Interrupted.\n";
          session

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
      session)
    
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
        let infile = open_in file in
        let commands = Toplevel.parseChannelCommandList infile in
        List.fold_left executeCommand session commands
      with
        Sys_error(s) -> (O.error ("unable to open file '" ^ file ^ "': " ^ s ^ ".\n"); session)
      | Absyn.SyntaxError(s) -> (O.error ("in file '" ^ file ^ "': " ^ s ^ ".\n"); session)
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
        | Absyn.Clear -> (O.clear (); (session, true))
        | Absyn.Help -> (showHelp (); (session, true))
        | Absyn.Undo(_) -> ((undo session), false)
        | Absyn.Redo(_) -> ((redo session), false)
        | Absyn.Reset -> (L.reset (), true)
        | Absyn.Proof_Output name ->
            proof_output := Some (home_unrelate name) ;
            (session, true)
        | Absyn.Theorem(name, t) ->
            theorem_name := name ;
            L.prove name t session, true
        | Absyn.Definitions(ds) ->
            L.definitions ds session, true
        | Absyn.Timing(onoff) ->
            timing := onoff; (session, true)
        | Absyn.Debug(onoff) ->
            Output.showDebug := onoff; (session, true)
        | Absyn.Include(sl) ->
            (L.incl sl session, true)
        | Absyn.Open(sl) ->
            (openFiles session sl, true)
        | Absyn.Logics -> (showLogics session; (session, true))
        | Absyn.Logic(s) -> (loadLogic s session, true)
        | Absyn.Tacticals -> (showTacticals session; (session, true))
        | Absyn.TacticalDefinition(name, pretactical) ->
            (defineTactical name pretactical session, true)
        | Absyn.PreTactical(pretactical) ->
            if (L.validSequent session) then
              (tactical pretactical session, true)
            else
              (O.error "No valid sequent.\n";
              (session, true))
        | Absyn.NoCommand -> (session,true)
    in
 
    (*  Handle the input and then save the session in the undo stack
        only when it is not undo or redo. *)
    let (session', save) = handle input session in
    if save then
      (storeSession session;
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
  ********************************************************************)
  let onStart () =
    (showStartup ();
    resetLists ();
    L.reset ())
  
  (********************************************************************
  *onEnd:
  * This function is called by the interface (see interface.ml) when
  * a logic is unloaded.  It is provided to allow a logic to clean itself
  * up if necessary, though as of now no cleanup function is provided by
  * the Logic.Logic module (see logic.mli).
  ********************************************************************)
  let onEnd session = ()

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
        storeSession session;
        session)
end
