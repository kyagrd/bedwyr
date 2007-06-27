module type Interpreter =
sig
  type session
  exception Exit of session
  exception Logic of string

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
  exception Logic of string
  exception Success of session * proofbuilder
  exception Failure
  
  let timing = ref false
  
  (********************************************************************
  *findTactical:
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
#define <definition>.       : Add the given definition to the current session.
#exit.                      : Exit Taci.
#help.                      : Show this message.
#include <files>            : Add the definitions in the given files to the
                              current session.  File names should be surrounded
                              by quotes and separated by spaces.
#open <files>               : Read each line in the given files as a command.
                              File names should be surrounded by quotes and
                              separated by spaces.
#redo                       : Redo.
#reset.                     : Reset the current session, removing all definitions
                              and removing all sequents.
#tactical <name> <tactical> : Define a tactical with the given name and body.
#tacticals.                 : List all available tacticals.
#theorem <name> <theorem>.  : Prove the given theorem in the current logic.
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
    (undoList := []; redoList := [])
  
  let storeSession session =
    (undoList := session :: (!undoList);
    redoList := [];
    ())

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
  ********************************************************************)
  let applyTactical tactical session sc =
    match tactical with
        Absyn.Tactical(tac) ->
          let seqs = L.sequents session in
          tac seqs (sc session)
      | Absyn.String(_) -> failwith "invalid quoted string"
    
  (********************************************************************
  *buildTactical:
  * Constructs a tactical from an absyn pretactical.
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
  * Attempts to apply the given pretactical.
  ********************************************************************)
  let tactical pretactical session =
    (******************************************************************
    *success:
    * The toplevel success continuation.
    ******************************************************************)
    let success session newSequents oldSequents proofBuilder continue =
      let currentProof = L.proof session in
      let proof' = (Logic.composeProofBuilders proofBuilder currentProof) in
      let session' = L.update (newSequents @ oldSequents) proof' session in
      raise (Success(session', proof'))
    in
    
    (******************************************************************
    *failure:
    * The toplevel failure continuation.
    ******************************************************************)
    let failure () =
      raise Failure
    in
    
    try
      let () = O.debug ("Pretactical: " ^ (Absyn.string_of_pretactical pretactical) ^ ".\n") in
      let tactical = buildTactical pretactical session in
      let () = O.debug ("Built tactical.\n") in
      let () = (applyTactical tactical session success failure) in
      session
    with
        Absyn.SyntaxError(s) ->
          (O.error (s ^ ".\n");
          session)
      | Success(s, pb) ->
          (O.output "Success.\n";
          if not (L.validSequent s) then
            (O.output ("Proved:\n" ^ (L.string_of_proofs (pb [])) ^ "\n");
            O.goal "";
            s)
          else
            s)
      | Failure ->
          (O.output "Failure.\n";
          session)

  (********************************************************************
  *makeTactical:
  ********************************************************************)
  let makeTactical name t session args =
    match args with
      [] -> fun sequents sc fc -> (t sequents sc fc)
    | _ -> fun _ _ fc -> (O.error (name ^ ": invalid arguments.\n"); fc ())

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
    ()
  
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
  * Loads the given logic.
  ********************************************************************)
  let loadLogic l =
    raise (Logic l)
    
  (********************************************************************
  *openFiles:
  * Open each file and read each command in it.
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
  *handleInput:
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
        | Absyn.Theorem(name, t) ->
            (L.prove name t session, true)
        | Absyn.Definitions(ds) ->
            (L.definitions ds session, true)
        | Absyn.Timing(onoff) ->
            (timing := onoff; (session, true))
        | Absyn.Debug(onoff) ->
            (O.showDebug := onoff; (session, true))
        | Absyn.Include(sl) ->
            (L.incl sl session, true)
        | Absyn.Open(sl) ->
            (openFiles session sl, true)
        | Absyn.Logics -> (showLogics session; (session, true))
        | Absyn.Logic(s) -> ((loadLogic s), true)
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
 
    let (session', save) = handle input session in
    if save then
      (storeSession session;
      session')
    else
      (session')

  let onPrompt session =
    (O.prompt ("[tac <" ^ (L.name) ^ ">]- ");
    session)

  let onStart () =
    (showStartup ();
    resetLists ();
    L.reset ())
  
  let onEnd session = ()

  let onInput session =
    try
      let input = Toplevel.parseStdinCommand () in
      let session' = handleInput input session in
      if L.validSequent session' then
        (O.goal ((L.string_of_sequents (L.sequents session')) ^ "\n");
        session')
      else
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
