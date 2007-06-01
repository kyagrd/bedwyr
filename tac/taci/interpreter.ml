module type Interpreter =
sig
  type session
  exception Exit of session

  val onStart : unit -> session
  val onEnd : session -> unit  
  val onPrompt : session -> session
  val onInput : string -> session -> session 
end

module Make (O : Output.Output) (L : Logic.Logic) =
struct
  type session = L.session
  exception Exit of session
  exception Success of session
  
  let timing = ref false
  let debug = ref false
  
  let findTactical name session =
    try
      let tactical = Logic.Table.find name L.tacticals in
      Some tactical
    with
      Not_found -> None
  
  let applyTactical tactical session sc =
    match tactical with
        Absyn.Tactical(tac) ->
          let so = L.sequent session in
          if Option.isSome so then
            let (sequent, session') = Option.get so in
            (tac sequent (sc session'))
          else
            ()
      | Absyn.String(_) -> failwith "invalid quoted string"
    
  let helpMessage =
"
Taci v0.0

#clear.                     : Clear the screen.
#debug <on | off>.          : Turn debugging on or off.
#definition <definition>.   : Add the given definition to the current session.
#exit.                      : Exit Taci.
#help.                      : Show this message.
#include <files>            : Add the definitions in the given files to the
                              current session.  File names should be surrounded
                              by quotes and separated by spaces.
#theorem <name> <theorem>.  : Prove the given theorem in the current logic.
#reset.                     : Reset the current session.
#time <on | off>.           : Turn timing on or off.
"

  let startupMessage = "Welcome to " ^ helpMessage
  let showHelp () =
    (O.output helpMessage;
    O.output L.info)

  let showStartup () =
    (O.output startupMessage;
    O.output L.start)

  (********************************************************************
  *Undo/Redo:
  ********************************************************************)
  let undoList = ref []
  let redoList = ref []
  let resetLists () =
    (undoList := []; redoList := [])

  let undo session =
    if (List.length (!undoList) > 0) then
      let session' = List.hd (!undoList) in
      (redoList := session :: (!redoList);
      undoList := List.tl (!undoList);
      session')
    else
      (O.error "nothing do undo.\n";
      session)

  let redo session =
    if (List.length (!redoList) > 0) then
      let session' = List.hd (!redoList) in
      (undoList := session :: (!undoList);
      redoList := List.tl (!redoList);
      session')
    else
      (O.error "nothing do redo.\n";
      session)
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
            Absyn.Tactical(t (List.map buildArg args))
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
    *sc:
    * The toplevel success continuation.
    ******************************************************************)
    let sc session sequents =
      let currentSequents = L.sequents session in
      let newSequents = (sequents @ currentSequents) in
      let session' = L.updateSequents newSequents session in
      raise (Success session')
    in
    
    try
      let () = O.debug ("Pretactical: " ^ (Absyn.string_of_pretactical pretactical) ^ ".\n") in

      let tactical = buildTactical pretactical session in
      let () = (applyTactical tactical session sc) in
      (O.output "Failure.\n";
      session)
    with
        Absyn.SyntaxError(s) ->
          (O.error (s ^ ".\n");
          session)
      | Success(session) ->
          (O.output "Success.\n";
          if not (L.validSequent session) then
            (O.output "Proved.\n";
            session)
          else
          session)

  (********************************************************************
  *handleInput:
  ********************************************************************)
  let handleInput input session =
    match input with
        Absyn.Exit -> raise (Exit session)
      | Absyn.Clear -> (O.clear (); session)
      | Absyn.Help -> (showHelp (); session)
      | Absyn.Undo(_) -> (undo session)
      | Absyn.Redo(_) -> (redo session)
      | Absyn.Reset -> (resetLists (); L.reset ())
      | Absyn.Theorem(name, t) ->
          (resetLists ();
          L.prove name t session)
      | Absyn.Definition(d) ->
          (L.definition d session)
      | Absyn.Timing(onoff) ->
          (timing := onoff; session)
      | Absyn.Debug(onoff) ->
          (debug := onoff; session)
      | Absyn.Include(sl) ->
          (L.incl sl session)
      | Absyn.PreTactical(pretactical) ->
          if (L.validSequent session) then
            (redoList := [];
            undoList := session :: (!undoList);
            tactical pretactical session)
          else
            (O.error "No valid sequent.\n";
            session)
      | Absyn.NoCommand -> session

  let onPrompt session =
    (O.prompt ("[tac <" ^ (L.name) ^ ">]- ");
    session)

  let onStart () =
    (showStartup ();
    resetLists ();
    L.reset ())
  
  let onEnd session = ()

  let onInput s session =
    try
      let input = Toplevel.parseStringCommand s in      
      let session' = handleInput input session in
      if L.validSequent session' then
        (O.output ((L.string_of_sequents session') ^ "\n");
        session')
      else
        session'
    with
        Absyn.SyntaxError(s) -> (O.error (s ^ ".\n"); session)
end
