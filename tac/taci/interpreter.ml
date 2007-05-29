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
  
  let applyTactical tactical parameters session sc =
    let tactical' = (tactical parameters) in
    let sequent = List.hd (L.sequents session) in
    (tactical' sequent sc)
  

    
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

  type interpretermode =
      TopLevelMode
    | LogicMode

  (********************************************************************
  *tactical:
  * Attempts to apply the named tactical.
  ********************************************************************)
  let tactical name params session =
    (******************************************************************
    *sc:
    * The toplevel success continuation.
    ******************************************************************)
    let sc sequents =
      let currentSequents = L.sequents session in
      let newSequents = (sequents @ List.tl currentSequents) in
      let session' = L.updateSequents newSequents session in
      raise (Success session')
    in
    
    (try
      let tacticalop = findTactical name session in
      if (Option.isSome tacticalop) then
        let tactical = Option.get tacticalop in
        let () = (applyTactical tactical params session sc) in
        (O.output "Failure.";
        session)
      else
        (O.error ("Undefined tactical: " ^ name ^ ".\n");
        session)
    with
      Success(session) ->
        (O.output "Success.";
        session))

  (********************************************************************
  *handleInput:
  ********************************************************************)
  let handleInput input session =
    match input with
        Command.Exit -> raise (Exit session)
      | Command.Clear -> (O.clear (); session)
      | Command.Help -> (showHelp (); session)
      | Command.Reset -> (L.reset ())
      | Command.Theorem(name, t) ->
          (L.prove name t session)
      | Command.Definition(d) ->
          (L.definition d session)
      | Command.Timing(onoff) ->
          (timing := onoff; session)
      | Command.Debug(onoff) ->
          (debug := onoff; session)
      | Command.Include(sl) ->
          (L.incl sl session)
      | Command.Tactical(name, params) ->
          (tactical name params session)
      | Command.NoCommand -> session

  let onPrompt session =
    (O.output ("[tac <" ^ (L.name) ^ ">]- ");
    session)

  let onStart () =
    (showStartup ();
    L.reset ())
  
  let onEnd session = ()

  let onInput s session =
    try
      let input = Toplevel.parseStringCommand s in
      (handleInput input session)
    with
        Command.SyntaxError(s) -> (O.error (s ^ ".\n"); session)
end
