module type Interface =
sig
  val interpret : unit -> unit
end

module Make (I : Interpreter.Interpreter) =
struct
  let interpret () =
    let rec interp session =
      try
        let session' = I.onPrompt session in
        let session'' = I.onInput session' in
        (interp session'')   
      with
        I.Exit(session) ->
          session
  in
    let session = I.onStart () in
    let session' = (interp session) in
    (I.onEnd session')
end
