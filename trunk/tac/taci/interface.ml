module Make (I : Interpreter.Interpreter) =
struct
  let interpret () =
    let rec interp session =
      try
        let _ = I.onPrompt session in
        let line = read_line () in
        let session' = I.onInput line session in
        (interp session')   
      with
        I.Exit(session) ->
          session
  in
    let session = I.onStart () in
    let session' = (interp session) in
    (I.onEnd session')
end
