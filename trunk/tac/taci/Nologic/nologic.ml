(**********************************************************************
*NoLogic:
* A dummy logic module.
**********************************************************************)
module Nologic =
struct
  let name = "No Logic"
  let info =
"
No Logic v0.0

No logic does nothing!
"

  let start = info
  type session = unit
  
  let incl files session =
    (print_endline (String.concat ", " files))

  let tacticals = Logic.Table.empty

  let reset () = ()
  let prove name s session =
    (print_endline ("No Logic can't prove '" ^ name ^ "': " ^ s ^ ".");
    session)
  let definition d session = session
  let operator name fix prec session =
    session

  type sequent = unit
  let validSequent session = true
  let sequent session = Some((), ())
  let sequents session = []
  let string_of_sequents sequents = "()"
  let updateSequents sequents session = ()
  
  type proof = unit
  let string_of_proofs proofs = "proofs: ()"
end
