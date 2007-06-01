exception SyntaxError of string

type pretactical =
    ApplicationPreTactical of string * pretactical list
  | StringPreTactical of string

type 'a tactical =
    Tactical of 'a
  | String of string

type command =
    Exit
  | Reset
  | Include of string list
  | Help
  | Clear
  | Undo of int
  | Redo of int
  
  | Theorem of string * string
  | Definition of string
  | PreTactical of pretactical
  | Timing of bool
  | Debug of bool
  
  | NoCommand

let rec string_of_pretactical tac =
  match tac with
      ApplicationPreTactical(name, []) ->
        name
    | ApplicationPreTactical(name, args) ->
        name ^ "(" ^ (String.concat ", " (List.map string_of_pretactical args)) ^ ")"
    | StringPreTactical(s) -> "\"" ^ s ^ "\""