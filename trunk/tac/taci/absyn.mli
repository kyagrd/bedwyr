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
  
val string_of_pretactical : pretactical -> string
  