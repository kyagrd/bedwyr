exception SyntaxError of string

type command =
    Help
  | Clear
  | Include of (string list)
  | Reset
  | Debug of bool
  | Timing of bool
  | Theorem of (string * string)
  | Definition of string
  | Exit
  | Tactical of (string * string)
  | NoCommand