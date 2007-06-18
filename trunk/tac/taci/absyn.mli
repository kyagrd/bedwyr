(**********************************************************************
*Absyn:
* Represents the abstract syntax parsed at the top level.  The top level
* parser (module Toplevelparser) assumes that any quoted string is
* "opaque" and will be later parsed by a particular logic's parser.
* A logic should not need to reference this module.
**********************************************************************)
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
  | Open of string list
  | Include of string list
  | Help
  | Clear
  | Undo of int
  | Redo of int
  
  | Theorem of string * string
  | Definitions of string list

  | Tacticals
  | TacticalDefinition of string * pretactical
  
  | PreTactical of pretactical
  
  | Timing of bool
  | Debug of bool
  
  | Logic of string  
  | Logics

  | NoCommand
  
val string_of_pretactical : pretactical -> string
  