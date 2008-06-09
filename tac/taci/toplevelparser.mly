/**********************************************************************
* Taci                                                                *
* Copyright (C) 2007 Zach Snow, David Baelde                          *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************/

/**********************************************************************
* Toplevelparser
***********************************************************************
* This is the ocamlyacc specification for the toplevel parser.  The
* parser is straightforward, the only thing to note being that it handles
* the end of file token explicitly.  All access to the generated parser
* is done through the Toplevel module (see toplevel.mli).
**********************************************************************/
%{
%}

%token DOT SHARP LPAREN RPAREN COMMA
%token HELP EXIT RESET OPEN INCLUDE TIME DEBUG PROOF_OUTPUT
%token ON OFF CLEAR THEOREM SET
%token TACTICAL TACTICALS LOGIC LOGICS
%token DEFINE UNDO REDO
%token EOF
%token <string> ID STRING

%start toplevel_command toplevel_file
%type <Absyn.command list> toplevel_file
%type <Absyn.command> toplevel_command
%%

toplevel_file:
  | file  {$1}
  ;

file:
  | SHARP command DOT file   {$2 ::  $4}
  | tactical DOT file        {Absyn.PreTactical($1) :: $3}
  | EOF                      {[]}
  ;

toplevel_command
  : SHARP command DOT   {$2}
  | tactical DOT        {Absyn.PreTactical($1)}
  ;

tactical
  : ID                              {Absyn.ApplicationPreTactical($1, [])}
  | ID LPAREN tactical_list RPAREN  {Absyn.ApplicationPreTactical($1, $3)}
  | STRING                          {Absyn.StringPreTactical($1)}
  | LPAREN tactical RPAREN          {$2}
  ;

tactical_list
  : tactical COMMA tactical_list  {$1::$3}
  | tactical                      {$1::[]}
  ;

command
  : EXIT                {Absyn.Exit}
  | RESET               {Absyn.Reset}
  | OPEN stringlist     {Absyn.Open $2}
  | INCLUDE stringlist  {Absyn.Include $2}
  | PROOF_OUTPUT STRING {Absyn.ProofOutput $2}
  
  | CLEAR       {Absyn.Clear}
  
  | UNDO        {Absyn.Undo(1)}
  | REDO        {Absyn.Redo(1)}
  
  | DEBUG onoff {Absyn.Debug($2)}
  | TIME onoff  {Absyn.Timing($2)}
  
  | HELP                  {Absyn.Help}
  | THEOREM ID STRING     {Absyn.Theorem($2, $3)}
  | DEFINE stringlist {Absyn.Definitions($2)}
  
  | TACTICALS             {Absyn.Tacticals}
  | TACTICAL ID tactical  {Absyn.TacticalDefinition($2, $3)}
  
  | LOGIC STRING          {Absyn.Logic($2)}
  | LOGICS                {Absyn.Logics}
  
  | SET STRING STRING     {Absyn.Set($2,$3)}
  ;

stringlist
  : STRING stringlist {$1 :: $2}
  | STRING            {[$1]}
  ;

onoff:
  | ON  {true}
  | OFF {false}
  ;

%%
