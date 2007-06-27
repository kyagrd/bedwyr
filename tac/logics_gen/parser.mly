/*****************************************************************************
* Logics_gen                                                                 *
* Copyright (C) 2007 Zach Snow                                               *
*                                                                            *
* This program is free software; you can redistribute it and/or modify       *
* it under the terms of the GNU General Public License as published by       *
* the Free Software Foundation; either version 2 of the License, or          *
* (at your option) any later version.                                        *
*                                                                            *
* This program is distributed in the hope that it will be useful,            *
* but WITHOUT ANY WARRANTY; without even the implied warranty of             *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *
* GNU General Public License for more details.                               *
*                                                                            *
* You should have received a copy of the GNU General Public License          *
* along with this code; if not, write to the Free Software Foundation,       *
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA               *
*****************************************************************************/
%{
  let addOutput output (outputs, logics) = (output::outputs, logics)
  let addLogic logic (outputs, logics) = (outputs, logic::logics)
%}

%token LOGIC OUTPUT LPAREN RPAREN COMMA SEMICOLON EOF
%token <string> ID

%start toplevel_file
%type <Absyn.output list * Absyn.logic list> toplevel_file
%%

toplevel_file:
  | file      {$1}
  | file EOF  {$1}
  ;

file:
  | output file {addOutput $1 $2}
  | logic file  {addLogic $1 $2}
  | output      {addOutput $1 ([],[])}
  | logic       {addLogic $1 ([],[])}
  ;


output
  : OUTPUT LPAREN ID COMMA ID RPAREN SEMICOLON {Absyn.Output($3, $5)}
  ;

logic
  : LOGIC LPAREN ID COMMA ID RPAREN SEMICOLON  {Absyn.Logic($3, $5)}
  ;

%%
