(**********************************************************************
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
**********************************************************************)

(**********************************************************************
* Toplevel
***********************************************************************
* The interface to the ocamlyacc lexer and parser (see toplevellexer.mll,
* toplevelparser.mly).  The interface functions all provide methods for
* parsing input into abstract syntax commands (see absyn.mli).
**********************************************************************)
val parseStdinCommand : unit -> Absyn.command
val parseStdinCommandList : unit -> Absyn.command list
val parseChannelCommandList : in_channel -> Absyn.command list
