(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
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
* Firstorder
***********************************************************************
* This module defines 4 different first order logics.  Each logic
* has equality, and definitions in the form of fixed point combinators.
**********************************************************************)

module Firstordernonstrict : functor (O : Output.Output) -> Logic.Logic
module Firstorderstrict    : functor (O : Output.Output) -> Logic.Logic
module MuLJstrict          : functor (O : Output.Output) -> Logic.Logic
module MuLJnonstrict       : functor (O : Output.Output) -> Logic.Logic
