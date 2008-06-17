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
* Listutils
***********************************************************************
* Simple functions operating on lists... I actually thought there would
* be more of them!
**********************************************************************)
val empty : 'a list -> bool
val split3 : ('a * 'b * 'c) list -> ('a list * 'b list * 'c list)
val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
val mapi : (int -> 'a) -> int -> 'a list
val split_nth : int -> 'a list -> ('a list * 'a list)
