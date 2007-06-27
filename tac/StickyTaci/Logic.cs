/*****************************************************************************
* StickTaci                                                                  *
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
using System;
using System.Collections.Generic;
using System.Text;

namespace StickyTaci
{
  public class Logic : IComparable
  {
    private string m_Name = "";
    public string Name
    {
      get
      {
        return m_Name;
      }
      set
      {
        m_Name = value;
      }
    }

    private string m_Key = "";
    public string Key
    {
      get
      {
        return m_Key;
      }
      set
      {
        m_Key = value;
      }
    }

    public Logic(string key, string name)
    {
      Key = key;
      Name = name;
    }

    public int CompareTo(object o)
    {
      if(o is Logic)
      {
        Logic other = (Logic)o;
        return Key.CompareTo(other.Key);
      }
      return -1;
    }
  }
}
