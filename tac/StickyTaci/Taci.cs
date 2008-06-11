/*****************************************************************************
* StickyTaci                                                                 *
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
using System.Diagnostics;
using System.Xml;

namespace StickyTaci
{
  public class Taci
  {
    private List<string> m_Commands = new List<string>();
    public List<string> Commands
    {
      get
      {
        return m_Commands;
      }
      set
      {
        m_Commands = value;
      }
    }
    public static string CLEAR = "#clear";
    public static string EXIT = "#exit";
    public static string HELP = "#help";
    public static string INCLUDE = "#include";
    public static string LOGIC = "#logic";
    public static string LOGICS = "#logics";
    public static string OPEN = "#open";
    public static string REDO = "#redo";
    public static string RESET = "#reset";
    public static string TACTICALS = "#tacticals";
    public static string UNDO = "#undo";
    public static string PROOF_OUTPUT = "#proof_output";
    
    public delegate void IOHandler<T>(Taci instance, T data);
    public delegate void ExitHandler(Taci instance);
    public event ExitHandler Exit;
    public event IOHandler<string> Output;
    public event IOHandler<string> Goal;
    public event IOHandler<string> Debug;
    public event IOHandler<string> Warning;
    public event IOHandler<string> Error;
    public event IOHandler<string> Command;
    public event IOHandler<string> Tactical;
    public event IOHandler<Logic> Logic;

    private bool m_Exiting = false;
    public bool Exiting
    {
      get
      {
        return m_Exiting;
      }
      set
      {
        m_Exiting = value;
      }
    }

    private Process m_Taci = null;
    private string m_Data;
    private string m_Path;
    private string m_Arguments;
    private string m_CurrentLogic = "";
    public string CurrentLogic
    {
      get
      {
        return m_CurrentLogic;
      }
      set
      {
        m_CurrentLogic = value;
        m_Arguments = " --logic " + value + " --output xml";
      }
    }
    
    public Taci(string path, string logic)
    {
      m_Path = path;
      CurrentLogic = logic;
      System.Diagnostics.Debug.WriteLine("Executing '" + path + m_Arguments + "'.");

      m_Commands.Add("#clear");
      m_Commands.Add("#debug");
      m_Commands.Add("#define");
      m_Commands.Add("#help");
      m_Commands.Add("#logic");
      m_Commands.Add("#logics");
      m_Commands.Add("#open");
      m_Commands.Add("#proof_output");
      m_Commands.Add("#redo");
      m_Commands.Add("#reset");
      m_Commands.Add("#tactical");
      m_Commands.Add("#tacticals");
      m_Commands.Add("#theorem");
      m_Commands.Add("#timing");
      m_Commands.Add("#undo");
    }

    public void Restart()
    {
      if(m_Taci != null)
      {
        m_Taci.Kill();
        m_Taci.Close();
      }

      ProcessStartInfo si = new ProcessStartInfo(m_Path, m_Arguments);
      si.UseShellExecute = false;
      si.RedirectStandardInput = true;
      si.RedirectStandardOutput = true;

      m_Taci = new Process();
      m_Taci.StartInfo = si;
      m_Taci.OutputDataReceived += new DataReceivedEventHandler(Taci_OutputDataReceived);
      m_Taci.Exited += new EventHandler(Taci_Exited);
      m_Taci.EnableRaisingEvents = true;

      if(m_Taci.Start())
      {
        m_Taci.BeginOutputReadLine();
      }
      return;
    }

   
    public void Write(string s)
    {
      System.Diagnostics.Debug.WriteLine("Taci: " + s);
      m_Taci.StandardInput.WriteLine(s + "\n");
    }

    public void Shutdown()
    {
      Exiting = true;
      Write(Taci.EXIT + ".");
      return;
    }


    private void Taci_Exited(object sender, EventArgs e)
    {
      if(sender == m_Taci)
      {
        m_Taci.Close();
        m_Taci = null;

        if(Exiting)
        {
          if(Exit != null)
          {
            Exit(this);
          }
        }
        else
        {
          Restart();
        }
      }
    }

    private void ProcessOutput()
    {
      try
      {
        XmlDocument doc = new XmlDocument();
        doc.LoadXml("<xml>" + m_Data + "</xml>");
        ParseOutput(doc);
        m_Data = "";
      }
      catch(XmlException)
      {
        System.Diagnostics.Debug.WriteLine("Unable to parse: " + m_Data);
        return;
      }
    }
    private void Taci_OutputDataReceived(object sender, DataReceivedEventArgs e)
    {
      m_Data += e.Data;
      ProcessOutput();
    }

    private void ParseOutput(XmlDocument doc)
    {
      XmlNodeList outputs = doc.GetElementsByTagName("Output");
      if(outputs.Count == 0)
      {
        System.Diagnostics.Debug.WriteLine("No <Output> nodes.");
        return;
      }

      foreach(XmlNode output in outputs)
      {
        XmlAttribute type = output.Attributes["type"];
        if(type != null)
        {
          Notify(type.Value, output);
        }
        else
        {
          System.Diagnostics.Debug.WriteLine("Invalid <Output> node.");
        }
      }
    }

    private string Unescape(string s)
    {
      s = s.Replace("&lt;", "<");
      s = s.Replace("&gt;", ">");
      s = s.Replace("&amp;", "&");
      s = s.Replace("&quot;", "\"");
      s = s.Replace("&apos;", "'");
      s = s.Replace("\\n", "\n");
      s = s.Replace("\\\\", "\\");
      
      return s;
    }

    private void Notify(string type, XmlNode node)
    {
      if(type == "output" && Output != null)
      {
        string text = GetAttribute(node, "text");
        Output(this, text);
      }
      else if(type == "goal" && Goal != null)
      {
        string text = GetAttribute(node, "text");
        Goal(this, text);
      }
      else if(type == "error" && Error != null)
      {
        string text = GetAttribute(node, "text");
        Error(this, text);
      }
      else if(type == "command" && Command != null)
      {
        string text = GetAttribute(node, "text");
        Command(this, text);
      }
      else if(type == "tactical" && Tactical != null)
      {
        string text = GetAttribute(node, "text");
        System.Diagnostics.Debug.WriteLine("Tactical: " + text + ".");
        Tactical(this, text);
      }
      else if(type == "logic" && Logic != null)
      {
        string key = GetAttribute(node, "key");
        string name = GetAttribute(node, "name");
        System.Diagnostics.Debug.WriteLine("Logic: " + key + " : " + name + ".");
        Logic(this, new Logic(key, name));
      }
      else if(type == "warning" && Warning != null)
      {
        string text = GetAttribute(node, "text");
        Warning(this, text);
      }
      else if(type == "debug" && Debug != null)
      {
        string text = GetAttribute(node, "text");
        Debug(this, text);
      }
    }

    string GetAttribute(XmlNode node, string name)
    {
      XmlAttribute attr = node.Attributes[name];
      if(attr != null)
      {
        return Unescape(attr.Value);
      }
      return "";
    }
  }
}
