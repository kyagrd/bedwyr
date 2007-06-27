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
using System.IO;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;

namespace StickyTaci
{
  public class IdeCtrl
  {
    private string m_Line = "";

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
      }
    }

    private List<Logic> m_Logics = new List<Logic>();
    private List<string> m_Tacticals = new List<string>();
    private bool m_Dirty = false;
    public bool Dirty
    {
      get
      {
        return m_Dirty;
      }
      set
      {
        m_Dirty = value;
      }
    }

    private string m_FileName = "";
    public string FileName
    {
      get
      {
        return m_FileName;
      }
      set
      {
        m_FileName = value;
      }
    }

    public uint CurrentLine
    {
      get
      {
        return Form.CurrentLine;
      }
      set
      {
        Form.CurrentLine = value;
      }
    }

    private IdeForm m_Form = null;
    public IdeForm Form
    {
      get
      {
        return m_Form;
      }
      set
      {
        m_Form = value;
      }
    }

    private Taci m_Taci = null;
    public Taci Taci
    {
      get
      {
        return m_Taci;
      }
    }

    public void StartTaci(string path, string logic)
    {
      m_Taci = new Taci(path, "--output xml --logic " + logic);
      m_Taci.Output += new Taci.IOHandler<string>(Taci_Output);
      m_Taci.Goal += new Taci.IOHandler<string>(Taci_Goal);
      m_Taci.Error += new Taci.IOHandler<string>(Taci_Error);
      m_Taci.Command += new Taci.IOHandler<string>(Taci_Command);
      m_Taci.Tactical += new Taci.IOHandler<string>(Taci_Tactical);
      m_Taci.Logic += new Taci.IOHandler<Logic>(Taci_Logic);
      m_Taci.Restart();

      CurrentLogic = logic;

      //Get information.  Yeah, this is dumb.
      //TODO: Fix Taci parser to leave unparsed input
      //      in the lexbuf.
      m_Taci.Write(Taci.LOGICS + ".");
      System.Threading.Thread.Sleep(100);
      m_Taci.Write(Taci.TACTICALS + ".");
      System.Threading.Thread.Sleep(100);
      m_Taci.Write(Taci.CLEAR + ".");
      System.Threading.Thread.Sleep(100);
      m_Taci.Write(Taci.HELP + ".");

      Form.Commands = m_Taci.Commands;
    }

    void Taci_Logic(Taci instance, Logic data)
    {
      if(instance == m_Taci)
      {
        if(!m_Logics.Contains(data))
        {
          m_Logics.Add(data);
          m_Logics.Sort();
          Form.Logics = m_Logics;
        }
      }
    }

    void Taci_Tactical(Taci instance, string data)
    {
      if(instance == m_Taci)
      {
        if(!m_Tacticals.Contains(data))
        {
          m_Tacticals.Add(data);
          m_Tacticals.Sort();
          Form.Tacticals = m_Tacticals;
        }
      }
    }

    public void OnTacInclude()
    {
      //Get a list of files.
      OpenFileDialog dlg = new OpenFileDialog();
      dlg.Filter = "All Files (*.*)|*.*";
      dlg.RestoreDirectory = true;
      dlg.Multiselect = true;

      if(dlg.ShowDialog() == DialogResult.OK)
      {
        //Open them:
        string command = Taci.INCLUDE;
        foreach(string filename in dlg.FileNames)
        {
          command += " \"" + filename + "\"";
        }
        command += ".";
        Taci.Write(command);
      }
    }

    public void OnTacOpen()
    {
      //Get a list of files.
      OpenFileDialog dlg = new OpenFileDialog();
      dlg.Filter = "All Files (*.*)|*.*";
      dlg.RestoreDirectory = true;
      dlg.Multiselect = true;

      if(dlg.ShowDialog() == DialogResult.OK)
      {
        //Open them:
        string command = Taci.OPEN;
        foreach(string filename in dlg.FileNames)
        {
          command += " \"" + filename + "\"";
        }
        command += ".\n";
        Form.Input(command);
      }
    }

    public void OnTacReset()
    {
      Form.CurrentLine = 0;
      Taci.Write(Taci.RESET + ".");
    }

    public void OnTacRestart()
    {
      Form.CurrentLine = 0;
      Taci.Restart();
    }

    public void OnShown()
    {
      StartTaci(Application.StartupPath + "/taci.exe", "firstorder");
    }

    private bool SaveMessage()
    {
      string text = "The current file has changed.\nDo you want to save the changes?";
      DialogResult result = MessageBox.Show(text, "StickyTaci", MessageBoxButtons.YesNoCancel, MessageBoxIcon.Exclamation);
      if(result == DialogResult.Yes)
      {
        return OnSave();
      }
      else if(result == DialogResult.No)
      {
        return true;
      }
      else
      {
        return false;
      }
    }

    private void Save(string filename)
    {
      Form.Rtf.SaveFile(filename, RichTextBoxStreamType.PlainText);
      Dirty = false;
    }

    public void OnNew()
    {
      if((Dirty && SaveMessage()) || !Dirty)
      {
        FileName = "";
        Form.Clear();
        OnTacReset();
        Dirty = false;
      }
    }

    public void OnExit()
    {
      if((Dirty && SaveMessage()) || !Dirty)
      {
        Taci.Write(Taci.EXIT + ".");
        Taci.Exit();
        Form.Close();
      }
    }

    public bool OnSave()
    {
      if(FileName == "")
      {
        return OnSaveAs();
      }
      else
      {
        Save(FileName);
        return true;
      }
    }

    public bool OnSaveAs()
    {
      SaveFileDialog dlg = new SaveFileDialog();
      dlg.Filter = "StickyTaci Session (*.tac)|*.tac";
      dlg.RestoreDirectory = true;

      if(dlg.ShowDialog() == DialogResult.OK)
      {
        string path = Path.ChangeExtension(dlg.FileName, "." + CurrentLogic + ".tac");
        Save(path);
        return true;
      }
      else
      {
        return false;
      }
    }

    public void OnOpen()
    {
      if((Dirty && SaveMessage()) || !Dirty)
      {
        Open();
      }
    }

    private void Open()
    {
      OpenFileDialog dlg = new OpenFileDialog();
      dlg.Filter = "StickyTaci Session (*.tac)|*.tac|All Files (*.*)|*.*";

      if(dlg.ShowDialog() == DialogResult.OK)
      {
        OnTacReset();
        Form.Clear();

        //Get the logic name:
        string ext = Path.GetExtension(dlg.FileName);
        if(ext == ".tac")
        {
          string name = Path.GetFileNameWithoutExtension(dlg.FileName);
          ext = Path.GetExtension(name);
          if(ext != "")
          {
            string logic = ext.Substring(1);
            OnLogic(logic);
          }
        }
        Form.Rtf.LoadFile(dlg.FileName, RichTextBoxStreamType.PlainText);
        FileName = dlg.FileName;
        Form.ColorLines((uint)Form.Rtf.Lines.Length);

        Dirty = false;
      }
    }

    public void OnHelpTaci()
    {
      Taci.Write(Taci.HELP + ".");
    }

    public void OnHelp()
    {
      AboutDlg dlg = new AboutDlg();
      dlg.ShowDialog();
    }

    public void OnTacClear()
    {
      Taci.Write(Taci.CLEAR + ".");
    }

    public void OnTactical(string tac)
    {
      Form.Input(tac);
    }

    public void OnLogic(string name)
    {
      CurrentLogic = name;
      Taci.Write(Taci.LOGIC + " " + name + ".");
      OnTacReset();
    }
    public void OnLogic(Logic l)
    {
      OnLogic(l.Key);
    }

    public bool OnNextLine()
    {
      string line = "";
      if(Form.GetNextLine(ref line))
      {        
        line = line.Trim();
        
        if(line != "" && line[0] != '%')
          m_Line += line;

        if(m_Line == "" || m_Line[m_Line.Length - 1] != '.')
        {
          return false;
        }
        else
        {
          Taci.Write(m_Line);
          m_Line = "";
        }
        return true;
      }
      return false;
    }

    public void OnInputChanged(uint numlines)
    {
      Dirty = true;
      if(CurrentLine >= numlines)
      {
        if(numlines > 0)
          CurrentLine = numlines - 1;
        else
          CurrentLine = 0;
      }
    }

    public void OnStart()
    {
      OnTacReset();
    }

    public void OnEnd()
    {
      OnAll((uint)Form.Rtf.Lines.Length);
    }

    public void OnPreviousLine()
    {
      string line = "";
      if(Form.GetPreviousLine(ref line))
      {
        line = line.Trim();
        if(line == "" || line[0] == '%' || line[line.Length - 1] != '.')
        {
          return;
        }
        Taci.Write(Taci.UNDO + ".");
        return;
      };
    }

    public void OnAll(uint line)
    {
      //Reset the environment so everything works as planned.
      OnTacReset();

      //Run each line upto the given one.
      while(CurrentLine < line)
      {
        OnNextLine();
      }
    }

    private void Taci_Output(Taci instance, string data)
    {
      Form.Output(data);
    }

    private void Taci_Error(Taci instance, string data)
    {
      Form.Error(data);
    }

    private void Taci_Goal(Taci instance, string data)
    {
      Form.Goal(data);
    }

    private void Taci_Command(Taci instance, string data)
    {
      if(data == "clear")
      {
        Form.ClearOutput();
      }
    }
  }
}
