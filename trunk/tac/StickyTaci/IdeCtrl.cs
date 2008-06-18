/*****************************************************************************
* StickyTaci                                                                 *
* Copyright (C) 2007 - 2008 Zach Snow                                        *
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

    public string ApplicationPath
    {
      get
      {
        return Path.GetDirectoryName(Application.ExecutablePath);
      }
    }

    public string CurrentLogic
    {
      get
      {
        return Taci.CurrentLogic;
      }
      set
      {
        Taci.CurrentLogic = value;
      }
    }

    private List<Logic> m_Logics = new List<Logic>();
    private List<string> m_Tacticals = new List<string>();

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

    public int CurrentLine
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
      if(Taci == null)
      {
        m_Taci = new Taci(path, "--output xml --logic " + logic);
        CurrentLogic = logic;

        Taci.Output += new Taci.IOHandler<string>(Taci_Output);
        Taci.Goal += new Taci.IOHandler<string>(Taci_Goal);
        Taci.Error += new Taci.IOHandler<string>(Taci_Error);
        Taci.Debug += new Taci.IOHandler<string>(Taci_Debug);
        Taci.Warning += new Taci.IOHandler<string>(Taci_Warning);
        Taci.Command += new Taci.IOHandler<string>(Taci_Command);
        Taci.Tactical += new Taci.IOHandler<string>(Taci_Tactical);
        Taci.Logic += new Taci.IOHandler<Logic>(Taci_Logic);
        Taci.Exit += new Taci.ExitHandler(Taci_Exit);
        Taci.Restart();

        
        UpdateInfo();

        Form.Commands = Taci.Commands;
      }
    }

    private void UpdateInfo()
    {
      //Get information.  Yeah, this is dumb.
      //TODO: Fix Taci parser to leave unparsed input in the lexbuf.
      System.Threading.Thread.Sleep(100);
      Taci.Write(Taci.LOGICS + ".");
      System.Threading.Thread.Sleep(100);
      Taci.Write(Taci.TACTICALS + ".");
      System.Threading.Thread.Sleep(100);
      Taci.Write(Taci.CLEAR + ".");
      System.Threading.Thread.Sleep(100);
      Taci.Write(Taci.HELP + ".");
    }

    void Taci_Logic(Taci instance, Logic data)
    {
      if(instance == Taci)
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
      if(instance == Taci)
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
      Form.ClearOutput();
      Form.ClearGoal();
      Taci.Write(Taci.RESET + ".");
    }

    public void OnTacRestart()
    {
      Form.CurrentLine = 0;
      Taci.Restart();
    }

    public void OnShown()
    {
      StartTaci(Path.Combine(ApplicationPath, "taci.exe"), "muLJ");
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
      FileName = filename;
      Form.SaveFile(filename);
      
    }

    public void OnNew()
    {
      if((Form.Dirty && SaveMessage()) || !Form.Dirty)
      {
        FileName = "";
        Form.Clear();
        OnTacReset();
      }
    }

    public void OnExit()
    {
      if((Form.Dirty && SaveMessage()) || !Form.Dirty)
      {
        Taci.Shutdown();
      }
    }

    public void Taci_Exit(object instance)
    {
      if(instance == Taci)
      {
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
        string path = dlg.FileName;
        if(GetLogicName(dlg.FileName) == "")
        {
          path = Path.ChangeExtension(dlg.FileName, "." + CurrentLogic + ".tac");
        }
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
      if((Form.Dirty && SaveMessage()) || !Form.Dirty)
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
        string logic = GetLogicName(dlg.FileName);
        if(logic != "")
        {
          OnLogic(logic);
        }
        else
        {
          MessageBox.Show("Unable to load session logic: logic not specified.", "StickyTaci - Warning", MessageBoxButtons.OK, MessageBoxIcon.Warning);
        }
        Form.LoadFile(dlg.FileName);
        FileName = dlg.FileName;
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
      Taci.Restart();
      UpdateInfo();
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

    public void OnInputChanged(int numlines)
    {
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
      OnAll((int)Form.Scintilla.Lines.Count);
    }

    public void OnPreviousLine()
    {
      string line = "";
      if(Form.GetPreviousLine(ref line))
      {
        line = line.Trim();

        //Count number of periods before the first %.
        int count = 0;
        for(int i = 0; i < line.Length; i++)
        {
          if(line[i] == '.')
            count++;
          else if(line[i] == '%')
            break;
        }

        //Undo many periods.
        for(int i = 0; i < count; i++)
        {
          Taci.Write(Taci.UNDO + ".");
        }
        return;
      };
    }

    public void OnAll(int line)
    {
      //Run each line upto the given one.
      int i = 0;
      int maxIterations = Form.Scintilla.Lines.Count + 1;
      while(CurrentLine < line && i < maxIterations)
      {
        OnNextLine();
        i++;
      }
    }

    private void Taci_Output(Taci instance, string data)
    {
      Form.Output(data);
    }


    void Taci_Debug(Taci instance, string data)
    {
      Form.Debug(data);
    }

    void Taci_Warning(Taci instance, string data)
    {
      Form.Warning(data);
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
        Form.ClearOutput();
      else if(data == "begin-computation")
        Form.Computing = true;
      else if(data == "end-computation")
        Form.Computing = false;
    }

    private string GetLogicName(string path)
    {
      string ext = Path.GetExtension(path);
      if(ext == ".tac")
      {
        string name = Path.GetFileNameWithoutExtension(path);        
        ext = Path.GetExtension(name);
        if(ext.Length > 0)
          return ext.Substring(1);
        else
          return "";
      }
      return "";
    }
  }
}
