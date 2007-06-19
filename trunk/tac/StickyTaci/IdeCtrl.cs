using System;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;

namespace StickyTaci
{
  public class IdeCtrl
  {
    private string m_Line = "";

    List<string> m_Tacticals = new List<string>();
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

    public IdeCtrl()
    {
    }

    public void StartTaci(string path, string arguments)
    {
      m_Taci = new Taci(path, arguments);
      m_Taci.Output += new Taci.IOHandler(Taci_Output);
      m_Taci.Goal += new Taci.IOHandler(Taci_Goal);
      m_Taci.Error += new Taci.IOHandler(Taci_Error);
      m_Taci.Command += new Taci.IOHandler(Taci_Command);
      m_Taci.Tactical += new Taci.IOHandler(Taci_Tactical);
      m_Taci.Restart();

      //Get information.
      m_Taci.Write(Taci.TACTICALS + ".");
      m_Taci.Write(Taci.CLEAR + ".");
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
      dlg.Filter = "Taci Files (*.tac)|*.t|All Files (*.*)|*.*";
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
      Taci.Write(Taci.RESET + ".");
    }

    public void OnTacRestart()
    {
      Taci.Restart();
    }

    private bool SaveMessage()
    {
      string text = "The current file has changed.\nDo you want to save the changes?";
      DialogResult result = MessageBox.Show(text, "StickyTaci", MessageBoxButtons.YesNoCancel);
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
      Dirty = false;
      Form.Rtf.SaveFile(filename, RichTextBoxStreamType.PlainText);
    }

    public void OnNew()
    {
      if((Dirty && SaveMessage()) || !Dirty)
      {
        Dirty = false;
        FileName = "";
        Form.Clear();
        OnTacReset();
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
      dlg.Filter = "StickyTaci Session (*.st)|*.st|All Files (*.*)|*.*";
      dlg.RestoreDirectory = true;

      if(dlg.ShowDialog() == DialogResult.OK)
      {
        Save(dlg.FileName);
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
      dlg.Filter = "StickyTaci Session (*.st)|*.st|All Files (*.*)|*.*";

      if(dlg.ShowDialog() == DialogResult.OK)
      {
        Form.Clear();
        Form.Rtf.LoadFile(dlg.FileName, RichTextBoxStreamType.PlainText);
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
      Taci.Write(Taci.CLEAR);
    }

    public void OnTactical(string tac)
    {
      Form.Input(tac);
    }

    public bool OnNextLine()
    {
      string line = "";
      if(Form.GetNextLine(ref line))
      {        
        line = line.Trim();
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

    public void OnPreviousLine()
    {
      if(CurrentLine > 0)
      {
        uint line = CurrentLine - 1;
        CurrentLine = 0;
        OnAll(line);
      };
    }

    public void OnAll(uint line)
    {
      OnTacReset();
      while((CurrentLine < line) && OnNextLine());      
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
