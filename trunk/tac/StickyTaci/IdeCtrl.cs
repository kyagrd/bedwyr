using System;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;

namespace StickyTaci
{
  public class IdeCtrl
  {
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
      m_Taci.Output += new Taci.OutputHandler(Taci_Output);
      m_Taci.Goal += new Taci.OutputHandler(Taci_Goal);
      m_Taci.Error += new Taci.OutputHandler(Taci_Error);
      m_Taci.Command += new Taci.OutputHandler(Taci_Command);
    }

    public void OnRestart()
    {
      Taci.Restart();
    }

    public void OnNew()
    {
      if((Dirty && SaveMessage()) || !Dirty)
      {
        FileName = "";
        Form.Clear();
      }
    }

    private bool SaveMessage()
    {
      string caption = "The current file has changed.\nDo you want to save the changes?";
      DialogResult result = MessageBox.Show("StickyTaci", caption, MessageBoxButtons.YesNoCancel);
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
      Form.Rtf.SaveFile(filename);
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
      dlg.Filter = "StickyTaci Session (*.st)|*.st";
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
      dlg.Filter = "StickyTaci Session (*.st)|*.st";

      if(dlg.ShowDialog() == DialogResult.OK)
      {
        Form.Clear();
        Form.Rtf.LoadFile(dlg.FileName, RichTextBoxStreamType.PlainText);
      }
    }

    public void OnExit()
    {
      Taci.Write("#exit.");
      Taci.Exit();
      Form.Close();
    }

    public void OnHelpTaci()
    {
      Taci.Write("#help.");
    }

    public void OnHelp()
    {
      AboutDlg dlg = new AboutDlg();
      dlg.ShowDialog();
    }

    public void OnClear()
    {
      Taci.Write("#clear.");
    }

    public bool OnNextLine()
    {
      string line = "";
      if(Form.GetNextLine(ref line))
      {
        if(line != "")
        {
          Taci.Write(line + "\n");
        }
        return true;
      }
      return false;
    }

    public void OnInputChanged(uint numlines)
    {
      Dirty = true;
      if(CurrentLine > numlines)
      {
        CurrentLine = numlines;
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
      while((CurrentLine <= line) && OnNextLine());      
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
