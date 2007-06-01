using System;
using System.Collections.Generic;
using System.Text;

namespace StickyTaci
{
  public class IdeCtrl
  {
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

    public void OnClear()
    {
      Taci.Write("#clear.");
    }

    public void OnNextLine()
    {
    }

    public void OnPreviousLine()
    {
    }

    public void OnAll()
    {
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
