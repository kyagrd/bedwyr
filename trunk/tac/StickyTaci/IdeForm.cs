using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace StickyTaci
{
  public partial class IdeForm : Form
  {
    private delegate void OutputHandler(string s);
    private delegate void ClearHandler();

    private Font m_Font = new Font("Courier New", 8, FontStyle.Regular);
    private Color m_ErrorColor = Color.Red;
    public Color ErrorColor
    {
      get
      {
        return m_ErrorColor;
      }
      set
      {
        m_ErrorColor = value;
      }
    }

    private Color m_OutputColor = Color.Black;
    public Color OutputColor
    {
      get
      {
        return m_OutputColor;
      }
      set
      {
        m_OutputColor = value;
      }
    }

    private Color m_GoalColor = Color.Black;
    public Color GoalColor
    {
      get
      {
        return m_GoalColor;
      }
      set
      {
        m_GoalColor = value;
      }
    }
    private IdeCtrl m_Ctrl;
    public IdeCtrl Ctrl
    {
      get
      {
        return m_Ctrl;
      }
    }

    public IdeForm(IdeCtrl ctrl)
    {
      InitializeComponent();

      goalBox.Font = m_Font;
      outputBox.SelectionFont = m_Font;

      inputBox.KeyDown += new KeyEventHandler(inputBox_KeyDown);
      m_Ctrl = ctrl;
    }

    public void Output(string s)
    {
      if(outputBox.InvokeRequired)
      {
        OutputHandler h = new OutputHandler(Output);
        Invoke(h, new object[] { s });
      }
      else
      {
        outputBox.SelectionFont = m_Font;
        outputBox.SelectionColor = OutputColor;
        outputBox.SelectedText = s;
        outputBox.ScrollToCaret();
      }
    }

    public void ClearOutput()
    {
      if(outputBox.InvokeRequired)
      {
        ClearHandler h = new ClearHandler(ClearOutput);
        Invoke(h);
      }
      else
      {
        outputBox.Clear();
      }
    }

    public void Error(string s)
    {
      if(outputBox.InvokeRequired)
      {
        OutputHandler h = new OutputHandler(Error);
        Invoke(h, new object[] { s });
      }
      else
      {
        outputBox.SelectionFont = m_Font;
        outputBox.SelectionColor = ErrorColor;
        outputBox.SelectedText = s;
        outputBox.ScrollToCaret();
      }
    }

    public void Goal(string s)
    {
      if(goalBox.InvokeRequired)
      {
        OutputHandler h = new OutputHandler(Goal);
        Invoke(h, new object[] { s });
      }
      else
      {
        goalBox.Clear();
        goalBox.SelectionColor = GoalColor;
        goalBox.SelectedText = s;
      }
    }

    void inputBox_KeyDown(object sender, KeyEventArgs e)
    {
      if((e.KeyCode == Keys.Down) && e.Control && e.Alt)
      {
        Ctrl.OnNextLine();
        e.SuppressKeyPress = true;
      }
      else if((e.KeyCode == Keys.Up) && e.Control && e.Alt)
      {
        Ctrl.OnPreviousLine();
        e.SuppressKeyPress = true;
      }
      else if((e.KeyCode == Keys.Enter) && e.Control && e.Alt)
      {
        Ctrl.OnAll();
        e.SuppressKeyPress = true;
      }
      return;
    }

    private void mainMenuFileExit_Click(object sender, EventArgs e)
    {
      Ctrl.OnExit();
    }

    private void helpMenuTaci_Click(object sender, EventArgs e)
    {
      Ctrl.OnHelpTaci();
    }

    private void mainMenuTacRestart_Click(object sender, EventArgs e)
    {
      goalBox.Clear();
      outputBox.Clear();
      Ctrl.OnRestart();
    }

    private void mainMenuTacClear_Click(object sender, EventArgs e)
    {
      Ctrl.OnClear();
    }
  }
}