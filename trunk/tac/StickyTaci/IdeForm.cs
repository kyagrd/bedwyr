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
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Drawing.Imaging;
using System.Text;
using System.Windows.Forms;
using System.IO;
using System.Diagnostics;

namespace StickyTaci
{
  public partial class IdeForm : Form
  {
    private delegate void MethodInvoker1(object o1);
    private delegate void MethodInvoker2(object o1, object o2);


    private bool m_Dirty = false;
    public bool Dirty
    {
      get
      {
        return m_Dirty;
      }
    }

    private class TacticalHandler
    {
      private IdeCtrl m_Ctrl = null;
      private string m_Tactical = "";
      public TacticalHandler(IdeCtrl ctrl, string tac)
      {
        m_Ctrl = ctrl;
        m_Tactical = tac;
      }

      public void OnClick(object instance, EventArgs e)
      {
        m_Ctrl.OnTactical(m_Tactical);
      }
    }
    private class LogicHandler
    {
      private IdeCtrl m_Ctrl = null;
      private Logic m_Logic = null;
      public LogicHandler(IdeCtrl ctrl, Logic l)
      {
        m_Ctrl = ctrl;
        m_Logic = l;
      }

      public void OnClick(object instance, EventArgs e)
      {
        m_Ctrl.OnLogic(m_Logic);
      }
    }

    private bool m_LogicsChanged = false;    //So that they get updated at startup.
    public bool LogicsChanged
    {
      get
      {
        return m_LogicsChanged;
      }
      set
      {
        m_LogicsChanged = value;
      }
    }

    private bool m_TacticalsChanged = false; //So that they get updated at startup.
    public bool TacticalsChanged
    {
      get
      {
        return m_TacticalsChanged;
      }
      set
      {
        m_TacticalsChanged = value;
      }
    }

    private List<string> m_Commands = null;
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

    private List<Logic> m_Logics = null;
    public List<Logic> Logics
    {
      get
      {
        return m_Logics;
      }
      set
      {
        m_Logics = value;
        LogicsChanged = true;
      }
    }

    private List<string> m_Tacticals = null;
    public List<string> Tacticals
    {
      get
      {
        return m_Tacticals;
      }
      set
      {
        m_Tacticals = value;
        TacticalsChanged = true;

        string tacticals = String.Join(" ", m_Tacticals.ToArray());
        string commands = String.Join(" ", m_Commands.ToArray());
        InvokeDelegate(Scintilla, (MethodInvoker)delegate()
        {
          Scintilla.Lexing.Keywords[1] = tacticals;
          Scintilla.AutoComplete.ListString = commands + " " + tacticals;
          
        });
      }
    }
    
    public ScintillaNet.Scintilla Scintilla
    {
      get
      {
        return inputBox;
      }
    }

    private int m_CurrentLine = 0;
    public int CurrentLine
    {
      get
      {
        return m_CurrentLine;
      }
      set
      {
        int previous = m_CurrentLine;
        m_CurrentLine = value;
        
        InvokeDelegate(Scintilla, (MethodInvoker)delegate()
        {
          Scintilla.NativeInterface.SetProperty("lexer.simple.currentline", m_CurrentLine.ToString());
          Scintilla.Lexing.Colorize(Scintilla.Lines[previous].StartPosition, Scintilla.Lines[previous].EndPosition);
          Scintilla.Lexing.Colorize(Scintilla.Lines[m_CurrentLine].StartPosition, Scintilla.Lines[m_CurrentLine].EndPosition);
        });
        
        Debug.WriteLine("Value: " + Scintilla.NativeInterface.GetPropertyInt("lexer.simple.currentline", -1));
        UpdateCurrentLineMarker();
      }
    }

    private Image m_CurrentLineImage = null;

    private IdeCtrl m_Ctrl;
    public IdeCtrl Ctrl
    {
      get
      {
        return m_Ctrl;
      }
    }

    #region Font Information -- OBSOLETE
    private Font m_InputFont = new Font("Courier New", 8.25f, FontStyle.Regular);
    private Font m_OutputFont = new Font("Courier New", 8.25f, FontStyle.Regular);
    private Font m_GoalFont = new Font("Courier New", 8.25f, FontStyle.Regular);
    #endregion

    #region Coloring Information -- OBSOLETE
    private Color m_StringColor = Color.Maroon;
    public Color StringColor
    {
      get
      {
        return m_StringColor;
      }
      set
      {
        m_StringColor = value;
      }
    }

    private Color m_TacticalColor = Color.Blue;
    public Color TacticalColor
    {
      get
      {
        return m_TacticalColor;
      }
      set
      {
        m_TacticalColor = value;
      }
    }

    private Color m_CommandColor = Color.Red;
    public Color CommandColor
    {
      get
      {
        return m_CommandColor;
      }
      set
      {
        m_CommandColor = value;
      }
    }

    private Color m_CommentColor = Color.Green;
    public Color CommentColor
    {
      get
      {
        return m_CommentColor;
      }
      set
      {
        m_CommentColor = value;
      }
    }

    private Color m_OldInputColor = Color.LightGray;    
    public Color OldInputColor
    {
      get
      {
        return m_OldInputColor;
      }
      set
      {
        m_OldInputColor = value;
      }
    }

    private Color m_InputColor = Color.Black;
    public Color InputColor
    {
      get
      {
        return m_InputColor;
      }
      set
      {
        m_InputColor = value;
      }
    }

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
    #endregion

    #region Constructors
    public IdeForm(IdeCtrl ctrl)
    {
      InitializeComponent();

      m_CurrentLineImage = Image.FromFile("Data/CurrentLine.bmp");
      currentLineImagePanel.Paint += new PaintEventHandler(currentLineImagePanel_Paint);
      currentLineImagePanel.Show();
      
      goalBox.Font = m_GoalFont;
      
      outputBox.Font = m_OutputFont;
      outputBox.SelectionFont = m_OutputFont;

      Scintilla.Font = m_InputFont;
      Scintilla.TextChanged += new EventHandler(Scintilla_TextChanged);
      Scintilla.Scroll += new EventHandler<ScrollEventArgs>(Scintilla_Scroll);
      Scintilla.ConfigurationManager.CustomLocation = "Data\\tac.xml";
      Scintilla.ConfigurationManager.Language = "taci";
      Scintilla.Margins.Margin0.Width = 20;
      Scintilla.Margins.Margin1.Width = 0;
      Scintilla.Margins.Margin2.Width = 20;
      Scintilla.Indentation.TabWidth = 2;
      Scintilla.Indentation.UseTabs = false;

      m_Ctrl = ctrl;

      mainMenuEdit.DropDownOpening += new EventHandler(mainMenuEdit_DropDownOpening);
      mainMenuTacTacticals.DropDownOpening += new EventHandler(mainMenuTacTacticals_DropDownOpening);
      mainMenuTacTacticals.DropDownItems.Add("*dummy*");
      mainMenuTacLogics.DropDownOpening += new EventHandler(mainMenuTacLogics_DropDownOpening);
      mainMenuTacLogics.DropDownItems.Add("*dummy*");

      mainMenuTacStart.ShortcutKeys =
        ((System.Windows.Forms.Keys)
          ((System.Windows.Forms.Keys.Control |
          System.Windows.Forms.Keys.Alt)|
          System.Windows.Forms.Keys.PageUp));
      mainMenuTacEnd.ShortcutKeys =
        ((System.Windows.Forms.Keys)
          ((System.Windows.Forms.Keys.Control |
          System.Windows.Forms.Keys.Alt) |
          System.Windows.Forms.Keys.PageDown));

      TacticalsChanged = true;
      CurrentLine = 0;
    }
    #endregion

    #region Overridden Protected Methods
    protected override void OnShown(EventArgs e)
    {
      base.OnShown(e);
      Ctrl.OnShown();
    }

    protected override void WndProc(ref Message m)
    {
      //Check for WM_CLOSE:
      if(m.Msg == 0x0112 && (int)m.WParam == 0xf060)
      {
        Ctrl.OnExit();
        return;
      }
      base.WndProc(ref m);
    }

    #endregion

    #region Control Event Handlers
    private void mainMenuTacRestart_Click(object sender, EventArgs e)
    {
      goalBox.Clear();
      outputBox.Clear();
      Ctrl.OnTacRestart();
    }

    private void mainMenuTacClear_Click(object sender, EventArgs e)
    {
      Ctrl.OnTacClear();
    }

    private void mainMenuTacLogics_DropDownOpening(object sender, EventArgs e)
    {
      if(LogicsChanged)
      {
        mainMenuTacLogics.DropDownItems.Clear();
        if(Logics != null)
        {
          foreach(Logic l in Logics)
          {
            ToolStripItem t = mainMenuTacLogics.DropDownItems.Add(l.Key);
            t.ToolTipText = l.Name;
            LogicHandler h = new LogicHandler(Ctrl, l);
            t.Click += new EventHandler(h.OnClick);
          }
        }
        LogicsChanged = false;
      }
    }

    private void mainMenuTacTacticals_DropDownOpening(object sender, EventArgs e)
    {
      if(TacticalsChanged)
      {
        mainMenuTacTacticals.DropDownItems.Clear();
        if(Tacticals != null)
        {
          foreach(string tac in Tacticals)
          {
            ToolStripItem t = mainMenuTacTacticals.DropDownItems.Add(tac);
            TacticalHandler h = new TacticalHandler(Ctrl, tac);
            t.Click += new EventHandler(h.OnClick);
          }
        }
        TacticalsChanged = false;
      }
    }

    private void mainMenuEdit_DropDownOpening(object sender, EventArgs e)
    {
      mainMenuEditUndo.Enabled = Scintilla.UndoRedo.CanUndo;
      mainMenuEditRedo.Enabled = Scintilla.UndoRedo.CanRedo;
      mainMenuEditCopy.Enabled = (Scintilla.Selection.Length > 0);
      mainMenuEditPaste.Enabled = Scintilla.Clipboard.CanPaste;
    }

    private void mainMenuFileExit_Click(object sender, EventArgs e)
    {
      Ctrl.OnExit();
    }

    private void mainMenuEditPaste_Click(object sender, EventArgs e)
    {
      Scintilla.Clipboard.Paste();
    }

    private void mainMenuEditUndo_Click(object sender, EventArgs e)
    {
      Scintilla.UndoRedo.Undo();
    }

    private void mainMenuEditRedo_Click(object sender, EventArgs e)
    {
      Scintilla.UndoRedo.Redo();
    }

    private void mainMenuEditCut_Click(object sender, EventArgs e)
    {
      Scintilla.Clipboard.Cut();
    }

    private void mainMenuEditCopy_Click(object sender, EventArgs e)
    {
      Scintilla.Clipboard.Copy();
    }

    private void mainMenuEditDelete_Click(object sender, EventArgs e)
    {
      Scintilla.Selection.Text = "";
    }

    private void mainMenuFileSave_Click(object sender, EventArgs e)
    {
      Ctrl.OnSave();
    }

    private void mainMenuFileSaveAs_Click(object sender, EventArgs e)
    {
      Ctrl.OnSaveAs();
    }

    private void mainMenuEditSelectAll_Click(object sender, EventArgs e)
    {
      Scintilla.Selection.SelectAll();
    }

    private void mainMenuFileNew_Click(object sender, EventArgs e)
    {
      Ctrl.OnNew();
    }

    private void mainMenuFileOpen_Click(object sender, EventArgs e)
    {
      Ctrl.OnOpen();
    }

    private void mainMenuHelpAbout_Click(object sender, EventArgs e)
    {
      Ctrl.OnHelp();
    }

    private void mainMenuTacInclude_Click(object sender, EventArgs e)
    {
      Ctrl.OnTacInclude();
    }

    private void mainMenuTacOpen_Click(object sender, EventArgs e)
    {
      Ctrl.OnTacOpen();
    }

    private void mainMenuTacReset_Click(object sender, EventArgs e)
    {
      Ctrl.OnTacReset();
    }

    private void helpMenuTaci_Click(object sender, EventArgs e)
    {
      Ctrl.OnHelpTaci();
    }

    private void mainMenuTacNextLine_Click(object sender, EventArgs e)
    {
      Ctrl.OnNextLine();
    }

    private void mainMenuTacPreviousLine_Click(object sender, EventArgs e)
    {
      Ctrl.OnPreviousLine();
    }

    private void mainMenuTacStart_Click(object sender, EventArgs e)
    {
      Ctrl.OnStart();
    }

    private void mainMenuTacEnd_Click(object sender, EventArgs e)
    {
      Ctrl.OnEnd();
    }

    private void currentLineImagePanel_Paint(object sender, PaintEventArgs e)
    {
      Rectangle dest = new Rectangle(new Point(0, 0), m_CurrentLineImage.Size);
      ImageAttributes attr = new ImageAttributes();
      attr.SetColorKey(Color.Black, Color.Black);
      e.Graphics.DrawImage(m_CurrentLineImage, dest, 0, 0, m_CurrentLineImage.Width, m_CurrentLineImage.Height, GraphicsUnit.Pixel, attr);
    }
    #endregion

    #region Scintilla Event Handlers
    void Scintilla_Scroll(object sender, ScrollEventArgs e)
    {
      UpdateCurrentLineMarker();
    }

    void Scintilla_TextChanged(object sender, EventArgs e)
    {
      Ctrl.OnInputChanged(Scintilla.Lines.Count);
      m_Dirty = true;
    }
    #endregion

    #region Public Interface
    new public void Close()
    {
      InvokeDelegate(this, (MethodInvoker)delegate()
      {
        ((Form)this).Close();
      });
    }

    public void Output(string s)
    {
      InvokeDelegate(this, (MethodInvoker)delegate()
      {
        outputBox.SelectionFont = m_OutputFont;
        outputBox.SelectionColor = OutputColor;
        outputBox.SelectedText = s;
        outputBox.ScrollToCaret();
      });
    }

    public void ClearOutput()
    {
      InvokeDelegate(this, (MethodInvoker)delegate()
      {
        outputBox.Clear();
      });
    }

    public void Error(string s)
    {
      InvokeDelegate(this, (MethodInvoker)delegate()
      {
        //outputBox.Clear();
        outputBox.SelectionFont = m_OutputFont;
        outputBox.SelectionColor = ErrorColor;
        outputBox.SelectedText = "Error: " + s;
        outputBox.ScrollToCaret();
      });
    }

    public void Input(string s)
    {
      InvokeDelegate(this, (MethodInvoker)delegate()
      {
        Scintilla.Selection.Text = s;
      });
    }

    public void Goal(string s)
    {
      InvokeDelegate(this, (MethodInvoker)delegate()
      {  
        goalBox.Clear();
        goalBox.SelectionColor = GoalColor;
        goalBox.SelectedText = s;
      });
    }


    public bool GetNextLine(ref string line)
    {
      if(CurrentLine >= Scintilla.Lines.Count)
      {
        return false;
      }
      else
      {
        line = Scintilla.Lines[CurrentLine].Text;
        if(CurrentLine == (Scintilla.Lines.Count - 1) && line == "")
          return false;
        CurrentLine++;
        return true;
      }
    }

    public bool GetPreviousLine(ref string line)
    {
      if(CurrentLine <= 0)
      {
        return false;
      }
      else
      {
        line = Scintilla.Lines[CurrentLine - 1].Text;
        --CurrentLine;
        return true;
      }
    }

    public void Clear()
    {
      outputBox.Clear();
      Scintilla.Text = "";
      goalBox.Clear();
      m_Dirty = false;
    }

    public void SaveFile(string filename)
    {
      File.WriteAllText(filename, Scintilla.Text, Encoding.ASCII);
      m_Dirty = false;
      return;
    }

    public void LoadFile(string filename)
    {
      Scintilla.ResetText();
      Scintilla.AppendText(File.ReadAllText(filename, Encoding.ASCII));
      Scintilla.Caret.Position = 0;
      m_Dirty = false;
      return;
    }
    
    private void InvokeDelegate(Control o, MethodInvoker d)
    {
      if(o.InvokeRequired)
        o.Invoke(d, null);
      else
        d.Invoke();
    }

    public string GetLine(int line)
    {
      return Scintilla.Lines[line].Text;
    }

    #endregion

    #region Private Methods
    private void UpdateCurrentLineMarker()
    {
      //Show current line marker:
      int line = (int)CurrentLine;
      int y = 0;
      if(line == Scintilla.Lines.Count)
      {
        y = 0;
      }
      else
      {
        Point inc = new Point(0, Scintilla.PointYFromPosition(Scintilla.Lines[CurrentLine].StartPosition));
        Point inw = PointToClient(Scintilla.PointToScreen(inc));
        y = inw.Y;
        y -= Font.Height;
        y -= Font.Height;
      }
      Point p = new Point(1, y);
      currentLineImagePanel.Location = p;
    }
    #endregion
  }
}