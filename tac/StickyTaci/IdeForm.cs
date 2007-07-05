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

namespace StickyTaci
{
  public partial class IdeForm : Form
  {
    private int CompareLength(string s1, string s2)
    {
      return s1.Length.CompareTo(s2.Length);
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
    private List<string> m_SortedCommands = null;
    public List<string> Commands
    {
      get
      {
        return m_Commands;
      }
      set
      {
        m_Commands = value;
        m_SortedCommands = value.ConvertAll<string>(new Converter<string, string>(string.Copy));
        m_SortedCommands.Sort(new Comparison<string>(CompareLength));
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

    private bool m_Coloring = false;
    private List<string> m_Tacticals = null;

    //Sorted by length so that the dumb syntac highlighter uses
    //the largest match.
    private List<string> m_SortedTacticals = null; 
    public List<string> Tacticals
    {
      get
      {
        return m_Tacticals;
      }
      set
      {
        m_Tacticals = value;

        m_SortedTacticals = value.ConvertAll<string>(new Converter<string, string>(string.Copy));
        m_SortedTacticals.Sort(new Comparison<string>(CompareLength));

        TacticalsChanged = true;

      }
    }

    public RichTextBox Rtf
    {
      get
      {
        return inputBox;
      }
    }

    private uint m_CurrentLine = 0;
    public uint CurrentLine
    {
      get
      {
        return m_CurrentLine;
      }
      set
      {
        m_CurrentLine = value;

        UpdateCurrentLineMarker();
      }
    }

    private delegate void IOHandler(string s);
    private delegate void ClearHandler();
    private delegate void CloseHandler();

    private Image m_CurrentLineImage = null;
    private Font m_InputFont = new Font("Courier New", 10, FontStyle.Regular);
    private Font m_OutputFont = new Font("Courier New", 8, FontStyle.Regular);
    private Font m_GoalFont = new Font("Courier New", 10, FontStyle.Regular);

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

      m_CurrentLineImage = Image.FromFile("Data/CurrentLine.bmp");
      currentLineImagePanel.Paint += new PaintEventHandler(currentLineImagePanel_Paint);
      currentLineImagePanel.Show();
      
      goalBox.Font = m_GoalFont;
      
      outputBox.Font = m_OutputFont;
      outputBox.SelectionFont = m_OutputFont;

      Rtf.Font = m_InputFont;
      Rtf.KeyDown += new KeyEventHandler(inputBox_KeyDown);
      Rtf.TextChanged += new EventHandler(inputBox_TextChanged);
      Rtf.VScroll += new EventHandler(inputBox_VScroll);

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

    void inputBox_VScroll(object sender, EventArgs e)
    {
      UpdateCurrentLineMarker();
    }

    protected override void OnShown(EventArgs e)
    {
      base.OnShown(e);
      Ctrl.OnShown();
    }

    void mainMenuTacLogics_DropDownOpening(object sender, EventArgs e)
    {
      if(LogicsChanged)
      {
        mainMenuTacLogics.DropDownItems.Clear();
        if(Logics != null)
        {
          foreach(Logic l in Logics)
          {
            ToolStripItem t = mainMenuTacLogics.DropDownItems.Add(l.Key);
            LogicHandler h = new LogicHandler(Ctrl, l);
            t.Click += new EventHandler(h.OnClick);
          }
        }
        LogicsChanged = false;
      }
    }

    void mainMenuTacTacticals_DropDownOpening(object sender, EventArgs e)
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

    void mainMenuEdit_DropDownOpening(object sender, EventArgs e)
    {
      mainMenuEditUndo.Enabled = Rtf.CanUndo;
      mainMenuEditRedo.Enabled = Rtf.CanRedo;
      mainMenuEditCopy.Enabled = (Rtf.SelectionLength > 0);
      mainMenuEditPaste.Enabled = Rtf.CanPaste(DataFormats.GetFormat(DataFormats.Text));
    }

    void currentLineImagePanel_Paint(object sender, PaintEventArgs e)
    {
      Rectangle dest = new Rectangle(new Point(0, 0), m_CurrentLineImage.Size);
      ImageAttributes attr = new ImageAttributes();
      attr.SetColorKey(Color.Black, Color.Black);
      e.Graphics.DrawImage(m_CurrentLineImage, dest, 0, 0, m_CurrentLineImage.Width, m_CurrentLineImage.Height, GraphicsUnit.Pixel, attr);
    }

    void inputBox_TextChanged(object sender, EventArgs e)
    {
      if(!m_Coloring)
      {
        Ctrl.OnInputChanged((uint)inputBox.Lines.Length);
      }
    }

    new public void Close()
    {
      if(this.InvokeRequired)
      {
        CloseHandler h = new CloseHandler(Close);
        Invoke(h);
      }
      else
      {
        //Real close.
        ((Form)this).Close();
      }
    }
    public void Output(string s)
    {
      if(outputBox.InvokeRequired)
      {
        IOHandler h = new IOHandler(Output);
        Invoke(h, new object[] { s });
      }
      else
      {
        outputBox.SelectionFont = m_OutputFont;
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
        IOHandler h = new IOHandler(Error);
        Invoke(h, new object[] { s });
      }
      else
      {
        //outputBox.Clear();
        outputBox.SelectionFont = m_OutputFont;
        outputBox.SelectionColor = ErrorColor;
        outputBox.SelectedText = "Error: " + s;
        outputBox.ScrollToCaret();
      }
    }

    public void Input(string s)
    {
      if(goalBox.InvokeRequired)
      {
        IOHandler h = new IOHandler(Input);
        Invoke(h, new object[] { s });
      }
      else
      {
        inputBox.SelectionColor = InputColor;
        inputBox.SelectedText = s;
      }
    }

    public void Goal(string s)
    {
      if(goalBox.InvokeRequired)
      {
        IOHandler h = new IOHandler(Goal);
        Invoke(h, new object[] { s });
      }
      else
      {
        goalBox.Clear();
        goalBox.SelectionColor = GoalColor;
        goalBox.SelectedText = s;
      }
    }

    public void ColorLines(uint max)
    {
      int state = SaveState();
      int len = Rtf.SelectionLength;
      for(uint i = 0; i < max; i++)
      {
        ColorLine(i);
      }
      RestoreState(state);
      Rtf.SelectionLength = len;
    }

    private void ColorLine(uint linenum)
    {
      if(linenum < 0 || linenum > (Rtf.Lines.Length - 1))
        return;

      int start = Rtf.GetFirstCharIndexFromLine((int)linenum);      
      string line = Rtf.Lines[linenum];

      if(line == "")
        return;

      //If this is an "old" line, color it green.
      if(linenum < CurrentLine)
      {
        Rtf.Select(start, line.Length);
        Rtf.SelectionColor = OldInputColor;
        return;
      }

      //Reset the color.
      Rtf.Select(start, line.Length);
      Rtf.SelectionColor = InputColor;

      //If the first character in the line is a % it is a comment.
      string comment = line.Trim();
      if(comment != "" && comment[0] == '%')
      {
        Rtf.Select(start, line.Length);
        Rtf.SelectionColor = CommentColor;
        return;
      }
      
      //Otherwise color it right:
      if(m_SortedTacticals != null)
      {
        foreach(string tactical in m_SortedTacticals)
        {
          int index = line.IndexOf(tactical);
          while(index != -1)
          {
            Rtf.Select(start + index, tactical.Length);
            Rtf.SelectionColor = TacticalColor;
            index = line.IndexOf(tactical, index + 1);
          }
        }
      }

      if(m_SortedCommands != null)
      {
        foreach(string command in m_SortedCommands)
        {
          int index = line.IndexOf(command);
          while(index != -1)
          {
            Rtf.Select(start + index, command.Length);
            Rtf.SelectionColor = CommandColor;
            index = line.IndexOf(command, index + 1);
          }
        }
      }
    }

    public void ColorCurrentLine()
    {
      int state = SaveState();
      ColorLine((uint)Rtf.GetLineFromCharIndex(Rtf.SelectionStart));
      RestoreState(state);
    }

    public void inputBox_KeyDown(object sender, KeyEventArgs e)
    {
      int state = SaveState();
      int length = Rtf.SelectionLength;

      //Coloring Triggers:
      if((e.KeyCode == Keys.D9 || e.KeyCode == Keys.D0) && e.Shift)
      {
        //Parens
        ColorCurrentLine();
      }
      else if(e.KeyCode == Keys.OemPeriod || e.KeyCode == Keys.Oemcomma)
      {
        //Period or comma
        ColorCurrentLine();
      }
      else if(e.KeyCode == Keys.Space || e.KeyCode == Keys.Tab || e.KeyCode == Keys.Enter)
      {
        //Whitespace
        ColorCurrentLine();
      }
      else if(e.KeyCode == Keys.Back || e.KeyCode == Keys.Delete)
      {
        //Backspace/Delete
        ColorCurrentLine();
      }
      RestoreState(state);
      Rtf.SelectionLength = length;
      return;
    }

    public void Clear()
    {
      outputBox.Clear();
      inputBox.Clear();
      goalBox.Clear();
    }

    public bool GetNextLine(ref string line)
    {
      if(CurrentLine >= inputBox.Lines.Length)
      {
        return false;
      }
      else
      {
        line = inputBox.Lines[CurrentLine];
        if(CurrentLine == (inputBox.Lines.Length - 1) && line == "" )
          return false;
        ++CurrentLine;

        int state = SaveState();
        ColorLine(CurrentLine - 1);
        RestoreState(state);
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
        line = inputBox.Lines[CurrentLine - 1];
        --CurrentLine;

        int state = SaveState();
        ColorLine(CurrentLine - 1);
        RestoreState(state);
        return true;
      }
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
      Ctrl.OnTacRestart();
    }

    private void mainMenuTacClear_Click(object sender, EventArgs e)
    {
      Ctrl.OnTacClear();
    }

    public string GetLine(uint line)
    {
      int begin = inputBox.GetFirstCharIndexFromLine((int)line);
      int end = inputBox.GetFirstCharIndexFromLine((int)line + 1);
      if(end - begin < 0 || begin < 0 || end < 0)
        return "";
      return inputBox.Text.Substring(begin, end - begin);
    }

    private void mainMenuEditPaste_Click(object sender, EventArgs e)
    {
      inputBox.Paste();
      inputBox.SelectionColor = InputColor;

      uint startline = (uint)Rtf.GetLineFromCharIndex(inputBox.SelectionStart);
      uint endline = (uint)Rtf.GetLineFromCharIndex(inputBox.SelectionStart + inputBox.SelectionLength);

      int state = SaveState();
      ColorLine(startline);
      for(uint currentline = startline + 1u; (currentline < endline); currentline++)
      {
        ColorLine(currentline);
      }
      RestoreState(state);
    }

    private void mainMenuEditUndo_Click(object sender, EventArgs e)
    {
      inputBox.Undo();
    }

    private void mainMenuEditRedo_Click(object sender, EventArgs e)
    {
      inputBox.Redo();
    }

    private void mainMenuEditCut_Click(object sender, EventArgs e)
    {
      inputBox.Cut();
    }

    private void mainMenuEditCopy_Click(object sender, EventArgs e)
    {
      inputBox.Copy();
    }

    private void mainMenuEditDelete_Click(object sender, EventArgs e)
    {
      inputBox.SelectedText = "";
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
      inputBox.SelectAll();
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
      uint current = CurrentLine;
      Ctrl.OnTacReset();
      ColorLines(current);
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

    private int SaveState()
    {
      m_Coloring = true;
      Rtf.Enabled = false;
      return Rtf.SelectionStart;
    }

    private void RestoreState(int i)
    {
      m_Coloring = false;
      Rtf.Select(i, 0);
      Rtf.SelectionColor = InputColor;
      Rtf.Enabled = true;
      Rtf.Focus();
    }

    private void mainMenuTacNextLine_Click(object sender, EventArgs e)
    {
      Ctrl.OnNextLine();
    }

    private void mainMenuTacPreviousLine_Click(object sender, EventArgs e)
    {
      Ctrl.OnPreviousLine();

      int state = SaveState();
      ColorLine(CurrentLine);
      RestoreState(state);
    }

    private void mainMenuTacStart_Click(object sender, EventArgs e)
    {
      uint current = CurrentLine;
      Ctrl.OnStart();
      ColorLines(current);
    }

    private void mainMenuTacEnd_Click(object sender, EventArgs e)
    {
      Ctrl.OnEnd();
    }

    private void UpdateCurrentLineMarker()
    {
      //Show current line marker:
      int line = (int)m_CurrentLine;
      int y = 0;
      if(line == Rtf.Lines.Length)
      {
        y = 0;
      }
      else
      {
        Point inc = (Rtf.GetPositionFromCharIndex(Rtf.GetFirstCharIndexFromLine(line)));
        Point inw = PointToClient(Rtf.PointToScreen(inc));
        y = inw.Y;
        y -= Font.Height;
        y -= Font.Height;
      }
      Point p = new Point(1, y);
      currentLineImagePanel.Location = p;
    }
  }
}