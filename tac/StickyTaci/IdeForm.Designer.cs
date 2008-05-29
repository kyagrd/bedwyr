namespace StickyTaci
{
  partial class IdeForm
  {
    /// <summary>
    /// Required designer variable.
    /// </summary>
    private System.ComponentModel.IContainer components = null;

    /// <summary>
    /// Clean up any resources being used.
    /// </summary>
    /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
    protected override void Dispose(bool disposing)
    {
      if(disposing && (components != null))
      {
        components.Dispose();
      }
      base.Dispose(disposing);
    }

    #region Windows Form Designer generated code

    /// <summary>
    /// Required method for Designer support - do not modify
    /// the contents of this method with the code editor.
    /// </summary>
    private void InitializeComponent()
    {
      System.Windows.Forms.ToolStripMenuItem mainMenuTacOpen;
      System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(IdeForm));
      this.mainMenu = new System.Windows.Forms.MenuStrip();
      this.mainMenuFile = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuFileNew = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuFileOpen = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator5 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuFileSave = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuFileSaveAs = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator4 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuFileExit = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuEdit = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuEditUndo = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuEditRedo = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator2 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuEditCut = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuEditCopy = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuEditPaste = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuEditDelete = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator3 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuEditSelectAll = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTac = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacClear = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacDebug = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacInclude = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacReset = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacRestart = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacTiming = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator7 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuTacNextLine = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacPreviousLine = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacStart = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacEnd = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator6 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuTacLogics = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuTacTacticals = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuHelp = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuHelpTaci = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator1 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuHelpAbout = new System.Windows.Forms.ToolStripMenuItem();
      this.mainSplitter = new System.Windows.Forms.SplitContainer();
      this.currentLineImagePanel = new System.Windows.Forms.Panel();
      this.inputBox = new ScintillaNet.Scintilla();
      this.outputSplitter = new System.Windows.Forms.SplitContainer();
      this.goalBox = new System.Windows.Forms.RichTextBox();
      this.outputBox = new System.Windows.Forms.RichTextBox();
      mainMenuTacOpen = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenu.SuspendLayout();
      this.mainSplitter.Panel1.SuspendLayout();
      this.mainSplitter.Panel2.SuspendLayout();
      this.mainSplitter.SuspendLayout();
      ((System.ComponentModel.ISupportInitialize)(this.inputBox)).BeginInit();
      this.outputSplitter.Panel1.SuspendLayout();
      this.outputSplitter.Panel2.SuspendLayout();
      this.outputSplitter.SuspendLayout();
      this.SuspendLayout();
      // 
      // mainMenuTacOpen
      // 
      mainMenuTacOpen.Name = "mainMenuTacOpen";
      mainMenuTacOpen.ShortcutKeys = ((System.Windows.Forms.Keys)(((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Alt)
                  | System.Windows.Forms.Keys.O)));
      mainMenuTacOpen.Size = new System.Drawing.Size(214, 22);
      mainMenuTacOpen.Text = "&Open";
      mainMenuTacOpen.Click += new System.EventHandler(this.mainMenuTacOpen_Click);
      // 
      // mainMenu
      // 
      this.mainMenu.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mainMenuFile,
            this.mainMenuEdit,
            this.mainMenuTac,
            this.mainMenuHelp});
      this.mainMenu.Location = new System.Drawing.Point(0, 0);
      this.mainMenu.Name = "mainMenu";
      this.mainMenu.Size = new System.Drawing.Size(705, 24);
      this.mainMenu.TabIndex = 0;
      this.mainMenu.Text = "mainMenu";
      // 
      // mainMenuFile
      // 
      this.mainMenuFile.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mainMenuFileNew,
            this.mainMenuFileOpen,
            this.toolStripSeparator5,
            this.mainMenuFileSave,
            this.mainMenuFileSaveAs,
            this.toolStripSeparator4,
            this.mainMenuFileExit});
      this.mainMenuFile.Name = "mainMenuFile";
      this.mainMenuFile.Size = new System.Drawing.Size(35, 20);
      this.mainMenuFile.Text = "&File";
      // 
      // mainMenuFileNew
      // 
      this.mainMenuFileNew.Name = "mainMenuFileNew";
      this.mainMenuFileNew.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.N)));
      this.mainMenuFileNew.Size = new System.Drawing.Size(151, 22);
      this.mainMenuFileNew.Text = "&New";
      this.mainMenuFileNew.Click += new System.EventHandler(this.mainMenuFileNew_Click);
      // 
      // mainMenuFileOpen
      // 
      this.mainMenuFileOpen.Name = "mainMenuFileOpen";
      this.mainMenuFileOpen.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.O)));
      this.mainMenuFileOpen.Size = new System.Drawing.Size(151, 22);
      this.mainMenuFileOpen.Text = "&Open";
      this.mainMenuFileOpen.Click += new System.EventHandler(this.mainMenuFileOpen_Click);
      // 
      // toolStripSeparator5
      // 
      this.toolStripSeparator5.Name = "toolStripSeparator5";
      this.toolStripSeparator5.Size = new System.Drawing.Size(148, 6);
      // 
      // mainMenuFileSave
      // 
      this.mainMenuFileSave.Name = "mainMenuFileSave";
      this.mainMenuFileSave.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.S)));
      this.mainMenuFileSave.Size = new System.Drawing.Size(151, 22);
      this.mainMenuFileSave.Text = "&Save";
      this.mainMenuFileSave.Click += new System.EventHandler(this.mainMenuFileSave_Click);
      // 
      // mainMenuFileSaveAs
      // 
      this.mainMenuFileSaveAs.Name = "mainMenuFileSaveAs";
      this.mainMenuFileSaveAs.Size = new System.Drawing.Size(151, 22);
      this.mainMenuFileSaveAs.Text = "Save &As";
      this.mainMenuFileSaveAs.Click += new System.EventHandler(this.mainMenuFileSaveAs_Click);
      // 
      // toolStripSeparator4
      // 
      this.toolStripSeparator4.Name = "toolStripSeparator4";
      this.toolStripSeparator4.Size = new System.Drawing.Size(148, 6);
      // 
      // mainMenuFileExit
      // 
      this.mainMenuFileExit.Name = "mainMenuFileExit";
      this.mainMenuFileExit.Size = new System.Drawing.Size(151, 22);
      this.mainMenuFileExit.Text = "E&xit";
      this.mainMenuFileExit.Click += new System.EventHandler(this.mainMenuFileExit_Click);
      // 
      // mainMenuEdit
      // 
      this.mainMenuEdit.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mainMenuEditUndo,
            this.mainMenuEditRedo,
            this.toolStripSeparator2,
            this.mainMenuEditCut,
            this.mainMenuEditCopy,
            this.mainMenuEditPaste,
            this.mainMenuEditDelete,
            this.toolStripSeparator3,
            this.mainMenuEditSelectAll});
      this.mainMenuEdit.Name = "mainMenuEdit";
      this.mainMenuEdit.Size = new System.Drawing.Size(37, 20);
      this.mainMenuEdit.Text = "&Edit";
      // 
      // mainMenuEditUndo
      // 
      this.mainMenuEditUndo.Name = "mainMenuEditUndo";
      this.mainMenuEditUndo.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Z)));
      this.mainMenuEditUndo.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditUndo.Text = "&Undo";
      this.mainMenuEditUndo.Click += new System.EventHandler(this.mainMenuEditUndo_Click);
      // 
      // mainMenuEditRedo
      // 
      this.mainMenuEditRedo.Name = "mainMenuEditRedo";
      this.mainMenuEditRedo.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Y)));
      this.mainMenuEditRedo.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditRedo.Text = "&Redo";
      this.mainMenuEditRedo.Click += new System.EventHandler(this.mainMenuEditRedo_Click);
      // 
      // toolStripSeparator2
      // 
      this.toolStripSeparator2.Name = "toolStripSeparator2";
      this.toolStripSeparator2.Size = new System.Drawing.Size(164, 6);
      // 
      // mainMenuEditCut
      // 
      this.mainMenuEditCut.Name = "mainMenuEditCut";
      this.mainMenuEditCut.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.X)));
      this.mainMenuEditCut.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditCut.Text = "Cu&t";
      this.mainMenuEditCut.Click += new System.EventHandler(this.mainMenuEditCut_Click);
      // 
      // mainMenuEditCopy
      // 
      this.mainMenuEditCopy.Name = "mainMenuEditCopy";
      this.mainMenuEditCopy.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.C)));
      this.mainMenuEditCopy.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditCopy.Text = "&Copy";
      this.mainMenuEditCopy.Click += new System.EventHandler(this.mainMenuEditCopy_Click);
      // 
      // mainMenuEditPaste
      // 
      this.mainMenuEditPaste.Name = "mainMenuEditPaste";
      this.mainMenuEditPaste.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.V)));
      this.mainMenuEditPaste.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditPaste.Text = "&Paste";
      this.mainMenuEditPaste.Click += new System.EventHandler(this.mainMenuEditPaste_Click);
      // 
      // mainMenuEditDelete
      // 
      this.mainMenuEditDelete.Name = "mainMenuEditDelete";
      this.mainMenuEditDelete.ShortcutKeys = System.Windows.Forms.Keys.Delete;
      this.mainMenuEditDelete.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditDelete.Text = "&Delete";
      this.mainMenuEditDelete.Click += new System.EventHandler(this.mainMenuEditDelete_Click);
      // 
      // toolStripSeparator3
      // 
      this.toolStripSeparator3.Name = "toolStripSeparator3";
      this.toolStripSeparator3.Size = new System.Drawing.Size(164, 6);
      // 
      // mainMenuEditSelectAll
      // 
      this.mainMenuEditSelectAll.Name = "mainMenuEditSelectAll";
      this.mainMenuEditSelectAll.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.A)));
      this.mainMenuEditSelectAll.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditSelectAll.Text = "Select &All";
      this.mainMenuEditSelectAll.Click += new System.EventHandler(this.mainMenuEditSelectAll_Click);
      // 
      // mainMenuTac
      // 
      this.mainMenuTac.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mainMenuTacClear,
            this.mainMenuTacDebug,
            this.mainMenuTacInclude,
            mainMenuTacOpen,
            this.mainMenuTacReset,
            this.mainMenuTacRestart,
            this.mainMenuTacTiming,
            this.toolStripSeparator7,
            this.mainMenuTacNextLine,
            this.mainMenuTacPreviousLine,
            this.mainMenuTacStart,
            this.mainMenuTacEnd,
            this.toolStripSeparator6,
            this.mainMenuTacLogics,
            this.mainMenuTacTacticals});
      this.mainMenuTac.Name = "mainMenuTac";
      this.mainMenuTac.Size = new System.Drawing.Size(36, 20);
      this.mainMenuTac.Text = "&Tac";
      // 
      // mainMenuTacClear
      // 
      this.mainMenuTacClear.Name = "mainMenuTacClear";
      this.mainMenuTacClear.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacClear.Text = "&Clear";
      this.mainMenuTacClear.Click += new System.EventHandler(this.mainMenuTacClear_Click);
      // 
      // mainMenuTacDebug
      // 
      this.mainMenuTacDebug.CheckOnClick = true;
      this.mainMenuTacDebug.Name = "mainMenuTacDebug";
      this.mainMenuTacDebug.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacDebug.Text = "&Debug";
      // 
      // mainMenuTacInclude
      // 
      this.mainMenuTacInclude.Name = "mainMenuTacInclude";
      this.mainMenuTacInclude.ShortcutKeys = ((System.Windows.Forms.Keys)(((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Alt)
                  | System.Windows.Forms.Keys.I)));
      this.mainMenuTacInclude.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacInclude.Text = "&Include";
      this.mainMenuTacInclude.Click += new System.EventHandler(this.mainMenuTacInclude_Click);
      // 
      // mainMenuTacReset
      // 
      this.mainMenuTacReset.Name = "mainMenuTacReset";
      this.mainMenuTacReset.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacReset.Text = "&Reset";
      this.mainMenuTacReset.Click += new System.EventHandler(this.mainMenuTacReset_Click);
      // 
      // mainMenuTacRestart
      // 
      this.mainMenuTacRestart.Name = "mainMenuTacRestart";
      this.mainMenuTacRestart.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacRestart.Text = "Re&start";
      this.mainMenuTacRestart.Click += new System.EventHandler(this.mainMenuTacRestart_Click);
      // 
      // mainMenuTacTiming
      // 
      this.mainMenuTacTiming.CheckOnClick = true;
      this.mainMenuTacTiming.Name = "mainMenuTacTiming";
      this.mainMenuTacTiming.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacTiming.Text = "&Timing";
      // 
      // toolStripSeparator7
      // 
      this.toolStripSeparator7.Name = "toolStripSeparator7";
      this.toolStripSeparator7.Size = new System.Drawing.Size(211, 6);
      // 
      // mainMenuTacNextLine
      // 
      this.mainMenuTacNextLine.Name = "mainMenuTacNextLine";
      this.mainMenuTacNextLine.ShortcutKeys = ((System.Windows.Forms.Keys)(((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Alt)
                  | System.Windows.Forms.Keys.Down)));
      this.mainMenuTacNextLine.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacNextLine.Text = "&Next Line";
      this.mainMenuTacNextLine.Click += new System.EventHandler(this.mainMenuTacNextLine_Click);
      // 
      // mainMenuTacPreviousLine
      // 
      this.mainMenuTacPreviousLine.Name = "mainMenuTacPreviousLine";
      this.mainMenuTacPreviousLine.ShortcutKeys = ((System.Windows.Forms.Keys)(((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Alt)
                  | System.Windows.Forms.Keys.Up)));
      this.mainMenuTacPreviousLine.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacPreviousLine.Text = "&Previous Line";
      this.mainMenuTacPreviousLine.Click += new System.EventHandler(this.mainMenuTacPreviousLine_Click);
      // 
      // mainMenuTacStart
      // 
      this.mainMenuTacStart.Name = "mainMenuTacStart";
      this.mainMenuTacStart.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacStart.Text = "&Start";
      this.mainMenuTacStart.Click += new System.EventHandler(this.mainMenuTacStart_Click);
      // 
      // mainMenuTacEnd
      // 
      this.mainMenuTacEnd.Name = "mainMenuTacEnd";
      this.mainMenuTacEnd.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacEnd.Text = "&End";
      this.mainMenuTacEnd.Click += new System.EventHandler(this.mainMenuTacEnd_Click);
      // 
      // toolStripSeparator6
      // 
      this.toolStripSeparator6.Name = "toolStripSeparator6";
      this.toolStripSeparator6.Size = new System.Drawing.Size(211, 6);
      // 
      // mainMenuTacLogics
      // 
      this.mainMenuTacLogics.Name = "mainMenuTacLogics";
      this.mainMenuTacLogics.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacLogics.Text = "&Logics";
      // 
      // mainMenuTacTacticals
      // 
      this.mainMenuTacTacticals.Name = "mainMenuTacTacticals";
      this.mainMenuTacTacticals.Size = new System.Drawing.Size(214, 22);
      this.mainMenuTacTacticals.Text = "&Tacticals";
      // 
      // mainMenuHelp
      // 
      this.mainMenuHelp.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mainMenuHelpTaci,
            this.toolStripSeparator1,
            this.mainMenuHelpAbout});
      this.mainMenuHelp.Name = "mainMenuHelp";
      this.mainMenuHelp.Size = new System.Drawing.Size(40, 20);
      this.mainMenuHelp.Text = "&Help";
      // 
      // mainMenuHelpTaci
      // 
      this.mainMenuHelpTaci.Name = "mainMenuHelpTaci";
      this.mainMenuHelpTaci.Size = new System.Drawing.Size(164, 22);
      this.mainMenuHelpTaci.Text = "&Taci";
      this.mainMenuHelpTaci.Click += new System.EventHandler(this.helpMenuTaci_Click);
      // 
      // toolStripSeparator1
      // 
      this.toolStripSeparator1.Name = "toolStripSeparator1";
      this.toolStripSeparator1.Size = new System.Drawing.Size(161, 6);
      // 
      // mainMenuHelpAbout
      // 
      this.mainMenuHelpAbout.Name = "mainMenuHelpAbout";
      this.mainMenuHelpAbout.Size = new System.Drawing.Size(164, 22);
      this.mainMenuHelpAbout.Text = "&About StickyTaci";
      this.mainMenuHelpAbout.Click += new System.EventHandler(this.mainMenuHelpAbout_Click);
      // 
      // mainSplitter
      // 
      this.mainSplitter.Dock = System.Windows.Forms.DockStyle.Fill;
      this.mainSplitter.Location = new System.Drawing.Point(0, 24);
      this.mainSplitter.Name = "mainSplitter";
      // 
      // mainSplitter.Panel1
      // 
      this.mainSplitter.Panel1.Controls.Add(this.currentLineImagePanel);
      this.mainSplitter.Panel1.Controls.Add(this.inputBox);
      // 
      // mainSplitter.Panel2
      // 
      this.mainSplitter.Panel2.Controls.Add(this.outputSplitter);
      this.mainSplitter.Size = new System.Drawing.Size(705, 242);
      this.mainSplitter.SplitterDistance = 344;
      this.mainSplitter.TabIndex = 1;
      // 
      // currentLineImagePanel
      // 
      this.currentLineImagePanel.Location = new System.Drawing.Point(1, 0);
      this.currentLineImagePanel.Name = "currentLineImagePanel";
      this.currentLineImagePanel.Size = new System.Drawing.Size(16, 16);
      this.currentLineImagePanel.TabIndex = 1;
      // 
      // inputBox
      // 
      this.inputBox.Anchor = ((System.Windows.Forms.AnchorStyles)((((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Bottom)
                  | System.Windows.Forms.AnchorStyles.Left)
                  | System.Windows.Forms.AnchorStyles.Right)));
      this.inputBox.CurrentPos = 0;
      this.inputBox.Font = new System.Drawing.Font("Courier New", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
      this.inputBox.Location = new System.Drawing.Point(18, 0);
      this.inputBox.Name = "inputBox";
      this.inputBox.Scrolling.HorizontalWidth = 256;
      this.inputBox.Size = new System.Drawing.Size(330, 242);
      this.inputBox.TabIndex = 0;
      this.inputBox.UseFont = true;
      // 
      // outputSplitter
      // 
      this.outputSplitter.Dock = System.Windows.Forms.DockStyle.Fill;
      this.outputSplitter.Location = new System.Drawing.Point(0, 0);
      this.outputSplitter.Name = "outputSplitter";
      this.outputSplitter.Orientation = System.Windows.Forms.Orientation.Horizontal;
      // 
      // outputSplitter.Panel1
      // 
      this.outputSplitter.Panel1.Controls.Add(this.goalBox);
      // 
      // outputSplitter.Panel2
      // 
      this.outputSplitter.Panel2.Controls.Add(this.outputBox);
      this.outputSplitter.Size = new System.Drawing.Size(357, 242);
      this.outputSplitter.SplitterDistance = 92;
      this.outputSplitter.TabIndex = 0;
      // 
      // goalBox
      // 
      this.goalBox.BackColor = System.Drawing.SystemColors.Window;
      this.goalBox.Dock = System.Windows.Forms.DockStyle.Fill;
      this.goalBox.ForeColor = System.Drawing.SystemColors.WindowText;
      this.goalBox.Location = new System.Drawing.Point(0, 0);
      this.goalBox.Name = "goalBox";
      this.goalBox.ReadOnly = true;
      this.goalBox.Size = new System.Drawing.Size(357, 92);
      this.goalBox.TabIndex = 0;
      this.goalBox.Text = "";
      // 
      // outputBox
      // 
      this.outputBox.BackColor = System.Drawing.SystemColors.Window;
      this.outputBox.Dock = System.Windows.Forms.DockStyle.Fill;
      this.outputBox.Location = new System.Drawing.Point(0, 0);
      this.outputBox.Name = "outputBox";
      this.outputBox.ReadOnly = true;
      this.outputBox.Size = new System.Drawing.Size(357, 146);
      this.outputBox.TabIndex = 0;
      this.outputBox.Text = "";
      // 
      // IdeForm
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(705, 266);
      this.Controls.Add(this.mainSplitter);
      this.Controls.Add(this.mainMenu);
      this.Icon = ((System.Drawing.Icon)(resources.GetObject("$this.Icon")));
      this.MainMenuStrip = this.mainMenu;
      this.Name = "IdeForm";
      this.StartPosition = System.Windows.Forms.FormStartPosition.CenterScreen;
      this.Text = "StickyTaci";
      this.WindowState = System.Windows.Forms.FormWindowState.Maximized;
      this.mainMenu.ResumeLayout(false);
      this.mainMenu.PerformLayout();
      this.mainSplitter.Panel1.ResumeLayout(false);
      this.mainSplitter.Panel2.ResumeLayout(false);
      this.mainSplitter.ResumeLayout(false);
      ((System.ComponentModel.ISupportInitialize)(this.inputBox)).EndInit();
      this.outputSplitter.Panel1.ResumeLayout(false);
      this.outputSplitter.Panel2.ResumeLayout(false);
      this.outputSplitter.ResumeLayout(false);
      this.ResumeLayout(false);
      this.PerformLayout();

    }

    #endregion

    private System.Windows.Forms.MenuStrip mainMenu;
    private System.Windows.Forms.ToolStripMenuItem mainMenuFile;
    private System.Windows.Forms.ToolStripMenuItem mainMenuFileExit;
    private System.Windows.Forms.SplitContainer mainSplitter;
    private System.Windows.Forms.SplitContainer outputSplitter;
    private ScintillaNet.Scintilla inputBox;
    private System.Windows.Forms.RichTextBox goalBox;
    private System.Windows.Forms.RichTextBox outputBox;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEdit;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTac;
    private System.Windows.Forms.ToolStripMenuItem mainMenuHelp;
    private System.Windows.Forms.ToolStripMenuItem mainMenuHelpTaci;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator1;
    private System.Windows.Forms.ToolStripMenuItem mainMenuHelpAbout;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacClear;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacRestart;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEditCut;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEditCopy;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEditPaste;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEditDelete;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEditUndo;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator2;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEditRedo;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator3;
    private System.Windows.Forms.ToolStripMenuItem mainMenuEditSelectAll;
    private System.Windows.Forms.Panel currentLineImagePanel;
    private System.Windows.Forms.ToolStripMenuItem mainMenuFileNew;
    private System.Windows.Forms.ToolStripMenuItem mainMenuFileOpen;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator5;
    private System.Windows.Forms.ToolStripMenuItem mainMenuFileSave;
    private System.Windows.Forms.ToolStripMenuItem mainMenuFileSaveAs;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator4;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacDebug;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacInclude;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator6;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacTacticals;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacTiming;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacLogics;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacReset;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator7;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacNextLine;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacPreviousLine;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacStart;
    private System.Windows.Forms.ToolStripMenuItem mainMenuTacEnd;
  }
}

