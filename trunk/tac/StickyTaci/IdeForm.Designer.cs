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
      this.mainMenu = new System.Windows.Forms.MenuStrip();
      this.mainMenuFile = new System.Windows.Forms.ToolStripMenuItem();
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
      this.mainMenuTacRestart = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuHelp = new System.Windows.Forms.ToolStripMenuItem();
      this.mainMenuHelpTaci = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator1 = new System.Windows.Forms.ToolStripSeparator();
      this.mainMenuHelpAbout = new System.Windows.Forms.ToolStripMenuItem();
      this.mainSplitter = new System.Windows.Forms.SplitContainer();
      this.inputBox = new System.Windows.Forms.RichTextBox();
      this.outputSplitter = new System.Windows.Forms.SplitContainer();
      this.goalBox = new System.Windows.Forms.RichTextBox();
      this.outputBox = new System.Windows.Forms.RichTextBox();
      this.mainMenu.SuspendLayout();
      this.mainSplitter.Panel1.SuspendLayout();
      this.mainSplitter.Panel2.SuspendLayout();
      this.mainSplitter.SuspendLayout();
      this.outputSplitter.Panel1.SuspendLayout();
      this.outputSplitter.Panel2.SuspendLayout();
      this.outputSplitter.SuspendLayout();
      this.SuspendLayout();
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
      this.mainMenu.Size = new System.Drawing.Size(502, 24);
      this.mainMenu.TabIndex = 0;
      this.mainMenu.Text = "mainMenu";
      // 
      // mainMenuFile
      // 
      this.mainMenuFile.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mainMenuFileExit});
      this.mainMenuFile.Name = "mainMenuFile";
      this.mainMenuFile.Size = new System.Drawing.Size(35, 20);
      this.mainMenuFile.Text = "&File";
      // 
      // mainMenuFileExit
      // 
      this.mainMenuFileExit.Name = "mainMenuFileExit";
      this.mainMenuFileExit.Size = new System.Drawing.Size(103, 22);
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
      // 
      // mainMenuEditRedo
      // 
      this.mainMenuEditRedo.Name = "mainMenuEditRedo";
      this.mainMenuEditRedo.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Y)));
      this.mainMenuEditRedo.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditRedo.Text = "&Redo";
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
      // 
      // mainMenuEditCopy
      // 
      this.mainMenuEditCopy.Name = "mainMenuEditCopy";
      this.mainMenuEditCopy.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.C)));
      this.mainMenuEditCopy.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditCopy.Text = "&Copy";
      // 
      // mainMenuEditPaste
      // 
      this.mainMenuEditPaste.Name = "mainMenuEditPaste";
      this.mainMenuEditPaste.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.V)));
      this.mainMenuEditPaste.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditPaste.Text = "&Paste";
      // 
      // mainMenuEditDelete
      // 
      this.mainMenuEditDelete.Name = "mainMenuEditDelete";
      this.mainMenuEditDelete.ShortcutKeys = System.Windows.Forms.Keys.Delete;
      this.mainMenuEditDelete.Size = new System.Drawing.Size(167, 22);
      this.mainMenuEditDelete.Text = "&Delete";
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
      // 
      // mainMenuTac
      // 
      this.mainMenuTac.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mainMenuTacClear,
            this.mainMenuTacRestart});
      this.mainMenuTac.Name = "mainMenuTac";
      this.mainMenuTac.Size = new System.Drawing.Size(36, 20);
      this.mainMenuTac.Text = "&Tac";
      // 
      // mainMenuTacClear
      // 
      this.mainMenuTacClear.Name = "mainMenuTacClear";
      this.mainMenuTacClear.Size = new System.Drawing.Size(121, 22);
      this.mainMenuTacClear.Text = "&Clear";
      this.mainMenuTacClear.Click += new System.EventHandler(this.mainMenuTacClear_Click);
      // 
      // mainMenuTacRestart
      // 
      this.mainMenuTacRestart.Name = "mainMenuTacRestart";
      this.mainMenuTacRestart.Size = new System.Drawing.Size(121, 22);
      this.mainMenuTacRestart.Text = "&Restart";
      this.mainMenuTacRestart.Click += new System.EventHandler(this.mainMenuTacRestart_Click);
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
      // 
      // mainSplitter
      // 
      this.mainSplitter.Dock = System.Windows.Forms.DockStyle.Fill;
      this.mainSplitter.Location = new System.Drawing.Point(0, 24);
      this.mainSplitter.Name = "mainSplitter";
      // 
      // mainSplitter.Panel1
      // 
      this.mainSplitter.Panel1.Controls.Add(this.inputBox);
      // 
      // mainSplitter.Panel2
      // 
      this.mainSplitter.Panel2.Controls.Add(this.outputSplitter);
      this.mainSplitter.Size = new System.Drawing.Size(502, 242);
      this.mainSplitter.SplitterDistance = 303;
      this.mainSplitter.TabIndex = 1;
      // 
      // inputBox
      // 
      this.inputBox.Dock = System.Windows.Forms.DockStyle.Fill;
      this.inputBox.Location = new System.Drawing.Point(0, 0);
      this.inputBox.Name = "inputBox";
      this.inputBox.ScrollBars = System.Windows.Forms.RichTextBoxScrollBars.ForcedVertical;
      this.inputBox.Size = new System.Drawing.Size(303, 242);
      this.inputBox.TabIndex = 0;
      this.inputBox.Text = "";
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
      this.outputSplitter.Size = new System.Drawing.Size(195, 242);
      this.outputSplitter.SplitterDistance = 92;
      this.outputSplitter.TabIndex = 0;
      // 
      // goalBox
      // 
      this.goalBox.Dock = System.Windows.Forms.DockStyle.Fill;
      this.goalBox.Location = new System.Drawing.Point(0, 0);
      this.goalBox.Name = "goalBox";
      this.goalBox.ReadOnly = true;
      this.goalBox.Size = new System.Drawing.Size(195, 92);
      this.goalBox.TabIndex = 0;
      this.goalBox.Text = "";
      // 
      // outputBox
      // 
      this.outputBox.Dock = System.Windows.Forms.DockStyle.Fill;
      this.outputBox.Location = new System.Drawing.Point(0, 0);
      this.outputBox.Name = "outputBox";
      this.outputBox.ReadOnly = true;
      this.outputBox.Size = new System.Drawing.Size(195, 146);
      this.outputBox.TabIndex = 0;
      this.outputBox.Text = "";
      // 
      // IdeForm
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(502, 266);
      this.Controls.Add(this.mainSplitter);
      this.Controls.Add(this.mainMenu);
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
    private System.Windows.Forms.RichTextBox inputBox;
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
  }
}

