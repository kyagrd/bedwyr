using System;
using System.Collections.Generic;
using System.Windows.Forms;

namespace StickyTaci
{
  static class StickyTaci
  {
    /// <summary>
    /// The main entry point for the application.
    /// </summary>
    [STAThread]
    static void Main()
    {
      Application.EnableVisualStyles();
      Application.SetCompatibleTextRenderingDefault(false);

      IdeCtrl ctrl = new IdeCtrl();
      IdeForm frm = new IdeForm(ctrl);
      ctrl.Form = frm;
      Application.Run(frm);
    }
  }
}