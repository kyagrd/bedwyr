using System;
using System.Collections.Generic;
using System.Text;
using System.Diagnostics;
using System.Xml;

namespace StickyTaci
{
  public class Taci
  {
    public static string CLEAR = "#clear";
    public static string EXIT = "#exit";
    public static string HELP = "#help";
    public static string INCLUDE = "#include";
    public static string LOGICS = "#logics";
    public static string OPEN = "#open";
    public static string RESET = "#reset";
    public static string TACTICALS = "#tacticals";
    
    bool m_Fail = false;
    public delegate void IOHandler(Taci instance, string data);
    public event IOHandler Output;
    public event IOHandler Goal;
    public event IOHandler Error;
    public event IOHandler Command;
    public event IOHandler Tactical;

    private Process m_Taci = null;
    private string m_Data;
    private string m_Path;
    private string m_Arguments;
    
    public Taci(string path, string arguments)
    {
      System.Diagnostics.Debug.WriteLine("Executing '" + path + arguments + "'.");
      m_Path = path;
      m_Arguments = arguments;
    }

    public void Restart()
    {
      if(m_Fail)
        return;

      if(m_Taci != null)
      {
        m_Taci.Kill();
        m_Taci.Close();
      }

      ProcessStartInfo si = new ProcessStartInfo(m_Path, m_Arguments);
      si.UseShellExecute = false;
      si.RedirectStandardInput = true;
      si.RedirectStandardOutput = true;

      m_Taci = new Process();
      m_Taci.StartInfo = si;
      m_Taci.OutputDataReceived += new DataReceivedEventHandler(Taci_OutputDataReceived);
      m_Taci.Exited += new EventHandler(Taci_Exited);
      m_Taci.EnableRaisingEvents = true;

      if(m_Taci.Start())
        m_Taci.BeginOutputReadLine();
      else
        m_Fail = true;
      return;
    }

   
    public void Write(string s)
    {
      m_Taci.StandardInput.WriteLine(s);
    }

    public void Exit()
    {
      m_Taci.EnableRaisingEvents = false;
      m_Taci.Close();
      return;
    }

    private void Taci_Exited(object sender, EventArgs e)
    {
      if(sender == m_Taci)
      {
        m_Fail = true;
        m_Taci.Close();
        m_Taci = null;
        Restart();
      }
    }

    private void ProcessOutput()
    {
      try
      {
        XmlDocument doc = new XmlDocument();
        doc.LoadXml("<xml>" + m_Data + "</xml>");
        ParseOutput(doc);
        m_Data = "";
      }
      catch(XmlException)
      {
        System.Diagnostics.Debug.WriteLine("Unable to parse: " + m_Data);
        return;
      }
    }
    private void Taci_OutputDataReceived(object sender, DataReceivedEventArgs e)
    {
      m_Data += e.Data;
      ProcessOutput();
    }

    private void ParseOutput(XmlDocument doc)
    {
      XmlNodeList outputs = doc.GetElementsByTagName("Output");
      if(outputs.Count == 0)
      {
        System.Diagnostics.Debug.WriteLine("No <Output> nodes.");
        return;
      }

      foreach(XmlNode output in outputs)
      {
        XmlAttribute type = output.Attributes["type"];
        XmlAttribute text = output.Attributes["text"];
        if(type != null && text != null)
        {
          Notify(type.Value, text.Value);
        }
        else
        {
          System.Diagnostics.Debug.WriteLine("Invalid <Output> node.");
        }
      }
    }

    private string Unescape(string s)
    {
      s = s.Replace("&lt;", "<");
      s = s.Replace("&gt;", ">");
      s = s.Replace("&amp;", "&");
      s = s.Replace("&quot;", "\"");
      s = s.Replace("&apos;", "'");
      return System.Text.RegularExpressions.Regex.Unescape(s);
    }

    private void Notify(string type, string text)
    {
      if(type == "output" && Output != null)
      {
        Output(this, Unescape(text));
      }
      else if(type == "goal" && Goal != null)
      {
        Goal(this, Unescape(text));
      }
      else if(type == "error" && Error != null)
      {
        Error(this, Unescape(text));
      }
      else if(type == "command" && Command != null)
      {
        Command(this, Unescape(text));
      }
      else if(type == "tactical" && Tactical != null)
      {
        Tactical(this, Unescape(text));
      }
    }

  }
}
