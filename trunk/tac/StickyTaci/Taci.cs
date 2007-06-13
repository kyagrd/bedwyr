using System;
using System.Collections.Generic;
using System.Text;
using System.Diagnostics;
using System.Xml;

namespace StickyTaci
{
  public class Taci
  {
    public delegate void OutputHandler(Taci instance, string data);
    public event OutputHandler Output;
    public event OutputHandler Goal;
    public event OutputHandler Error;
    public event OutputHandler Command;

    private Process m_Taci = null;
    private string m_Data;
    private string m_Path;
    private string m_Arguments;
    
    public Taci(string path, string arguments)
    {
      m_Path = path;
      m_Arguments = arguments;

      Restart();
    }

    public void Restart()
    {
      if(m_Taci != null)
      {
        m_Taci.Kill();
        m_Taci.Close();
      }

      m_Taci = new Process();
      m_Taci.StartInfo.FileName = m_Path;
      m_Taci.StartInfo.Arguments = m_Arguments;
      m_Taci.StartInfo.UseShellExecute = false;
      m_Taci.StartInfo.RedirectStandardInput = true;
      m_Taci.StartInfo.RedirectStandardOutput = true;

      m_Taci.OutputDataReceived += new DataReceivedEventHandler(Taci_OutputDataReceived);
      m_Taci.Exited += new EventHandler(Taci_Exited);
      m_Taci.EnableRaisingEvents = true;

      m_Taci.Start();
      m_Taci.BeginOutputReadLine();
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
        doc.LoadXml(m_Data);
        m_Data = "";
        ParseOutput(doc);
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
      return s.Replace("\\n", "\n");
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
    }

  }
}
