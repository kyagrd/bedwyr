<?php
function inc($file, $hidden=true){
?>
    <figure>
      <figcaption>
      <a>
        <span class="caret down" style="display:<?=($hidden?'default':'none;')?>;"></span>
        <span class="caret up" style="display:<?=($hidden?'none':'default;')?>;"></span>
        <?=htmlspecialchars($file)?>
      </a>
      [<a href="<?=$file?>">thm</a>]
      </figcaption>
      <pre style="display: <?=($hidden?'none':'default;')?>;" class='vimCodeElement'>
<?php include($file.'.html')?>
      </pre>
    </figure>
<?php
}
?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" lang="en" xml:lang="en">
  <head>
    <title>Bedwyr</title>
    <link href="../../slimmer.css" rel="stylesheet" type="text/css"/>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8"/>
    <style>
td>figure { margin: 1em; font-size: small; }
tr>th {text-align: left; }
tr>td>figure>figcaption {text-align: right; }

.caret {
  position: relative;
  cursor: pointer;
  padding-right: 1em;
}
.caret:before {
  content: '';
  position: absolute;
  top: 0.4em;
  border: 0.4em solid transparent;
}
.caret.down:before {
  border-top-color: grey;
  border-bottom-width: 0em;
}
.caret.up:before {
  border-bottom-color: grey;
  border-top-width: 0em;
}

.vimCodeElement { overflow-x: auto; white-space: pre; font-family: monospace; color: #ffffff; background-color: #000000; padding: 1em; }
.vimCodeElement * { font-size: 1em; }
.vimCodeElement .Comment { color: #626262; }
.vimCodeElement .Special { color: #ffd787; }
.vimCodeElement .PreProc { color: #d7afaf; }
.vimCodeElement .String { color: #5fffaf; background-color: #000000; padding-bottom: 1px; }
.Identifier { color: #5fafd7; font-weight: bold; }
.Statement { color: #5fd75f; font-weight: bold; }
.Type { color: #d787ff; font-weight: bold; }
    </style>
    <script src="http://code.jquery.com/jquery-2.1.1.min.js"></script>
    <script>
$(function(){
  $('.vimCodeElement').parent().find('figcaption>a:first-child').click(function(){
    $(this).children('.caret').toggle();
    $(this).parent().parent().children('pre.vimCodeElement').toggle(500);
  });
  $('th>h3>a.view:first-child').click(function(){
    $(this).parent().parent().parent().next().find('pre.vimCodeElement:visible').each(function(){
      $(this).prev().children().children().toggle();
      $(this).toggle(500);
    });
    $(this).parent().parent().find('pre.vimCodeElement').toggle(500);
  });
});
    </script>
  </head>

  <body>
    <h1>Bedwyr:<br/>
      Proof certificates for model checking
    </h1>

    <p>This page provides examples illustrating the framework presented
    in the paper <em>A framework for proof certificates in model
      checking</em> [<a
      href="http://www.lix.polytechnique.fr/~dale/papers/pcmc-draft.pdf">pdf</a>]
    by <a href="http://www.lix.polytechnique.fr/Labo/Dale.Miller/">Dale
      Miller</a> and
    <a href="http://www.lix.polytechnique.fr/~heath/">Quentin Heath</a>.
    Each example demonstrates the use of one FPC
    (<em>foundational proof certificate</em>).</p>

    <p>The definition files (usually <code>*.def</code> or
    <code>*.thm</code>) can be run with the
    <a href="../#download">Bedwyr system</a>, for example with the
    command <code>bedwyr -t -I &lt;NAME&gt;/harness.thm</code>.

    <p>The files presented on this page are available as an archive
    (<a href="pcmc-examples.tbz">tbz</a>, <a href="pcmc-examples.zip">zip</a>).</p>

    <h2>Harness</h2>

    A testing harness is modelled after
    <code>generic/harness.thm</code>.  It loads
    <ul>
      <li>the core of the framework (<code>logic.thm</code>,
        <code>cert-sig.thm</code> and, especially,
        <code>kernel.thm</code>)</li>
      <li>the modular part of the framework (<code>*/fpc.thm</code>)</li>
      <li>definitions to be used in test assertions
        (<code>*/examples.thm</code>)</li>
    </ul>
    As there are no separate signature files, the order is important:
    the FPC must be loaded before the kernel, but after the logic and
    the certificates.
<?php inc('generic/harness.thm')?>

    For simplicity reasons, the logic defined in <code>logic.thm</code>
    only uses abstraction on one type, <code>i</code>, and Bedwyr's
    polymorphism is unused; these details may change in future versions
    of the framework.
    <code>cert-sig.thm</code> defines common certificate constructors
    may be used by any FPC.
<?php inc('logic.thm')?>
<?php inc('cert-sig.thm')?>

    The file <code>generic/fpc.thm</code> contains a basic example of
    FPC, i.e. defined predicates for each clerks and experts, which use
    the common certificates constructors from <code>cert-sig.thm</code>.
    It is only a starting point for writing new FPCs.
    The FPCs from the provided examples are mostly identical to this
    generic FPC; the differences are marked by <code>% XXX</code>
    comments in the source files.
<?php inc('generic/fpc.thm')?>

    The kernel is a direct implementation of the inference rules.
    Thanks to the simple settings chosen ("switchable formulas"), the
    treatment of object-level implication can be done without Bedwyr's
    meta-level implication.  The latter is only used in the case of
    unification.
<?php inc('kernel.thm')?>


    <h2>Examples from the paper</h2>

    <table style="width: 100%; display: block;">

      <tr>
        <th colspan="3">
          <h3>
            Reachability
            [<a class="view"><span>hide all</span></a>]
          </h3>
        </th>
      </tr>
      <tr style="vertical-align: top;">
        <td>
<?php inc('reachable/fpc.thm')?>
<?php inc('adj.thm')?>
        </td>
        <td>
<?php inc('reachable/examples.thm')?>
        </td>
        <td>
<?php inc('reachable/harness.thm')?>
        </td>
      </tr>

      <tr>
        <th colspan="3">
          <h3>
            Non-reachability
            [<a class="view"><span>hide all</span></a>]
          </h3>
        </th>
      </tr>
      <tr style="vertical-align: top;">
        <td>
<?php inc('unreachable/fpc.thm')?>
        </td>
        <td>
<?php inc('unreachable/examples.thm')?>
        </td>
        <td>
<?php inc('unreachable/harness.thm')?>
        </td>
      </tr>

      <tr>
        <th colspan="3">
          <h3>
            Simulation
            [<a class="view"><span>hide all</span></a>]
          </h3>
        </th>
      </tr>
      <tr style="vertical-align: top;">
        <td>
<?php inc('sim/fpc.thm')?>
<?php inc('lts.thm')?>
        </td>
        <td>
<?php inc('sim/examples.thm')?>
        </td>
        <td>
<?php inc('sim/harness.thm')?>
        </td>
      </tr>

      <tr>
        <th colspan="3">
          <h3>
            Non-(bi)simulation
            [<a class="view"><span>hide all</span></a>]
          </h3>
        </th>
      </tr>
      <tr style="vertical-align: top;">
        <td>
<?php inc('nonsim/fpc.thm')?>
        </td>
        <td>
<?php inc('nonsim/examples.thm')?>
        </td>
        <td>
<?php inc('nonsim/harness.thm')?>
        </td>
      </tr>

    </table>

    <p>Last modifed: June 2015.</p>
  </body>
</html>
