rem Builds tactex.exe and mod2def.exe; assumes that xml-light is installed somewhere that O'Caml can find it.
@echo off
echo Building tools...
ocamake xml-light.cmxa str.cmxa tactex.ml -opt -epp -o ..\bin\tactex.exe
ocamake mod2def.ml ..\taci\output.ml* ..\taci\listutils.ml* ..\taci\Firstorder\LP\*.ml* -opt -epp -o ..\bin\mod2def.exe
echo Done.
