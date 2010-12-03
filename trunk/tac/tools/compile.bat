rem Builds tactex.exe and mod2def.exe; assumes that xml-light is installed somewhere that O'Caml can find it.
@echo off
echo Building tools...
ocamake xml-light.cma str.cma tactex.ml -epp -o ..\bin\tactex.exe
ocamake mod2def.ml str.cma ..\taci\properties.ml* ..\taci\option.ml* ..\taci\output.ml* ..\taci\listutils.ml* ..\taci\Firstorder\LP\*.ml* -epp -o ..\bin\mod2def.exe
echo Done.
