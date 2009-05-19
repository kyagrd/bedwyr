rem Deletes intermediate files.
@echo offf
echo Cleaning...
ocamake xml-light.cmxa str.cmxa tactex.ml -opt -epp -o ..\bin\tactex.exe -clean
ocamake mod2def.ml ..\taci\output.ml* ..\taci\listutils.ml* ..\taci\Firstorder\LP\*.ml* -opt -epp -o ..\bin\mod2def.exe -clean
echo Done.
