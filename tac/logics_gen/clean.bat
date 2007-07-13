@echo off
echo Cleaning logics_gen...
ocamake -clean *.ml*
ocamake -clean *.ml* -opt
echo Done.
