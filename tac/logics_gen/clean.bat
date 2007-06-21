@echo off
echo Cleaning logics_gen...
ocamake -clean *.ml*
del *.cm*
del *.obj
echo Done.
