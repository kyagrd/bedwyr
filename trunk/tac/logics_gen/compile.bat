@echo off
echo Compiling logics_gen...
ocamake *.ml* -epp -opt -o %1
xcopy %1 %2 /Y
%2 --input "bin\Logics.in" --output "..\taci\Logics_gen"
echo Done.
