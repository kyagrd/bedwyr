@echo off
echo Compiling logics_gen...
ocamake *.ml* -epp -opt -o %1
echo Done.
