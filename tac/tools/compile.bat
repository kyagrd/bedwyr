@echo off
echo Building tactex...
ocamlc 	xml-light.cma str.cma tactex.ml -o ..\bin\tactex.exe
echo Done.
