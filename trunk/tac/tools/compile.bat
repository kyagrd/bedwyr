rem Builds tactex.exe; assumes that xml-light is installed somewhere that O'Caml can find it.
@echo off
echo Building tactex...
ocamlc xml-light.cma str.cma tactex.ml -o ..\bin\tactex.exe
echo Done.
