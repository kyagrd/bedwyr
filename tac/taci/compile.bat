@echo off
echo Compiling...
del logics_gen.cm*
ocamake *.ml*  Nologic/*.ml* Propositional/*.ml* Firstorder/*.ml* Firstorder/LP/*.ml* ../../bedwyr/src/ndcore/*.ml* str.cmxa unix.cmxa -epp -opt -lp "-cclib 104857600" -lp "-cclib /F" -o %1
xcopy %1 %2 /Y
echo Done.

