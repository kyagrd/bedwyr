del logics_gen.cm*
ocamake *.ml*  Nologic/*.ml* Propositional/*.ml* Firstorder/*.ml* ../../bedwyr/src/ndcore/*.ml* str.cmxa unix.cmxa -epp -opt -v -lp "-cclib 10485760" -lp "-cclib /F" -o %1
xcopy %1 %2 /Y
