del logics_gen.cm*
ocamake *.ml*  Nologic/*.ml* Propositional/*.ml* Firstorder/*.ml* ../../bedwyr/src/ndcore/*.ml* str.cma unix.cma -epp -g -o %1
xcopy %1 %2 /Y
