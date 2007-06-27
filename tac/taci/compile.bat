del logics_gen.cm*
ocamake *.ml*  Nologic/*.ml* Propositional/*.ml* Firstorder/*.ml* Linear/*.ml* ndcore/*.ml* str.cma -epp -o %1
xcopy %1 %2 /Y
