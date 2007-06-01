ocamake *.ml* Nologic\*.ml* Propositional\*.ml* str.cmxa -epp -opt -o %1
xcopy %1 %2 /Y
