@echo off
ocamake -clean *.ml* Propositional/*.ml* Nologic/*.ml* Firstorder/*.ml* ../../bedwyr/src/ndcore/*.ml*
ocamake -clean *.ml* Propositional/*.ml* Nologic/*.ml* Firstorder/*.ml* ../../bedwyr/src/ndcore/*.ml* -opt
echo Done.
