@echo off
ocamake -clean *.ml* Propositional/*.ml* Nologic/*.ml* Firstorder/*.ml* ../../bedwyr/src/ndcore/*.ml*
echo Done.
