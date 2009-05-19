@echo off
echo Cleaning...
ocamake -clean *.ml* Propositional/*.ml* Nologic/*.ml* Firstorder/*.ml* Firstorder/LP/*.ml* ../../bedwyr/src/ndcore/*.ml*
ocamake -clean *.ml* Propositional/*.ml* Nologic/*.ml* Firstorder/*.ml* Firstorder/LP/*.ml* ../../bedwyr/src/ndcore/*.ml* -opt
echo Done.
