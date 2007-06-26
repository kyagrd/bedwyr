@echo off
ocamake -clean *.ml* Propositional/*.ml* Nologic/*.ml* Firstorder/*.ml* ndcore/*.ml*
del *.cm*
del *.obj
del ndcore\*.cm*
del ndcore\*.obj
del Propositional\*.cm*
del Propositional\*.obj
del Nologic\*.cm*
del Nologic\*.obj
del Firstorder\*.cm*
del Firstorder\*.obj
echo Done.
