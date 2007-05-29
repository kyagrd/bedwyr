@echo off
ocamake -clean *.ml* Propositional\*.ml* Nologic\*.ml*
del *.cm*
del *.obj
del Propositional\*.cm*
del Propositional\*.obj
del Nologic\*.cm*
del Nologic\*.obj
echo Done.
