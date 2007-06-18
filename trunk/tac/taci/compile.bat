del logics_gen.cm*
ocamake *.ml*  Nologic/*.ml* Propositional/*.ml* Firstorder/*.ml* ../../bedwyr/src/ndcore/term.ml* ../../bedwyr/src/ndcore/norm.ml* ../../bedwyr/src/ndcore/pprint.ml* ../../bedwyr/src/ndcore/unify.ml* ../../bedwyr/src/ndcore/index.ml* str.cma -epp -o %1
xcopy %1 %2 /Y
