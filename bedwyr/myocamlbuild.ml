open Ocamlbuild_plugin ;;

let _ =
  dispatch begin function
    | After_rules ->
        flag ["ocaml" ; "compile"] (A "-annot") ;
        flag ["ocaml" ; "compile"] (S [A "-warn-error" ; A "A"]) ;
        flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
        (* flag ["ocaml" ; "link" ; "program"] (A "-linkpkg") ; *)

        (* add "~extern:true" when using external libs *)
        ocaml_lib "src/oUnit/oUnit" ;

        ocaml_lib "src/ndcore/ndcore" ;
        ocaml_lib "src/batyping/batyping" ;
        ocaml_lib "src/input/input" ;
        ocaml_lib "src/prover/prover" ;

        ()
    | _ -> ()
  end

