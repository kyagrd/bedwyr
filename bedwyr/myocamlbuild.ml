open Ocamlbuild_plugin ;;

let print_info f =
  Format.fprintf Format.std_formatter
    "@[<hv 2>Tags for file %s:@ %a@]@." f
    Tags.print (tags_of_pathname f)

(*
 * ocamlbuild src/ndcore/test.byte \
 * && ./_build/src/ndcore/test.byte
 *
 * ocamlbuild src/main.byte \
 * && ./_build/src/main.byte
 *)

let _ =
  dispatch begin function
    | After_rules ->
        flag ["ocaml" ; "compile"] (A "-annot") ;
        flag ["ocaml" ; "compile"] (S [A "-warn-error" ; A "A"]) ;
        flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
        (* flag ["ocaml" ; "link" ; "program"] (A "-linkpkg") ; *)

        ocaml_lib "src/ndcore/ndcore" ;
        ocaml_lib "src/oUnit/oUnit" ;

        ()
    | _ -> ()
  end

