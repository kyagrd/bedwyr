(* stekki.ml -- an experimental simple GUI for taci
 *
 * Run with: ocaml -I +labltk labltk.cma stekki.ml
 *)

open Tk

let get_font ~size tag choices =
  let all = Font.families () in
  let rec find ch =
    match ch with
      | [] -> None
        | f::tail ->
            ( try Some (List.find (( = ) f) all)
              with Not_found -> find tail ) in
    match find choices with
      | None -> Font.create ~name:tag ~size ()
      | Some fam -> Font.create ~name:tag ~family:fam ~size ()

let window =
  let w = openTk () in

    (* Some general settings *)
    Encoding.system_set "utf-8" ;
    ignore (get_font "guifont" ~size:8
              ["sans"; "verdana"; "lucida"; "bitstream vera sans"]) ;
    Option.add ~path:"*Separator.borderWidth" "5";
    Option.add ~path:"*Separator.background" "black";
    Option.add ~path:"*Label.font" "guifont" ;

    Wm.title_set w "Stekki" ;
    w

let before,input,after,output =
  let txt   = Text.create ~width:80 window in
  let left  = Frame.create window in
  let before = Listbox.create left in
  let after  = Listbox.create left in
  let input  = Entry.create   left in
    Text.configure ~state:`Disabled txt ;
    pack ~fill:`Both ~expand:true [before] ;
    pack ~fill:`X [input] ;
    pack ~fill:`Both ~expand:true [after] ;
    pack ~side:`Left ~fill:`Both ~expand:true [left] ;
    pack ~side:`Right ~fill:`Both ~expand:true [txt] ;
    before,input,after,txt

(** The external process *)

let proc_pid,proc_in,proc_out =
  let rin,win = Unix.pipe () in
  let rout,wout = Unix.pipe () in
  let pid =
    Unix.create_process "ocaml" [|"ocaml"|] Unix.stdin wout Unix.stderr
  in
    Unix.close rin ; Unix.close wout ;
    pid,win,rout

(** INPUT *)

let on_input () =
  let line = Entry.get input in
    Entry.delete_range input ~start:(`At 0) ~stop:`End ;
    Listbox.insert before ~index:`End ~texts:[line] ;
    let line = line ^ "\n" in
    let len = String.length line in
      assert (len = Unix.write proc_in line 0 len) ;
      assert (10 = Unix.write proc_in "\n\n\n\n\n\n\n\n\n\n" 0 10) ;
      assert (len = Unix.write Unix.stdout line 0 len) ;
      flush_all ()

let () =
  bind input ~events:[`KeyReleaseDetail "Return"]
    ~action:(fun _ -> on_input ())

(** OUTPUT *)

let startup_delay = 1.
let len = 80
let buf = String.make len 'x'

let () =
  Fileevent.add_fileinput ~fd:Unix.stdin
    ~callback:(fun () ->
                 let len = Unix.read proc_out buf 0 len in
                 let s = String.sub buf 0 len in
                   Text.configure ~state:`Normal output ;
                   Text.insert ~index:(`End,[]) ~text:s output ;
                   Text.configure ~state:`Disabled output)

let () =
  (** The initial available data on proc_out isn't obtained via the file event
    * handler that we set up. *)
  let rec f delay =
    let readlist,_,_ = Unix.select [proc_out] [] [] delay in
      match readlist with
        | [_] ->
            let len = Unix.read proc_out buf 0 len in
            let s = String.sub buf 0 len in
              Printf.printf "Read %S\n%!" s ;
              Text.configure ~state:`Normal output ;
              Text.insert ~index:(`End,[]) ~text:s output ;
              Text.configure ~state:`Disabled output ;
              f 0.1
        | _ -> ()
  in
    f startup_delay

let () = mainLoop ()
