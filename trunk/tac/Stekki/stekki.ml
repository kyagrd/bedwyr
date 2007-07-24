(*****************************************************************************
 * stekki.ml -- a simple GUI for taci                                        *
 *                                                                           *
 * ocamlopt -I +labltk str.cmxa unix.cmxa labltk.cmxa stekki.ml -o stekki    * 
 *****************************************************************************)

let debug = ref false
let filename = ref None

let () =
  Arg.parse
    [ "--debug", Arg.Set debug, "Turn debugging on." ]
    (fun f -> filename := Some f)
    "Usage: stekki [--debug] <filename>"

let filename =
  match !filename with
    | None ->
        Printf.printf "Usage: stekki <filename>\n" ;
        Printf.printf "The file is used to load/save the script.\n" ;
        exit 1
    | Some f -> f

let logic =
  if Str.string_match (Str.regexp ".*\\.\\(.*\\)\\.tac") filename 0 then
    Str.matched_group 1 filename
  else
    "muLJ"

(* ********** GENERAL TK CONFIG ********** *)

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
    Option.add ~path:"*Label.font" "guifont" ;
    Option.add ~path:"*Button.font" "guifont" ;

    Wm.title_set w (Printf.sprintf "Stekki: %s" filename) ;
    w

(* ********** LAYOUT ********** *)

let before,after,output,reset,load,save =
  let output  =
    Text.create ~width:80 window in

  let left    = Frame.create window in

  let before_frame = Frame.create left in
  let after_frame  = Frame.create left in
  let before  = Listbox.create ~width:80 before_frame in
  let after   = Text.create ~width:80 after_frame in

  let buttons = Frame.create left in
  let reset   = Button.create ~text:"Reset" buttons in
  let load    = Button.create ~text:"Load" buttons in
  let save    = Button.create ~text:"Save" buttons in

  let output_scroll =
    let scroll = Scrollbar.create window ~command:(Text.yview output) in
      Text.configure output ~yscrollcommand:(Scrollbar.set scroll) ;
      scroll
  in
  let after_scroll =
    let scroll = Scrollbar.create after_frame ~command:(Text.yview after) in
      Text.configure after ~yscrollcommand:(Scrollbar.set scroll) ;
      scroll
  in
  let before_scroll =
    let scroll =
      Scrollbar.create before_frame ~command:(Listbox.yview before)
    in
      Listbox.configure before ~yscrollcommand:(Scrollbar.set scroll) ;
      scroll
  in

    Text.configure ~state:`Disabled output ;

    (* Pack the output on the right. *)
    pack ~side:`Right ~fill:`Y ~expand:true [output_scroll] ;
    pack ~side:`Right ~fill:`Both ~expand:true [output] ;

    (* Pack in the left frame. *)
    pack ~side:`Right ~expand:true ~fill:`Y    [before_scroll] ;
    pack ~side:`Right ~expand:true ~fill:`Both [before] ;
    pack ~side:`Top   ~expand:true ~fill:`X [before_frame] ;
    pack ~side:`Right ~expand:true ~fill:`Y    [after_scroll] ;
    pack ~side:`Right ~expand:true ~fill:`Both [after] ;
    pack ~side:`Top   ~expand:true ~fill:`Both [after_frame] ;

    pack ~side:`Left [reset;load;save] ;
    pack [buttons] ;

    pack ~side:`Left ~fill:`Both ~expand:true [left] ;

    before,after,output,reset,load,save

(* ********** EXTERNAL PROCESS ********** *)

let proc_in,proc_out,reload =
  let rin,win = Unix.pipe () in
  let rout,wout = Unix.pipe () in
  let pid = ref None in
  let reload () =
    begin match !pid with
      | None -> ()
      | Some p -> Unix.kill p 9 ; ignore (Unix.wait ())
    end ;
    Text.configure ~state:`Normal output ;
    Text.delete output ~start:(`Linechar (0,0),[]) ~stop:(`End,[]) ;
    Text.configure ~state:`Disabled output ;
    pid := Some (Unix.create_process
                   "taci"
                   (if !debug then
                      [|"taci";"--debug";"--logic";logic|]
                    else
                      [|"taci";"--logic";logic|])
                   rin wout Unix.stderr)
  in
    reload () ;
    win,rout,reload

(* ********** READ FROM THE PROCESS ********** *)

let startup_delay = 1.
let len = 80
let buf = String.make len 'x'

let clear_on_read = ref false

let read_from_process () =
  let len = Unix.read proc_out buf 0 len in
  let s = String.sub buf 0 len in
  let s = Str.global_replace (Str.regexp "\r") "" s in
    (* TODO: remove a command from the list on error. *)
    Text.configure ~state:`Normal output ;
    if !clear_on_read then begin
      Text.delete output ~start:(`Linechar (0,0),[]) ~stop:(`End,[]) ;
      clear_on_read := false
    end ;
    Text.insert ~index:(`End,[]) ~text:s output ;
    Text.configure ~state:`Disabled output

let () =
  Fileevent.add_fileinput ~fd:proc_out ~callback:read_from_process

let () =
  (** The initial available data on proc_out isn't obtained via the file event
    * handler that we set up. *)
  let rec f delay =
    let readlist,_,_ = Unix.select [proc_out] [] [] delay in
      match readlist with
        | [_] ->
            read_from_process () ;
            f 0.1
        | _ -> ()
  in
    f startup_delay

let clear_on_read () = clear_on_read := true

(* ********** WRITE TO THE PROCESS ********** *)

let write_process line =
  let len = String.length line in
    clear_on_read () ;
    assert (len = Unix.write proc_in line 0 len)

let eval_command () =
  (** Find the end of the next command. *)
  let start = `Linechar (0,0), [] in
    match
      try
        Some (Text.search ~pattern:".\n" ~switches:[]
                ~start ~stop:(`End,[])
                after)
      with _ -> None
    with
      | None -> ()
      | Some (`Linechar (l,c)) ->
          let command = Text.get after ~start ~stop:(`Linechar (l,c+1),[]) in
            Text.delete after ~start ~stop:(`Linechar (l+1,0),[]) ;
            Listbox.insert before ~index:`End ~texts:[command] ;
            Listbox.yview before (`Moveto 1.) ;
            write_process (command^"\n")

let undo () =
  if Listbox.size before = 0 then false else
    let command = Listbox.get before ~index:`End in
      Listbox.delete before ~first:`End ~last:`End ;
      Text.insert after ~index:(`Linechar (0,0),[]) ~text:(command^"\n") ;
      write_process "#undo.\n" ;
      true

let () =
  List.iter
    (fun e ->
       bind after ~events:[e] ~action:(fun _ -> eval_command ()))
    [`Modified ([`Alt],`KeyPressDetail "Down");
     `Modified ([`Alt],`KeyPressDetail "Return")] ;
  bind after ~events:[`Modified ([`Alt],`KeyPressDetail "Up")]
    ~action:(fun _ -> ignore (undo ()))

(* ********** BUTTONS ********** *)

let on_reset () =
  while undo () do () done ;
  reload ()

let warn message f =
  if
    1 = Dialog.create ~parent:window ~title:"Warning" ~message
          ~buttons:["Cancel";"OK"] ~default:0 ()
  then f ()

let on_load () =
  while undo () do () done ;
  reload () ;
  let file = open_in filename in
  let len = in_channel_length file in
  let text = String.make len 'x' in
    really_input file text 0 len ;
    let text = Str.global_replace (Str.regexp "\r") "" text in
      close_in file ;
      Text.delete after ~start:(`Linechar (0,0),[]) ~stop:(`End,[]) ;
      Text.insert ~index:(`End,[]) ~text after

let on_save () =
  while undo () do () done ;
  reload () ;
  let text = Text.get ~start:(`Linechar (0,0),[]) ~stop:(`End,[]) after in
  let file = open_out filename in
    output_string file text ;
    close_out file

let () =
  let load_msg =
    Printf.sprintf "Reloading %S will loose unsaved changes!" filename
  in
  let save_msg =
    Printf.sprintf "Overwrite %S?" filename
  in
    bind reset ~events:[`ButtonPress] ~action:(fun _ -> on_reset ()) ;
    bind load  ~events:[`ButtonPress] ~action:(fun _ -> warn load_msg on_load) ;
    bind save  ~events:[`ButtonPress] ~action:(fun _ -> warn save_msg on_save) ;
    if Sys.file_exists filename then
      on_load ()

let () = mainLoop ()
