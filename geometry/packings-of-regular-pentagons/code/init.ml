(* 
Need to run ocamlfpu from
~/Desktop/interval directory

If starting *ocaml-toplevel*, 
start with ocamlfpu in *shell*
then rename buffer to *ocaml-toplevel*

#directory "/home/hasty/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/";;
#use "init.ml";;
*)

#directory "/home/hasty/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/";;

#use "topfind";;
#list;;

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };;

Sys.catch_break true;;


let use_file s =
  if Toploop.use_file Format.std_formatter s then ()
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;

let hol_expand_directory s =
  if s = "$$" then "$"
  else if String.length s <= 2 then s
  else if String.sub s 0 2 = "$$" then (String.sub s 1 (String.length s - 1))
  else s;;

let load_path = ref ["."; "$";
"/home/hasty/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/"];;

let loaded_files = ref [];;

let file_on_path p s =
  if not (Filename.is_relative s) then s else
  let p' = List.map hol_expand_directory p in
  let d = List.find (fun d -> Sys.file_exists(Filename.concat d s)) p' in
  Filename.concat (if d = "." then Sys.getcwd() else d) s;;

let load_on_path p s =
  let s' = file_on_path p s in
  let fileid = (Filename.basename s',Digest.file s') in
  (use_file s'; loaded_files := fileid::(!loaded_files));;

let loads s = load_on_path ["$"] s;;

let loadt s = load_on_path (!load_path) s;;

let needs s =
  let s' = file_on_path (!load_path) s in
  let fileid = (Filename.basename s',Digest.file s') in
  if List.mem fileid (!loaded_files)
  then Format.print_string("File \""^s^"\" already loaded\n") else loadt s;;

let reneeds s = loadt ( s);;

(* ------------------------------------------------------------------------- *)
(* Various tweaks to OCaml and general library functions.                    *)
(* ------------------------------------------------------------------------- *)

loadt "lib.ml";;


open Lib;;

(* load pent libraries *)


(*
type interval = {
  lo : float;
  hi : float;
};;
*)

exception Unstable;;  (* generally thrown when there is a divide by zero *)

exception Fatal;;  (* generally indicates an uncorrected bug *)


(* needs "informal_code/port_interval/interval.hl";; *)

open Interval;;





let tests = ref [];;

let mktest (s,f) = tests := (s,f) :: !tests;;

let gettest () = List.map fst !tests;;

let runtest s = 
  let f = List.assoc s !tests in (s,f ());;

let runalltest() = 
  map runtest (gettest());;

reneeds "pent.ml";;

runalltest();;

open Pent;;


reneeds "pent.ml";;
reneeds "pet.ml";;
reneeds "function_library.ml";;
reneeds "dimer.ml";;
(* deprecate dimer2.ml *)
reneeds "autodiff.ml";;
reneeds "meet-in-middle.ml";;
(* reneeds "scratch.ml";; *)
(* reneeds "hypotheses.ml";; *)
