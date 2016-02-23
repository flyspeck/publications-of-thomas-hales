(* ========================================================================= *)
(* Convenient library functions.                                             *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

module Lib = struct

  let (+) = Pervasives.(+);;
  let (-) = Pervasives.(-);;

let fail() = failwith "";;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

let curry f x y = f(x,y);;

let uncurry f(x,y) = f x y;;

(* ------------------------------------------------------------------------- *)
(* List basics.                                                              *)
(* ------------------------------------------------------------------------- *)

let hd l =
  match l with
   h::t -> h
  | _ -> failwith "hd";;

let tl l =
  match l with
   h::t -> t
  | _ -> failwith "tl";;

let map f =
  let rec mapf l =
    match l with
      [] -> []
    | (x::t) -> let y = f x in y::(mapf t) in
  mapf;;

let rec last l =
  match l with
    [x] -> x
  | (h::t) -> last t
  | [] -> failwith "last";;

let rec butlast l =
  match l with
    [_] -> []
  | (h::t) -> h::(butlast t)
  | [] -> failwith "butlast";;

let rec el n l =
  if n = 0 then hd l else el (n - 1) (tl l);;

let rev =
  let rec rev_append acc l =
    match l with
      [] -> acc
    | h::t -> rev_append (h::acc) t in
  fun l -> rev_append [] l;;

let rec map2 f l1 l2 =
  match (l1,l2) with
    [],[] -> []
  | (h1::t1),(h2::t2) -> let h = f h1 h2 in h::(map2 f t1 t2)
  | _ -> failwith "map2: length mismatch";;

(* ------------------------------------------------------------------------- *)
(* Attempting function or predicate applications.                            *)
(* ------------------------------------------------------------------------- *)

let can f x = try (f x; true) with Failure _ -> false;;

let check p x = if p x then x else failwith "check";;

(* ------------------------------------------------------------------------- *)
(* Repetition of a function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let rec repeat f x =
  try let y = f x in repeat f y with Failure _ -> x;;

(* ------------------------------------------------------------------------- *)
(* To avoid consing in various situations, we propagate this exception.      *)
(* I should probably eliminate this and use pointer EQ tests instead.        *)
(* ------------------------------------------------------------------------- *)

exception Unchanged;;

(* ------------------------------------------------------------------------- *)
(* Various versions of list iteration.                                       *)
(* ------------------------------------------------------------------------- *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec rev_itlist f l b =
  match l with
    [] -> b
  | (h::t) -> rev_itlist f t (f h b);;

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

let rec itlist2 f l1 l2 b =
  match (l1,l2) with
    ([],[]) -> b
  | (h1::t1,h2::t2) -> f h1 h2 (itlist2 f t1 t2 b)
  | _ -> failwith "itlist2";;

let rec rev_itlist2 f l1 l2 b =
   match (l1,l2) with
     ([],[]) -> b
   | (h1::t1,h2::t2) -> rev_itlist2 f t1 t2 (f h1 h2 b)
      | _ -> failwith "rev_itlist2";;

(* ------------------------------------------------------------------------- *)
(* Iterative splitting (list) and stripping (tree) via destructor.           *)
(* ------------------------------------------------------------------------- *)

let rec splitlist dest x =
  try let l,r = dest x in
      let ls,res = splitlist dest r in
      (l::ls,res)
  with Failure _ -> ([],x);;

let rev_splitlist dest =
  let rec rsplist ls x =
    try let l,r = dest x in
        rsplist (r::ls) l
    with Failure _ -> (x,ls) in
  fun x -> rsplist [] x;;

let striplist dest =
  let rec strip x acc =
    try let l,r = dest x in
        strip l (strip r acc)
    with Failure _ -> x::acc in
  fun x -> strip x [];;

(* ------------------------------------------------------------------------- *)
(* Apply a destructor as many times as elements in list.                     *)
(* ------------------------------------------------------------------------- *)

let rec nsplit dest clist x =
  if clist = [] then [],x else
  let l,r = dest x in
  let ll,y = nsplit dest (tl clist) r in
  l::ll,y;;

(* ------------------------------------------------------------------------- *)
(* Replication and sequences.                                                *)
(* ------------------------------------------------------------------------- *)

let rec replicate x n =
    if n < 1 then []
    else x::(replicate x (n - 1));;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;

(* ------------------------------------------------------------------------- *)
(* Various useful list operations.                                           *)
(* ------------------------------------------------------------------------- *)

let rec forall p l =
  match l with
    [] -> true
  | h::t -> p(h) & forall p t;;

let rec forall2 p l1 l2 =
  match (l1,l2) with
    [],[] -> true
  | (h1::t1,h2::t2) -> p h1 h2 & forall2 p t1 t2
  | _ -> false;;

let rec exists p l =
  match l with
    [] -> false
  | h::t -> p(h) or exists p t;;

let length =
  let rec len k l =
    if l = [] then k else len (k + 1) (tl l) in
  fun l -> len 0 l;;

let rec filter p l =
  match l with
    [] -> l
  | h::t -> let t' = filter p t in
            if p(h) then if t'==t then l else h::t'
            else t';;

let rec partition p l =
  match l with
    [] -> [],l
  | h::t -> let yes,no = partition p t in
            if p(h) then (if yes == t then l,[] else h::yes,no)
            else (if no == t then [],l else yes,h::no);;

let rec mapfilter f l =
  match l with
    [] -> []
  | (h::t) -> let rest = mapfilter f t in
              try (f h)::rest with Failure _ -> rest;;

let rec find p l =
  match l with
      [] -> failwith "find"
    | (h::t) -> if p(h) then h else find p t;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;

let flat l = itlist (@) l [];;

let rec remove p l =
  match l with
    [] -> failwith "remove"
  | (h::t) -> if p(h) then h,t else
              let y,n = remove p t in y,h::n;;

let rec chop_list n l =
  if n = 0 then [],l else
  try let m,l' = chop_list (n-1) (tl l) in (hd l)::m,l'
  with Failure _ -> failwith "chop_list";;

let index x =
  let rec ind n l =
    match l with
      [] -> failwith "index"
    | (h::t) -> if Pervasives.compare x h = 0 then n else ind (n + 1) t in
  ind 0;;

(* ------------------------------------------------------------------------- *)
(* "Set" operations on lists.                                                *)
(* ------------------------------------------------------------------------- *)

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> Pervasives.compare x h = 0 or mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let unions l = itlist union l [];;

let intersect l1 l2 = filter (fun x -> mem x l2) l1;;

let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1;;

let subset l1 l2 = forall (fun t -> mem t l2) l1;;

let set_eq l1 l2 = subset l1 l2 & subset l2 l1;;

(* ------------------------------------------------------------------------- *)
(* Association lists.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare x a = 0 then y else assoc a t
  | [] -> failwith "find";;

let rec rev_assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assoc a t
  | [] -> failwith "find";;

(* ------------------------------------------------------------------------- *)
(* Zipping, unzipping etc.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let rec unzip =
  function [] -> [],[]
         | ((a,b)::rest) -> let alist,blist = unzip rest in
                            (a::alist,b::blist);;

(* ------------------------------------------------------------------------- *)
(* Sharing out a list according to pattern in list-of-lists.                 *)
(* ------------------------------------------------------------------------- *)

let rec shareout pat all =
  if pat = [] then [] else
  let l,r = chop_list (length (hd pat)) all in
  l::(shareout (tl pat) r);;

(* ------------------------------------------------------------------------- *)
(* Iterating functions over lists.                                           *)
(* ------------------------------------------------------------------------- *)

let rec do_list f l =
  match l with
    [] -> ()
  | (h::t) -> (f h; do_list f t);;

(* ------------------------------------------------------------------------- *)
(* Sorting.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec sort cmp lis =
  match lis with
    [] -> []
  | piv::rest ->
      let r,l = partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r));;

(* ------------------------------------------------------------------------- *)
(* Removing adjacent (NB!) equal elements from list.                         *)
(* ------------------------------------------------------------------------- *)

let rec uniq l =
  match l with
    x::(y::_ as t) -> let t' = uniq t in
                      if Pervasives.compare x y = 0 then t' else
                      if t'==t then l else x::t'
 | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Convert list into set by eliminating duplicates.                          *)
(* ------------------------------------------------------------------------- *)

let setify s = uniq (sort (fun x y -> Pervasives.compare x y <= 0) s);;

(* ------------------------------------------------------------------------- *)
(* String operations (surely there is a better way...)                       *)
(* ------------------------------------------------------------------------- *)

let implode l = itlist (^) l "";;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;

(* ------------------------------------------------------------------------- *)
(* Greatest common divisor.                                                  *)
(* ------------------------------------------------------------------------- *)

let gcd =
  let rec gxd x y =
    if y = 0 then x else gxd y (x mod y) in
  fun x y -> let x' = abs x and y' = abs y in
              if x' < y' then gxd y' x' else gxd x' y';;

(* ------------------------------------------------------------------------- *)
(* Some useful functions on "num" type.                                      *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* All pairs arising from applying a function over two lists.                *)
(* ------------------------------------------------------------------------- *)

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* Issue a report with a newline.                                            *)
(* ------------------------------------------------------------------------- *)

let report s =
  Format.print_string s; Format.print_newline();;

(* ------------------------------------------------------------------------- *)
(* Convenient function for issuing a warning.                                *)
(* ------------------------------------------------------------------------- *)

let warn cond s =
  if cond then report ("Warning: "^s) else ();;

(* ------------------------------------------------------------------------- *)
(* Flags to switch on verbose mode.                                          *)
(* ------------------------------------------------------------------------- *)

let verbose = ref true;;
let report_timing = ref true;;

(* ------------------------------------------------------------------------- *)
(* Switchable version of "report".                                           *)
(* ------------------------------------------------------------------------- *)

let remark s =
  if !verbose then report s else ();;

(* ------------------------------------------------------------------------- *)
(* Time a function.                                                          *)
(* ------------------------------------------------------------------------- *)

let time f x =
  if not (!report_timing) then f x else
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      report("CPU time (user): "^(string_of_float(finish_time -. start_time)));
      result
  with e ->
      let finish_time = Sys.time() in
      Format.print_string("Failed after (user) CPU time of "^
                          (string_of_float(finish_time -. start_time))^": ");
      raise e;;

(* ------------------------------------------------------------------------- *)
(* Versions of assoc and rev_assoc with default rather than failure.         *)
(* ------------------------------------------------------------------------- *)

let rec assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if Pervasives.compare x a = 0 then y else assocd a t d;;

let rec rev_assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assocd a t d;;

(* ------------------------------------------------------------------------- *)
(* Version of map that avoids rebuilding unchanged subterms.                 *)
(* ------------------------------------------------------------------------- *)

let rec qmap f l =
  match l with
    h::t -> let h' = f h and t' = qmap f t in
            if h' == h & t' == t then l else h'::t'
  | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Merging and bottom-up mergesort.                                          *)
(* ------------------------------------------------------------------------- *)

let rec merge ord l1 l2 =
  match l1 with
    [] -> l2
  | h1::t1 -> match l2 with
                [] -> l1
              | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;

let mergesort ord =
  let rec mergepairs l1 l2 =
    match (l1,l2) with
        ([s],[]) -> s
      | (l,[]) -> mergepairs [] l
      | (l,[s1]) -> mergepairs (s1::l) []
      | (l,(s1::s2::ss)) -> mergepairs ((merge ord s1 s2)::l) ss in
  fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [x]) l);;

(* ------------------------------------------------------------------------- *)
(* Common measure predicates to use with "sort".                             *)
(* ------------------------------------------------------------------------- *)

let increasing f x y = Pervasives.compare (f x) (f y) < 0;;

let decreasing f x y = Pervasives.compare (f x) (f y) > 0;;

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* ------------------------------------------------------------------------- *)

type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;

(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

let undefined = Empty;;

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

let is_undefined f =
  match f with
    Empty -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Operation analagous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

let mapf =
  let rec map_list f l =
    match l with
      [] -> []
    | (x,y)::t -> (x,f(y))::(map_list f t) in
  let rec mapf f t =
    match t with
      Empty -> Empty
    | Leaf(h,l) -> Leaf(h,map_list f l)
    | Branch(p,b,l,r) -> Branch(p,b,mapf f l,mapf f r) in
  mapf;;

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)

let foldl =
  let rec foldl_list f a l =
    match l with
      [] -> a
    | (x,y)::t -> foldl_list f (f a x y) t in
  let rec foldl f a t =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldl_list f a l
    | Branch(p,b,l,r) -> foldl f (foldl f a l) r in
  foldl;;

let foldr =
  let rec foldr_list f l a =
    match l with
      [] -> a
    | (x,y)::t -> f x y (foldr_list f t a) in
  let rec foldr f t a =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldr_list f l a
    | Branch(p,b,l,r) -> foldr f l (foldr f r a) in
  foldr;;

(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

let graph f = setify (foldl (fun a x y -> (x,y)::a) [] f);;

let dom f = setify(foldl (fun a x y -> x::a) [] f);;

let ran f = setify(foldl (fun a x y -> y::a) [] f);;

(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

let applyd =
  let rec apply_listd l d x =
    match l with
      (a,b)::t -> let c = Pervasives.compare x a in
                  if c = 0 then b else if c > 0 then apply_listd t d x else d x
    | [] -> d x in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
        Leaf(h,l) when h = k -> apply_listd l d x
      | Branch(p,b,l,r) when (k lxor p) land (b - 1) = 0
                -> look (if k land b = 0 then l else r)
      | _ -> d x in
    look f;;

let apply f = applyd f (fun x -> failwith "apply");;

let tryapplyd f a d = applyd f (fun x -> d) a;;

let defined f x = try apply f x; true with Failure _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

let undefine =
  let rec undefine_list x l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then t
          else if c < 0 then l else
          let t' = undefine_list x t in
          if t' == t then l else ab::t'
    | [] -> [] in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
        Leaf(h,l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t
          else if l' = [] then Empty
          else Leaf(h,l')
      | Branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else (match l' with Empty -> r | _ -> Branch(p,b,l',r))
          else
            let r' = und r in
            if r' == r then t
            else (match r' with Empty -> l | _ -> Branch(p,b,l,r'))
      | _ -> t in
    und;;

(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

let rec choose t =
  match t with
    Empty -> failwith "choose: completely undefined function"
  | Leaf(h,l) -> hd l
  | Branch(b,p,t1,t2) -> choose t1;;

(* ------------------------------------------------------------------------- *)
(* Install a trivial printer for the general polymorphic case.               *)
(* ------------------------------------------------------------------------- *)

let print_fpf (f:('a,'b)func) = Format.print_string "<func>";;


(* ------------------------------------------------------------------------- *)
(* Set operations parametrized by equality (from Steven Obua).               *)
(* ------------------------------------------------------------------------- *)

let rec mem' eq =
  let rec mem x lis =
    match lis with
      [] -> false
    | (h::t) -> eq x h or mem x t
  in mem;;

let insert' eq x l =
  if mem' eq x l then l else x::l;;

let union' eq l1 l2 = itlist (insert' eq) l1 l2;;

let unions' eq l = itlist (union' eq) l [];;

let subtract' eq l1 l2 = filter (fun x -> not (mem' eq x l2)) l1;;

end;;
