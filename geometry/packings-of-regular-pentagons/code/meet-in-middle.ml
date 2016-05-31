(* needs init.ml, pent.ml open Pent. pet.ml *)

needs "/home/hasty/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/pent.ml";;
needs "/home/hasty/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/pet.ml";;


(*
Meet-in-the-middle verifications of
multi-triangle estimates.

We make hash tables of areas of peripheral triangles.
Then we compute area of central triangle, using hash tables
to find total area of the cluster of triangles.

The keys for the hash tables are derived from shared data
along common edges.

Thomas Hales
March 2016
*)

module Meet = struct

  open Pent;;

let int_floor x = int_of_float (floor x);;

let int_ceil x = int_of_float (ceil x);;

let affine width offset r = 
  ((r - offset)/width);;

(* We rarely use integer arithmetic. *)
let ( +~ ) = Pervasives.( + );;
let ( *~) = Pervasives.( * );;
let ( -~ ) = Pervasives.( - );;

let ( >. ) (x:float) (y:float) = x > y;;
let ( <. ) (x:float) (y:float) = x < y;;

(* Hashtable keys are discretizations of interval domains. *)

let make_a_key width offset t =
  let im = int_floor (affine width offset t).low in
  let iM = int_ceil (affine width offset t).high in
  (im -- (iM -~ 1));;

make_a_key (m 0.2) (m 0.1) (mk 1.01 1.1);;

(* Sorting the angle keys j,k would allow the
   peripheral triangle to be reflected before attaching to 
   center triangle *)

let make_keys width offsets ranges = 
  let (o1,o23) = offsets in
  let (r1,r2,r3) = ranges in
  let k1 = make_a_key width o1 r1 in
  let k2 = make_a_key width o23 r2 in
  let k3 = make_a_key width o23 r3 in
  let pair x y = (x,y) in
(*  let sort (j,k) = if (j<k) then (j,k) else (k,j) in *)
  let k123 = outer pair k1 ((* map sort *) (outer pair k2 k3)) in
    map (fun (i,(j,k)) -> (i,j,k)) k123;;

make_keys (m 0.2) ((m 1.0),(m 1.0)) 
  ((mk 1.1 1.2),(mk 1.4 1.5),(mk 2.01 2.3));;

(* set up hashtables *)

let mk_hashtbl() = 
  let tbl = Hashtbl.create 20000 in
  let _ = Hashtbl.clear tbl in
  tbl;;

let subwidth width i =
  width_I i << width / two;;

let edgewidth (a,b,c) =
  let (wa,wb,wc) = width_I a,width_I b,width_I c in
  max3_I wa wb wc;;

let normal_edge_keys width offsets edgedata = 
  let (l,t,t') = edgedata in
  let ts = Pet.periodize_pent t in
  let ts' = Pet.periodize_pent t' in
  let lpair x y = l,x,y in
  let ls = outer lpair ts ts' in
  map (make_keys width offsets) ls;;

(*  let r =  map (fun t -> (make_keys width offsets t,t)) ls in
    List.flatten (map (fun (ks,ed) -> map (fun k -> (k,ed)) ks) r);;
*)

let repopulate_local_tbl hash_add width offsets 
    compute_one disjoint_from_local_domain tolist fromlist = 
  let rec add' = function
    | [] -> ()
    | lp :: lps ->
      try
	(match compute_one lp with
	| None -> add' lps
	| Some (extradata,edgedata,area) ->
	  if disjoint_from_local_domain extradata (* including area constraints *)
	  then add' lps
	  else 
	    let wedge = edgewidth edgedata in
	    let _ = subwidth width wedge or raise Unstable in
	    let keys = normal_edge_keys width offsets edgedata in
	    let _ =  map (fun k -> hash_add k (lp,area)) keys in
	    add' lps)
      with Unstable -> 
	let ls = tolist lp in
	let (ls1,ls2) = splitlist (1.0e-4) ls in
	add' (fromlist (ls,ls1):: fromlist (ls,ls2):: lps) in
  add';;

(* let populate_local_hash = 0;; *)
(* let populate_local_tbl = 0;; *)

let repopulate_area_tbl 
    local_tbl area_tbl = 
  let f k (_,area) =
    try 
      let currentarea = Hashtbl.find area_tbl k in
      if (area <. currentarea) then Hashtbl.add area_tbl k area else () 
    with Not_found -> () in
  Hashtbl.iter f local_tbl;;
      
let repopulate_peripheral 
    area_tbl local_tbl 
    width offsets compute_one 
    disjoint_from_local_domain tolist fromlist localparams =
  let _ = Hashtbl.reset area_tbl in
  let _ = Hashtbl.reset local_tbl in
  let _ = repopulate_local_tbl (Hashtbl.add local_tbl)  
    width offsets
    compute_one disjoint_from_local_domain
    tolist fromlist localparams in
  let _ = repopulate_area_tbl local_tbl area_tbl in
  let l1 = Hashtbl.length local_tbl in
  let l2 = Hashtbl.length area_tbl in
  let _ = report (Format.sprintf "..peripheral table lengths = %d/%d" l2 l1) in
  ();;

let findsome tbl key = 
    try
      Some (Hashtbl.find tbl key)
    with Not_found -> None;;

(* fix: This can't be used on hashtables of different types *)

let depopulate_local_tbl =
  let temp_tbl = Hashtbl.create 20000 in
  fun width offsets local_tbl edgecuts ->
  let _ = Hashtbl.reset temp_tbl in
  let getkeys (ed,areacutoff) = 
    let keys = normal_edge_keys width offsets ed in
    map (fun k -> (k,areacutoff)) keys in
  let keypairs = List.flatten (map getkeys edgecuts) in
  let add_temp (key,area) = 
    match findsome temp_tbl key with
    | None -> Hashtbl.add temp_tbl key area
    | Some current ->
      if (area >. current) then Hashtbl.add temp_tbl key area in
  let _ = map add_temp keypairs in
  let f k (lp,area) buffer = 
    try
      let areacutoff = Hashtbl.find temp_tbl k in
      if (area<= areacutoff) then lp::buffer
      else buffer 
    with Not_found -> buffer in
  Hashtbl.fold f local_tbl [];;

let add_area_cutoff_tbl = 0;;

(* sws is the subwidth list that must be rechecked later for
   a small width *)

let recurse_central 
    width compute_one disjoint_from_central_domain
    others_outofbounds 
    areacutoff edgewidthfn tolist fromlist = 
  let rec add' sws = 
  function 
  | [] -> sws
  | lp::lps ->
      try
	match compute_one lp with
	| None -> add' sws lps
	| Some (extradata,edgedata,area) ->
	  if area >> areacutoff or 
	    disjoint_from_central_domain extradata or
	    others_outofbounds edgedata (areacutoff-area) 
	  then add' sws lps
	  else 
	    if subwidth width (edgewidthfn edgedata)
	    then add' ((lp,extradata,edgedata,area)::sws) lps
	    else raise Unstable
      with Unstable -> 
	let ls = tolist lp in
	let (ls1,ls2) = splitlist (1.0e-4) ls in
	add' sws (fromlist (ls,ls1):: fromlist (ls,ls2):: lps) in
  add' [];;


let meet_one_round width_denom offsets
    compute_central disjoint_from_central_domain
    others_outofbounds mk_edgecuts
    areacutoff central_edgewidthfn central_tolist central_fromlist 
    central_params
    peripheral_area_tbls peripheral_local_tbls 
    compute_peripherals 
    disjoint_from_peripheral_domains peripheral_tolists peripheral_fromlists peripheral_paramss =
  let width = rat 1 width_denom in
  let repopulate (area_tbl,local_tbl,c,disj,tos,froms,locals) = 
    repopulate_peripheral area_tbl local_tbl width offsets c disj tos froms locals in
  let zips a b c d e f g = zip a (zip b (zip c (zip d (zip e (zip f g))))) in
  let zs = zips peripheral_area_tbls peripheral_local_tbls compute_peripherals disjoint_from_peripheral_domains peripheral_tolists peripheral_fromlists peripheral_paramss in
  let zs1 = map (fun (a,(b,(c,(d,(e,(f,g))))))->(a,b,c,d,e,f,g)) zs in
  let _ = map repopulate zs1 in
  let sws = recurse_central 
    width compute_central disjoint_from_central_domain
    others_outofbounds 
    areacutoff central_edgewidthfn central_tolist central_fromlist central_params in
  let edgecutss = mk_edgecuts sws in
  let depop (local_tbl,edgecuts) =
    depopulate_local_tbl width offsets local_tbl edgecuts in
  let z2 = zip peripheral_local_tbls edgecutss in
  let buffs = map depop z2 in
  let new_lps = map (fun (lp,_,_,_) -> lp) sws in
  (new_lps,buffs);;

let rec meet_in_the_middle count width_denom offsets
    compute_central disjoint_from_central_domain
    others_outofbounds mk_edgecuts
    areacutoff central_edgewidthfn central_tolist central_fromlist 
    central_params
    peripheral_area_tbls peripheral_local_tbls 
    compute_peripherals 
    disjoint_from_peripheral_domains peripheral_tolists peripheral_fromlists peripheral_paramss =
  let print ff d = report (Format.sprintf ff d) in
  let len = List.length in
  let _ = print "\n\nnew round: %d" count in
  let _ = print "  width = 1/%d" width_denom in
  let _ = print "  central list length = %d" (len central_params) in
  let _ = map (fun r -> print "  peripheral length = %d" (len r)) peripheral_paramss in 
  let (sws,buffs) = 
    meet_one_round width_denom offsets
    compute_central disjoint_from_central_domain
    others_outofbounds mk_edgecuts
    areacutoff central_edgewidthfn central_tolist central_fromlist 
      central_params
    peripheral_area_tbls peripheral_local_tbls 
    compute_peripherals 
    disjoint_from_peripheral_domains peripheral_tolists peripheral_fromlists peripheral_paramss in
  if sws = [] then (print "done! count=%d" count) else
    meet_in_the_middle (count +~ 1) (2 *~ width_denom) offsets
    compute_central disjoint_from_central_domain
    others_outofbounds mk_edgecuts
    areacutoff central_edgewidthfn central_tolist central_fromlist 
    sws
    peripheral_area_tbls peripheral_local_tbls 
    compute_peripherals 
    disjoint_from_peripheral_domains peripheral_tolists peripheral_fromlists buffs;;
		 

(* now start implementation of specific calculations *)


end;;

