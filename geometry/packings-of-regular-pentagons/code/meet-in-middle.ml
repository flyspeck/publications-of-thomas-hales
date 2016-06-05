(* Thomas Hales
March 2016. Redone June 2016.
*)


(* needs init.ml, pent.ml open Pent. pet.ml *)

needs "pent.ml";;
needs "pet.ml";;


(*
Meet-in-the-middle verifications of
multi-triangle estimates.

One triangle is designated a central.
The others are peripheral.
Each peripheral triangle must share an edge with the central triangle.

We make hash tables of areas of peripheral triangles.
Then we compute area of central triangle and
find total area of the cluster of triangles.

The keys for the hash tables are derived from shared data
along common edges.

*)

module Meet = struct

  open Pent;;

(***********************************************************************)
(* set up keys *)
(***********************************************************************)

let findsome tbl key = 
    try
      Some (Hashtbl.find tbl key)
    with Not_found -> None;;

let int_floor x = int_of_float (floor x);;

(* should be strictly larger than x *)
let int_ceil x = 
  let c = ceil x in 
  let i = int_of_float c in
  if (c = x) then i +~ 1 else i;;
  
let affine width offset r = 
  ((r - offset)/width);;


(* Hashtable keys are discretizations of interval domains. *)

let make_a_key width offset t =
  let im = int_floor (affine width offset t).low in
  let iM = int_ceil (affine width offset t).high in
  (im -- (iM -~ 1));;

int_ceil 3.0;;
make_a_key (m 0.2) (m 0.1) (mk 1.01 1.1);;
make_a_key one zero (m 3.0);;

(* Sorting the angle keys j,k would allow the
   peripheral triangle to be reflected before attaching to 
   center triangle *)

let make_keys width offsets ranges = 
  let (o1,o23) = offsets in  (* 2nd and 3rd offsets are equal *)
  let (r1,r2,r3) = ranges in
  let k1 = make_a_key width o1 r1 in
  let k2 = make_a_key width o23 r2 in
  let k3 = make_a_key width o23 r3 in
  outertriple k1 k2 k3;;

(*  let pair x y = (x,y) in 
    let sort (j,k) = if (j<k) then (j,k) else (k,j) in 
  let k123 = outerpair k1 ((* map sort *) (outerpair k2 k3)) in
    map (fun (i,(j,k)) -> (i,j,k)) k123;; *)

make_keys (m 0.2) ((m 1.0),(m 1.0)) 
  ((mk 1.1 1.2),(mk 1.4 1.5),(mk 2.01 2.3));;

let keys_of_edge width offsets edgedata = 
  let (l,t,t') = edgedata in
  let ts = Pet.periodize_pent t in
  let ts' = Pet.periodize_pent t' in
  let triples = outertriple [l] ts ts' in
  map (make_keys width offsets) triples;;

(***********************************************************************)
(* peripheral triangles. *)
(***********************************************************************)

(* takes one peridatum and generatees a list of peridata at smaller pwidth *)

let widthlist xs = (* floating point ok here *)
  let ws = map (fun x -> x.high -. x.low) xs in 
  itlist (fun x y -> max x y) ws 0.0;;

let rec subdivide_subwidth width = 
  let eps = 1.0e-8 in
  function
  | [] -> []
  | x::xs -> if widthlist x < width.low then x :: subdivide_subwidth width xs
    else let x1,x2 = splitlist eps x in subdivide_subwidth width (x1::x2::xs);;

(* cutoffs stored as snd in peripheral hashtable *)

let maxcutoff hash_tbl keys = 
  let data = map snd (map (Hashtbl.find hash_tbl) keys) in
  if data = [] then None
  else
    Some (  end_itlist (fun x y -> max2_I x y) data);;

(* current min areas stored as fst in hashtable *)

let minarea hash_tbl keys = 
  let data = map fst (map (Hashtbl.find hash_tbl) keys) in
  if data = [] then None
  else 
  Some  (end_itlist (fun x y -> min2_I x y) data);;

(* peripheral data stored as list of (pcoord,keys,area,fn).
   mk_one_peridata subdivides it. *)

let mk_one_peridata pwidth phash (pcoord,keys,area,fn) = 
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let maxcut = maxcutoff phash keys in 
  let _ = not (maxcut = None) or failwith "keys of phash should sync" in
  let makesome pc = match (fillfn extra pc) with
    | None -> None
    | Some fill -> (let area' = areafn fill in
		   if (area' >> the maxcut) or outdomfn fill then None
		   else let keys' = keyfn pwidth fill in 
			Some (pc,keys',min_I area',fn)) in
  if area >> the maxcut then []
  else
    let pcs = subdivide_subwidth pwidth [pcoord] in
    selectsome (map makesome pcs);;


(* area-one can be anything less than area.  It gets updated later by
   central procedures. *)

let  update_one_perihash phash (pcoord,keys,area,fn) = 
  let area = min_I area in
  let one_key k = match findsome phash k with
    | None -> ()
    | Some (ak,_) -> if area.low <. ak.low then Hashtbl.add phash k (area,area-one) in
  let _ = map one_key keys in
  ();;
    
let update_perihash phash peridata = 0;;

let mk_peridata pwidth (phash,oldps) = 
  let ps = List.flatten (map (mk_one_peridata pwidth phash) oldps) in
  let _ = Hashtbl.reset phash in 
  let _ = map (update_one_perihash phash) ps in
  (phash,ps);;



let recut phash cut' key = 
    match findsome phash key with
    | None -> ()
    | Some (a,cut) -> 
      if cut'.high >. cut.high then Hashtbl.add phash key (a,cut');;

(***********************************************************************)
(* central triangle.  *)
(***********************************************************************)

(* hashtables are mutable here: *)
  
let  mk_one_cendata cwidth cluster_areacut phashlist (ccoord,cencutoff,fn) = 
  let (extra,fillfn,outdomfn,areafn,keyfns) = fn in
  let _ = List.length keyfns = List.length phashlist or failwith "number of peripherals" in
  let perirecut gap ((phash,keys),area) = map (recut phash (max_I (gap+area))) keys in
  let makesome cc = match (fillfn extra cc) with
    | None -> None
    | Some fill -> 
      (let area' = min_I (areafn fill) in
       if (area' >> cencutoff) or outdomfn fill then None
       else 
	 let keys' = map (fun f -> f cwidth fill) keyfns in
	 let hashkeys = zip phashlist keys' in
	 let someperiareas = map (uncurry minarea) hashkeys in
	 if exists ((=) None) someperiareas then None
	 else 
	   let periareas = map the someperiareas in
	   let periarea = min_I (itlist ( + ) periareas zero) in 
	   let clustarea = area' + periarea in
	   let gap = clustarea - cluster_areacut in
	   if gap >> zero then None
	   else
	     let _ = map (perirecut gap) (zip hashkeys periareas) in
	     let cencutoff' = max_I (cluster_areacut - periarea) in
	     Some (cc,cencutoff',fn)) in
  let ccs = subdivide_subwidth cwidth [ccoord] in
  selectsome (map makesome ccs);;

let mk_cendata cwidth cluster_areacut phashlist ccs = 
  List.flatten (map (mk_one_cendata cwidth cluster_areacut phashlist) ccs);;

let debug c a p ccs = 
  (funpow 2 (mk_cendata c a p) ccs);;



(***********************************************************************)
(* set up hashtables *)
(***********************************************************************)


let mk_hashtbl() = 
  let tbl = Hashtbl.create 20000 in
  let _ = Hashtbl.clear tbl in
  tbl;;

(* let phash1 = mk_hashtbl();; *)

(***********************************************************************)
(* main recursion *)
(***********************************************************************)

let report_stats(i,width,pdata,ccs) = 
  let s1 = Printf.sprintf "i= %d, w=%3.3f, #p=%d, length(ccs)=%d" 
    i (width.low) (List.length pdata) (List.length ccs) in
  report s1;;


let rec mitm_recursion i cluster_areacut width pdata ccs =
  let _ = width >> (m (1.0e-6)) or failwith "I'm giving up at small width" in
  let scale = m 0.5 in (* experimental- coordinatewidth/keywidth ratio *)
  let pwidth = width * scale in  
  let cwidth = pwidth in
  let pdata = map (mk_peridata pwidth) pdata in
  let phashlist = map fst pdata in
  if (exists (fun (_,t) -> t=[]) pdata) then true
  else 
    let ccs = mk_cendata cwidth cluster_areacut phashlist ccs in
    if ccs = [] then true
    else 
      let _ = report_stats (i,width,pdata,ccs) in
      mitm_recursion (succ i) cluster_areacut (width/two) pdata ccs;;

(***********************************************************************)
(* implement specific calculations *)
(***********************************************************************)

(* fillout 5D.  Acute triangle.
   One pent contact between A and C. A points to C. *)

let fillout5D ((dAB,thABC,thBAC),dBC,dAC) = 
  if not(Pet.pet dAB thABC thBAC) then None 
  else
    let arcC = iarc dAC dBC dAB in
    let arcA = iarc dAC dAB dBC in
    let arcB = iarc dAB dBC dAC in
    let a = areamin_acute dAC dAB dBC in
    let thACB = - (arcA + thABC) in
    let thBCA = - (arcB + thBAC) in
    let thACB0 = periodize_pent thACB in
    let thACB_CAB = map (fun t -> t,theta_banana dAC t) thACB0 in
    let thACB_CAB= mapfilter (fun (t,s) -> (t, the s)) thACB_CAB in
    let thACB_CAB_CBA = map (fun (t1,t) -> (t1,t,-(arcC + t))) thACB_CAB in
    let thACB_CAB_CBA = filter (fun (_,_,th') -> Pet.pet dBC thBCA th') thACB_CAB_CBA in 
    if (thACB_CAB_CBA = []) then None 
    else
	(Some (a,(map (fun (thACB,thCAB,thCBA) -> 	  (dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB) ) 		   thACB_CAB_CBA)));;

end;;

