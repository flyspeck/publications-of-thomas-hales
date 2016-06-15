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

The keys for the hash tables are derived from shared coords
along common edges.

We structure the problems so that we wish to prove that
various domains are empty.  
That is, we subdivide until everything is out-of-domain.

*)

module Meet = struct

  open Pent;;

let findsome tbl key = 
    try
      Some (Hashtbl.find tbl key)
    with Not_found -> None;;


(***********************************************************************)
(* set up keys *)
(***********************************************************************)


let int_floor x = int_of_float (floor x);;

(* should be strictly larger than x *)
let int_ceil x = 
  let c = ceil x in 
  let i = int_of_float c in
  if (c = x) then succ i else i;;

(* Hashtable keys are discretizations of interval domains.
   We must have the property that if two domains have nonempty
   intersection, then they have at least one key in common.  
   We achieve this by enlarging the domains to a union of cubes
   of a fixed width and attaching a key to each cube.  *)

let make_a_key width  t =
  let rescale = t/width in
  let im = int_floor (rescale).low in
  let iM = int_ceil (rescale).high in
  (im -- (iM -~ 1));;

int_ceil 3.0;;
int_floor (- 2.5);;
make_a_key (m 0.2)  (mk 1.01 1.1);;
make_a_key one (m 3.0);;

(* Sorting the angle keys j,k would allow the
   peripheral triangle to be reflected before attaching to 
   center triangle *)

let make_keys widths ranges = 
  let (r1,r2,r3) = ranges in
  let (w1,w2,w3) = widths in
  let k1 = make_a_key w1 r1 in
  let k2 = make_a_key w2 r2 in
  let k3 = make_a_key w3 r3 in
  map (Hashtbl.hash) (outertriple k1 k2 k3);;

make_keys (m 0.2,m 0.2,m 0.2)
  ((mk 1.1 1.2),(mk 1.4 1.5),(mk 2.01 2.3));;

let keys_of_edge width edgedata = 
  let (l,t,t') = edgedata in
  let ts = Pet.periodize_pent t in
  let ts' = Pet.periodize_pent t' in
  let triples = outertriple [l] ts ts' in
  let s = two in (* scale factor, experimental design,
		 used because areas are more sensitive to edge lengths
		 than the theta variables. It reduces the size of the
		 hash table. *)
  List.flatten (map (make_keys (width,s*width,s*width)) triples);;

let key_invert w (l,t,t') = 
  keys_of_edge w (l,-t,-t');;  
(* peripheral vs. central perspective.
  We invert the central coordinates to get the peripheral ones and keys. *)

let key_inverts w eds = 
  setify (List.flatten (map (key_invert w) eds));;

(***********************************************************************)
(* peripheral triangles. *)
(***********************************************************************)

(* takes one peridatum and generates peridata at smaller width *)

let widthlist xs = (* floating point ok here *)
  let ws = map (fun x -> x.high -. x.low) xs in 
  itlist (fun x y -> max x y) ws 0.0;;

widthlist [mk 3.0 4.0; mk 7.0 9.1; mk 1.0 2.05];;

let rec subdivide_subwidth width xs = 
  let ns = map (fun t -> int_ceil (width_I t / width).high) xs in
  let one1 (n,x) = let v =  (width_I x /int n) in
		  let z = min_I x + zero2 v in
		  map (fun i -> [z + v * int i]) (0--(n-~ 1)) in
  let prs = map one1 (zip ns xs) in
  end_itlist (fun x y -> outer ( @ ) x y) prs;;
  

let test = 
 (subdivide_subwidth (m 2.1) [zero2 two;zero2 four;zero2 four]);;

let test = 
  let _ = time (subdivide_subwidth (one)) [mk 0.0 100.0;mk 0.0 100.7;mk 0.0 100.0] in
  ();;

let test = subdivide_subwidth one [mk 0.0 0.5];;


(* cuts stored as snd in peripheral hashtable.
   Any entry that has area above the cut can be discarded. *)

let maxcut hash keys = 
  let cuts = selectsome (map snd (map (Hashtbl.find hash) keys)) in
  if cuts = [] then None
  else
    Some (end_itlist (fun x y -> if x >. y then x else y) cuts);;

let testh = Hashtbl.create 20;;
let _ =   Hashtbl.clear testh;;
let _ = Hashtbl.add testh 0 (m 7.0,None);;
let _ = Hashtbl.add testh 1 (m 7.1,Some 1.0);;
let _ = Hashtbl.add testh 2 (m 7.2,Some 2.0);;
let _ = Hashtbl.add testh 3 (m 7.3,Some 3.0);;
Hashtbl.mem testh 3;;
maxcut testh [0;3;1;3;2];;

(* current min areas stored as fst in hashtable. Used by central procedures. *)

let minarea hash keys = 
  let areas = map fst (selectsome (map (findsome hash) keys)) in
  if areas = [] then None
  else 
  Some  (min_I(end_itlist (fun x y -> if x.low <. y.low then x else y) areas));;

minarea testh [3;1;3;2];;

(* recut is used by central procedures to update periphery *)

let recut phash cut' key = 
    match findsome phash key with
    | None -> ()
    | Some (a,None) -> Hashtbl.add phash key (a,Some cut')
    | Some (a,Some cut) -> 
      if cut' >. cut then Hashtbl.replace phash key (a,Some cut');;


(* peripheral record stored as list of (pcoord,keys,area,fn).
   mk_one_pericoord subdivides it. 

   The keys and phash here correspond to the stale width.
*)

let mk_one_pericoord initialized width phash fn (pcoord,keys,area) = 
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let maxcut = maxcut phash keys in 
  let overweight a = initialized &&
    (* Don't delete anything during initialization round *)
    (* if None, then no match was found with central triangle and can delete *)
    (match maxcut with | None -> true | Some mx -> (a >>. mx)) in
  let rec makesome pc = 
    try
      match (fillfn extra pc) with
      | None -> []
      | Some fill -> (let area' = areafn fill in
		      if (overweight area') or outdomfn fill then []
		      else let keys' = keyfn width fill in 
			   [(pc,keys',min_I area')])
    with Unstable -> (let (pc1,pc2) = splitlist (1.0e-4) pc in 
		      makesome pc1 @ makesome pc2) in
  if overweight area then []
  else
    let pcs = subdivide_subwidth width pcoord in
     (List.flatten (map makesome pcs));;

(* Initial None area gets updated later by central procedures. *)

let update_one_perihash phash (pcoord,keys,area) = 
  let area = min_I area in
  let one_key k = match findsome phash k with
    | None -> Hashtbl.add phash k (area,None)
    | Some (ak,_) -> if area.low <. ak.low then Hashtbl.replace phash k (area,None) in
  let _ = map one_key keys in
  ();;
    
let mk_peridata initialized width (phash,(pfn,ps)) = 
  let ps' = List.flatten (map (mk_one_pericoord initialized width phash pfn) ps) in
  let _ = Hashtbl.clear phash in 
  let _ = map (update_one_perihash phash) ps' in
  (phash,(pfn,ps'));;


(***********************************************************************)
(* central triangle.  *)
(***********************************************************************)

let periareas width some_phash keyfns fill = 
  if isnone(some_phash) then Some([],zero,[])
  else
    let phash = the some_phash in
    let keys' = map (fun f -> f width fill) keyfns in
    let someperiareas = map (fun keys -> minarea phash keys) keys' in
    if exists ((=) None) someperiareas then None
    else 
      let periareas = map the someperiareas in
      let total_periarea = min_I (itlist ( + ) periareas zero) in 
      Some (periareas,total_periarea,keys');;


(* hashtable is mutable here: *)
  
let  mk_one_cencoord width cluster_areacut some_phash fn (ccoord,cencut) = 
  let (extra,fillfn,outdomfn,areafn,keyfns) = fn in
  let _ = ((keyfns = [])=(isnone(some_phash))) or 
    failwith "number of peripherals" in
  let perirecut gap some_phash (keys,periarea0) = 
    map (recut (the some_phash) ((periarea0-gap).high)) keys in
  let rec makesome cc = 
    try
      match (fillfn extra cc) with
      | None -> []
      | Some fill -> 
	(let cenarea = min_I (areafn fill) in
	 if (cenarea >>. cencut) or outdomfn fill then []
	 else 
	   match periareas width some_phash keyfns fill with
	   | None -> []
	   | Some (periareas,total_periarea,keys') ->
	     (let clustarea = cenarea + total_periarea in
	      let gap = clustarea - cluster_areacut in
	      if gap >> zero then []
	      else
		(* mutable *)
		let _ = map (perirecut gap some_phash) (zip keys' periareas) in
		let cencut' = (cluster_areacut - total_periarea).high in
		let cencut' = min cencut' cencut in
		[(cc,cencut')]))
    with Unstable ->
      let (cc1,cc2) = splitlist (1.0e-4) cc in 
      makesome cc1 @ makesome cc2 in
  let ccs = subdivide_subwidth width ccoord in
  List.flatten (map makesome ccs);;

let mk_cencoord width cluster_areacut some_phash cfn ccs = 
  List.flatten (map (mk_one_cencoord width cluster_areacut some_phash cfn) ccs);;

let test c a p cfn ccs = 
  (funpow 2 (mk_cencoord c a p cfn) ccs);;



(***********************************************************************)
(* main recursion *)
(***********************************************************************)

(* pdata is Some(phash,(pfn,ps)).*)

let report_stats(i,width,pdata,ccs) = 
  let s1 = Printf.sprintf "i=%d, w=%3.5f, length(ccs)=%d" 
    i (width.low) (List.length ccs) in
  let _ = report s1 in
  let ls =  (function |None->0 | Some(_,(_,t)) -> List.length t) pdata in
  let ks,kplus,ph = match pdata with
    |None -> (0,0,0)
    |Some(ph,(_,ps)) ->
      let keyss = map (fun (_,k,_)-> List.length k) ps in
      (itlist (fun x y -> max x y) keyss 0,
       end_itlist ( +~) keyss,
       Hashtbl.length ph) in
  let _ = report (Printf.sprintf " length(ps)=%d maxkey=%d keysum=%d phash=%d" ls ks kplus ph) in
  ();;


let rec mitm_recursion i initialized cluster_areacut width some_pdata cfn ccs =
  let _ = width >> (m (1.0e-6)) or failwith "I'm giving up at small width" in
  let some_pdata',some_phash,empty = match some_pdata with
    | None -> (None,None,false)
    | Some pdata -> 
      let pdata' = mk_peridata initialized width pdata in
      let phash = fst pdata in
      (Some pdata',Some phash,(snd (snd pdata')=[])) in
  if empty then true
  else 
    let ccs = mk_cencoord width cluster_areacut some_phash cfn ccs in
    if ccs = [] then true
    else 
      let _ = report_stats (i,width,some_pdata',ccs) in
      mitm_recursion (succ i) true cluster_areacut (width/two) some_pdata' cfn ccs;;


(***********************************************************************)
(* set up hashtable *)
(***********************************************************************)

(* A single global hashtable is used for all the peripheral triangles *)

let mk_hashtbl() = 
  let tbl = Hashtbl.create 100000 in
  let _ = Hashtbl.clear tbl in
  tbl;;

let phash = mk_hashtbl();;  


(***********************************************************************)
(* implement specific calculations *)
(***********************************************************************)

(* fillout 5D.  Acute triangle.
   One pent contact between A and C. A points to C. 
   Full input coordinates (dAB,thABC,thBAC) given along edge AB. *)

let fillout5D ((dAB,thABC,thBAC),dBC,dAC) = 
  if not(Pet.pet dAB thABC thBAC) then None 
  else
    let arcC = iarc dAC dBC dAB in
    let arcA = iarc dAC dAB dBC in
    let arcB = iarc dAB dBC dAC in
    let a = areamin_acute dAC dAB dBC in
    let thACB = - (arcA + thABC) in
    let thBCA = - (arcB + thBAC) in
    let thACB0 = Pet.periodize_pent thACB in
    let thACB_CAB_pos = map (fun t -> t,theta_banana dAC t) thACB0 in
    let thACB_CAB_neg = map (fun t -> t,theta_banana_neg dAC t) thACB0 in
    let thACB_CAB= mapfilter (fun (t,s) -> (t, the s)) (thACB_CAB_pos @ thACB_CAB_neg) in
    let thACB_CAB_CBA = map (fun (t1,t) -> (t1,t,-(arcC + t))) thACB_CAB in
    let thACB_CAB_CBA = filter (fun (_,_,th') -> Pet.pet dBC thBCA th') thACB_CAB_CBA in 
    if (thACB_CAB_CBA = []) then None 
    else
	(Some (a,(map (fun (thACB,thCAB,thCBA) -> (dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB) ) thACB_CAB_CBA)));;

let areafn5D (a,_) = a;;

let edge5D_ABs (_,fs) = map (fun ((l,t,t',_),_,_)-> (l,t,t')) fs;;
let edge5D_BCs (_,fs) = map (fun (_,(l,t,t',_),_)-> (l,t,t')) fs;;
let edge5D_ACs (_,fs) = map (fun (_,_,(l,t,t',_))-> (l,t,t')) fs;;
let test t = edge5D_ACs (the (fillout5D t));;

let test1_centralpent_1237 = (* repeated calc from pent.ml *)
  let i = 0 in
  let cluster_areacut = (m 1.2 (* debug *)) in
  let width = (m 0.4) in
  let pdata = None in
  let cencut = cluster_areacut.high in
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn t = false in
  let areafn (a,_) = a in
  let keyfns = [] in
  let z2 = zero2 in
  let k2 = merge_I (two*kappa) in
  let ccoord = [k2 (21//10);z2 pi25;z2 pi25;k2 (21//10);k2 two] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  mitm_recursion i initialized cluster_areacut width pdata cfn ccs;;

let test1_centralpent_172 = (* repeated calc from pent.ml *)
  let i = 0 in
  let cluster_areacut = aK in
  let width = (m 0.1) in
  let pdata = None in
  let cencut = cluster_areacut.high in
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn (_,ts) = false in 
  let areafn (a,_) = a in
  let keyfns = [] in
  let z2 = zero2 pi25 in
  let k2 = merge_I (two*kappa) (172//100) in
  let ccoord = [k2 ;z2;z2;k2;k2] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  mitm_recursion i initialized cluster_areacut width pdata cfn ccs;;


let fillout6D ((dAB,thABC,thBAC),(dBC,thCBA),dAC) = 
  if not(Pet.pet dAB thABC thBAC) then None 
  else
    let arcC = iarc dAC dBC dAB in
    let arcA = iarc dAC dAB dBC in
    let arcB = iarc dAB dBC dAC in
    let a = areamin_acute dAC dAB dBC in
    let thACB = - (arcA + thABC) in
    let thBCA = - (arcB + thBAC) in
    let thCAB = - (arcC + thCBA) in
    if Pet.pet dAC thACB thCAB && Pet.pet dBC thBCA thCBA then
      Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
      (dAC,thACB,thCAB,arcB))
    else None;;


end;;
