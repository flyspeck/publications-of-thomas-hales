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

(* Hashtable keys are discretizations of interval domains. *)

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

let make_keys width ranges = 
  let (r1,r2,r3) = ranges in
  let k1 = make_a_key width r1 in
  let k2 = make_a_key width r2 in
  let k3 = make_a_key width r3 in
  outertriple k1 k2 k3;;

(*  let pair x y = (x,y) in 
    let sort (j,k) = if (j<k) then (j,k) else (k,j) in 
  let k123 = outerpair k1 ((* map sort *) (outerpair k2 k3)) in
    map (fun (i,(j,k)) -> (i,j,k)) k123;; *)

make_keys (m 0.2) 
  ((mk 1.1 1.2),(mk 1.4 1.5),(mk 2.01 2.3));;

let keys_of_edge width edgedata = 
  let (l,t,t') = edgedata in
  let ts = Pet.periodize_pent t in
  let ts' = Pet.periodize_pent t' in
  let triples = outertriple [l] ts ts' in
  List.flatten (map (make_keys width) triples);;

let key_invert w (l,t,t') = 
  keys_of_edge w (l,-t,-t');;  
(* peripheral vs. central perspective.
  We invert the central coordinates to get the peripheral ones and keys. *)

let key_inverts w eds = 
  setify (List.flatten (map (key_invert w) eds));;

(***********************************************************************)
(* peripheral triangles. *)
(***********************************************************************)

(* takes one peridatum and generatees a list of peridata at smaller pwidth *)

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
    Some (max_I(end_itlist (fun x y -> if x.high >. y.high then x else y) cuts));;

let testh = Hashtbl.create 20;;
let _ =   Hashtbl.clear testh;;
let _ = Hashtbl.add testh 0 (m 7.0,None);;
let _ = Hashtbl.add testh 1 (m 7.1,Some one);;
let _ = Hashtbl.add testh 2 (m 7.2,Some two);;
let _ = Hashtbl.add testh 3 (m 7.3,Some (int 3));;
maxcut testh [0;3;1;3;2];;

(* current min areas stored as fst in hashtable *)

let minarea hash keys = 
  let areas = map fst (map (Hashtbl.find hash) keys) in
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
      if cut'.high >. cut.high then Hashtbl.replace phash key (a,Some cut');;


(* peripheral data stored as list of (pcoord,keys,area,fn).
   mk_one_peridata subdivides it. 

   The keys and phash here correspond to the stale width.
*)

let mk_one_peridata initialized pwidth phash (pcoord,keys,area,fn) = 
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let maxcut = maxcut phash keys in 
  let overweight a = initialized &&
    (* Don't delete anything during initialization round *)
    (* if None, then no match exists with central triangle and can delete *)
    (match maxcut with | None -> true | Some mx -> (a >> mx)) in
  let rec makesome pc = 
    try
      match (fillfn extra pc) with
      | None -> [None]
      | Some fill -> (let area' = areafn fill in
		      if (overweight area') or outdomfn fill then [None]
		      else let keys' = keyfn pwidth fill in 
			   [Some (pc,keys',min_I area',fn)])
    with Unstable -> (let (pc1,pc2) = splitlist (1.0e-4) pc in 
		      makesome pc1 @ makesome pc2) in
  if overweight area then []
  else
    let pcs = subdivide_subwidth pwidth pcoord in
    selectsome (List.flatten (map makesome pcs));;

(* Initial None area gets updated later by central procedures. *)

let update_one_perihash phash (pcoord,keys,area,fn) = 
  let area = min_I area in
  let one_key k = match findsome phash k with
    | None -> Hashtbl.add phash k (area,None)
    | Some (ak,_) -> if area.low <. ak.low then Hashtbl.replace phash k (area,None) in
  let _ = map one_key keys in
  ();;
    
let update_perihash phash peridata = 0;;

let mk_peridata initialized pwidth (phash,ps) = 
  let ps' = List.flatten (map (mk_one_peridata initialized pwidth phash) ps) in
  let _ = Hashtbl.clear phash in 
  let _ = map (update_one_perihash phash) ps' in
  (phash,ps');;


(***********************************************************************)
(* central triangle.  *)
(***********************************************************************)

(* hashtables are mutable here: *)
  
let  mk_one_cendata cwidth cluster_areacut phashlist (ccoord,cencut,fn) = 
  let (extra,fillfn,outdomfn,areafn,keyfns) = fn in
  let _ = List.length keyfns = List.length phashlist or failwith "number of peripherals" in
  let perirecut gap ((phash,keys),area) = map (recut phash (max_I (gap+area))) keys in
  let rec makesome cc = 
    try
      match (fillfn extra cc) with
      | None -> [None]
      | Some fill -> 
	(let area' = min_I (areafn fill) in
	 if (area' >> cencut) or outdomfn fill then [None]
	 else 
	   let keys' = map (fun f -> f cwidth fill) keyfns in
	   let hashkeys = zip phashlist keys' in
	   let someperiareas = map (uncurry minarea) hashkeys in
	   if exists ((=) None) someperiareas then [None]
	   else 
	     let periareas = map the someperiareas in
	     let periarea = min_I (itlist ( + ) periareas zero) in 
	     let clustarea = area' + periarea in
	     let gap = clustarea - cluster_areacut in
	     if gap >> zero then ([None])
	     else
	       let _ = map (perirecut gap) (zip hashkeys periareas) in
	       let cencut' = max_I (cluster_areacut - periarea) in
	       [Some (cc,cencut',fn)])
    with Unstable ->
      let (cc1,cc2) = splitlist (1.0e-4) cc in 
      makesome cc1 @ makesome cc2 in
  let ccs = subdivide_subwidth cwidth ccoord in
  selectsome (List.flatten (map makesome ccs));;

let mk_cendata cwidth cluster_areacut phashlist ccs = 
  List.flatten (map (mk_one_cendata cwidth cluster_areacut phashlist) ccs);;

let debug c a p ccs = 
  (funpow 2 (mk_cendata c a p) ccs);;



(***********************************************************************)
(* main recursion *)
(***********************************************************************)

(* pdata is a list of (phash,ps).
   The length of the list is the number of peripheral triangles.
*)

let report_stats(i,width,pdata,ccs) = 
  let s1 = Printf.sprintf "i= %d, w=%3.5f, #p=%d, length(ccs)=%d" 
    i (width.low) (List.length pdata) (List.length ccs) in
  let _ = report s1 in
  let ls = map (fun (_,t) -> List.length t) pdata in
  let s2 = Printf.sprintf " length(ps)=%d" in
  let _ = map (fun t -> report (s2 t)) ls in
  ();;

let rec mitm_recursion i initialized cluster_areacut width pdata ccs =
  let _ = width >> (m (1.0e-6)) or failwith "I'm giving up at small width" in
  let scale = m 1.0 in (* experimental- coordinatewidth/keywidth ratio *)
  let pwidth = width * scale in  
  let cwidth = width * scale in
  let pdata = map (mk_peridata initialized pwidth) pdata in
  let phashlist = map fst pdata in
  if (exists (fun (_,t) -> t=[]) pdata) then true
  else 
    let ccs = mk_cendata cwidth cluster_areacut phashlist ccs in
    if ccs = [] then true
    else 
      let _ = report_stats (i,width,pdata,ccs) in
      mitm_recursion (succ i) true cluster_areacut (width/two) pdata ccs;;

(***********************************************************************)
(* set up hashtables *)
(***********************************************************************)


let mk_hashtbl() = 
  let tbl = Hashtbl.create 20000 in
  let _ = Hashtbl.clear tbl in
  tbl;;

(* let phash1 = mk_hashtbl();; *)

let phashAB = mk_hashtbl();;
let phashBC = mk_hashtbl();;
let phashAC = mk_hashtbl();;


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
  let pdata = [] in
  let cencut = cluster_areacut in
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn t = false in
  let areafn (a,_) = a in
  let keyfns = [] in
  let z2 = zero2 in
  let k2 = merge_I (two*kappa) in
  let ccoord = [k2 (21//10);z2 pi25;z2 pi25;k2 (21//10);k2 two] in
  let fn = (extra,fillfn,outdomfn,areafn,keyfns) in
  let ccs = [(ccoord,cencut,fn);] in 
  let initialized = false in
  mitm_recursion i initialized cluster_areacut width pdata ccs;;

let test1_centralpent_172 = (* repeated calc from pent.ml *)
  let i = 0 in
  let cluster_areacut = aK in
  let width = (m 0.1) in
  let pdata = [] in
  let cencut = cluster_areacut in
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn (_,ts) = false in 
  let areafn (a,_) = a in
  let keyfns = [] in
  let z2 = zero2 pi25 in
  let k2 = merge_I (two*kappa) (172//100) in
  let ccoord = [k2 ;z2;z2;k2;k2] in
  let fn = (extra,fillfn,outdomfn,areafn,keyfns) in
  let ccs = [(ccoord,cencut,fn);] in 
  let initialized = false in
  mitm_recursion i initialized cluster_areacut width pdata ccs;;

let init2Cps = 
  let extra = () in
  let range = (merge_I (172//100) (21//10) ) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB >> dAC or dBC >> dAC or a >> aK) in
  let areafn (a,_,_,_) = a in
  let keyfn w (_,_,_,(dAC,thACB,thCAB,_)) = keys_of_edge w (dAC,thACB,thCAB) in
  let fn = (extra,fillfn,outdomfn,areafn,keyfn) in
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in (* extended coords *)
  let pcoord = [xalpha;alpha;xalpha;alpha] in
  let keys = [] in 
  let area = amin in
  (pcoord,keys,area,fn);;
  
(* it runs, but it terminates quickly. I doubt it is correct. *)
let test_pent4 = 
  let i = 0 in
  let cluster_areacut = four*aK in
  let width = (1//2) in
  (* init peripheral *)
  let ps = [init2Cps] in
  let pdata = [(phashAB,ps);(phashBC,ps);(phashAC,ps)] in
  let _ = map (fun (ph,_) -> Hashtbl.reset ph) pdata in
  (* init central *)
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn _ = false in 
  let areafn (a,_) = a in
  let keyfnAB w fs = key_inverts w (edge5D_ABs fs) in
  let keyfnBC w fs = key_inverts w (edge5D_BCs fs) in
  let keyfnAC w fs = key_inverts w (edge5D_ACs fs) in
  let keyfns = [keyfnAB;keyfnBC;keyfnAC] in
  let fn = (extra,fillfn,outdomfn,areafn,keyfns) in
  (* init central ccs *)
  let z2 = zero2 pi25 in
  let k2 = merge_I (172//100) (21//10) in
  let k2' = merge_I (172//100) two in
  let ccoord = [k2;z2;z2;k2;k2'] in
  let cencut = aK + int 3*epso_I in
  let ccs = [(ccoord,cencut,fn);] in 
  let initialized = false in
  mitm_recursion i initialized cluster_areacut width pdata ccs;;

(* not working, terminating too quickly. *)
let hyp4_precluster = 
  let i = 0 in
  let cluster_areacut = two*aK - zero*epso'_I in (* debug *)
  let width = (1//5) in
  (* init peripheral *)
  let ps = [init2Cps] in
  let pdata = [(phashAB,ps)] in
  let _ = map (fun (ph,_) -> Hashtbl.reset ph) pdata in
  (* init central *)
  let extra = () in
  let range = merge_I (172 // 100) (18//10) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18 // 10 or dBC >> 18 // 10 or disjoint_I dAC range) in
  let areafn (a,_,_,_) = a in
  let keyfn w (_,_,_,(dAC,thACB,thCAB,_)) = key_invert w (dAC,thACB,thCAB) in
  let keyfns = [keyfn] in
  let fn = (extra,fillfn,outdomfn,areafn,keyfns) in
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in (* extended coords *)
  let ccoord = 
    [xalpha;alpha;xalpha;alpha] in
  (* init central ccs *)
  let cencut = aK + epso_I - zero*epso'_I in (* debug *)
  let ccs = [(ccoord,cencut,fn);] in 
  let initialized = false in
  mitm_recursion i initialized cluster_areacut width pdata ccs;;
  

aK;;
let _ = merge_I (two*kappa) (172//100);;
172//100;;
let k2 = merge_I (two*kappa) in
  map zero2 [k2 (21//10);z2 pi25;z2 pi25;k2 (21//10);k2 two] ;;
let ce1 = map mk_interval [(1.74991455078,1.75);(0.31408256632,0.314159265359);(0.942401097038,0.942477796077);(0.349914550781,0.35);(0.333251953125,0.333333333333)];;
  let fillfn1 _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC);;
  fillfn1 () ce1;;

  let ccoordx = 
  let z2 = zero2 pi25 in
  let k2 = merge_I (two*kappa) (172//100) in
  let ccoord = [k2 ;z2;z2;k2;k2] in
  ccoord;;

  let ccxx =  (subdivide_subwidth (m 0.1) ccoordx);;

  let fillxx = 
    let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
    List.length (setify (map (fillfn ()) ccxx));;
