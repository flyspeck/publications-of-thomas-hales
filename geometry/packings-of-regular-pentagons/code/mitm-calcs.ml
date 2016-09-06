(* run the various hypothesis verifications.

   Some of these calculations are memory intensive,
   using between 1 and 2GB of memory.

   I believe that most of the memory  usage goes into the 
   storage (in the pdata) of the keys to the hashtable.
   We could rewrite the code to avoid key storage in pdata,
   but we would have to recompute the fillfn on every pass,
   which would roughly double the runtime.

   It helps to run garbage collection between calculations:
   Gc.full_major();;
   I find that this does not completely free up memory, and
   I often restart ocaml between major calculations to force a 
   memory cleanup.

   The total runtime is approximately 60 hours.
 *)

open Meet;;
open Banana;;

let time_mitm cluster_areacut pdata cfn ccs =
  let i = 0 in
  let width = 1//2 in
  let initialized = false in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;

let unit_extra = ();;

let coord5 (dAB,dBC,dAC) = 
  let z2pi25 = zero2 pi25 in
  [dAB;z2pi25;z2pi25;dBC;dAC];;

let coord6 (dAB,dBC,dAC) = 
  let z2pi25 = zero2 pi25 in
  [dAB;z2pi25;z2pi25;dBC;z2pi25;dAC];;

let coord2Ce = 
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in (* extended coords *)
    [xalpha;alpha;xalpha;alpha];;

let fillfn5 _ [dAB;thABC;thBAC;dBC;dAC] = 
  fillout5D ((dAB,thABC,thBAC),dBC,dAC);;

let fillfn6 _ [dAB;thABC;thBAC;dBC;thCBA;dAC] =
  fillout6D ((dAB,thABC,thBAC),(dBC,thCBA),dAC);;


(* let areafn5D (a,_) = a;; *)

let areafn5 (a,_) = a;;

let areafn2Ce (a,_,_,_) = a;;

let forall_dom f (a,dds) = 
  forall f (map (fun (t1,t2,t3) -> (a,t1,t2,t3)) dds);;

let forall_alpha0 f t = 
  let ts = Pet.periodize_pent0 t in
  forall f ts;;

let forall_alpha f t = 
  let ts = Pet.periodize_pent t in
  forall f ts;;

let forall_alpha_pair f (t,t') = 
    let s = Pet.periodize_pent t in
    let s'= Pet.periodize_pent t' in
    forall f (outer pair s s');;


(* in case pent2_postcluster the cluster is not a pseudo-dimer
   but shares the egressive edge with a pseudo-dimer.
   The angle condition on the egress edge is antisymmetric.
   Thus, the pent2 cluster is enirely outof domain if it is fully in
   the pseudo-dimer domain *)

(* 
   The way the exact equality th+th' = pi25 is handled is a bit
   subtle.
   In the article, large is defined as alpha > pi15 and alpha < pi25.
   If the interval th+th' contains pi25, then when periodize_pent0
   is called, the transform of the interval th+th' contains 0.
   In this case, the test forall_alpha_constraint_pseudo_dimer fails.
   Thus we don't need the explicit condition alpha << pi25.
   (But it would not hurt to add it.)
*)

let _ = exists (mem_I 0.0) (Pet.periodize_pent0 (pi25));;

let forall_alpha_constraint_pseudo_dimer (th,th') = 
  forall_alpha0 (fun alpha -> alpha >>pi15) (th+th');;

let d_subcrit_shared = 
  let _ = area_I (two*kappa) (two*kappa) (21//10) >> aK or failwith "21" in
  merge_I (172//100) (21//10);;

let d_subcrit_contact = 
  merge_I (172//100) two;;

let d_shared_pseudo = merge_I (172//100) (18//10);;

let d_egress = 
  let _ = area_I (172//100) (two*kappa) (204//100) >> aK + epsN_I or
      failwith "204" in
  merge_I (18//10) (204//100);;

let d_third_pseudo = merge_I (two*kappa) (18//10);;

let edge5D_ABs (_,fs) = map (fun ((l,t,t',_),_,_)-> (l,t,t')) fs;;

let edge5D_BCs (_,fs) = map (fun (_,(l,t,t',_),_)-> (l,t,t')) fs;;

let edge5D_ACs (_,fs) = map (fun (_,_,(l,t,t',_))-> (l,t,t')) fs;;

let _ = fun t -> edge5D_ACs (the (fillout5D t));;

let ckeyfnBC w fs = key_inverts w (edge5D_BCs fs);;

let ckeyfnAC w fs = key_inverts w (edge5D_ACs fs);;

let ckeyfnAB w fs = key_inverts w (edge5D_ABs fs);;

let ckeyfn2Ce w (_,_,_,(dAC,thACB,thCAB,_)) = 
  key_invert w (dAC,thACB,thCAB);;

let ckeyfn6AB w (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = key_invert w (dAB,thABC,thBAC);;

let ckeyfn6BC w (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = key_invert w (dBC,thCBA,thBCA);;

let ckeyfn6AC w (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = key_invert w (dAC,thACB,thCAB);;

let init2Cps = (* standard 2C settings for peripheral triangles *)
  let fillfn () = mk2Ce d_subcrit_shared in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB >> dAC or dBC >> dAC or a >> aK) in
  let keyfn w (_,_,_,(dAC,thACB,thCAB,_)) = keys_of_edge w (dAC,thACB,thCAB) in
  let fn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfn) in
  let keys = [] in 
  let area = amin in
  (fn,[(coord2Ce,keys,area)]);;

let init2Cps_isosceles_AB_AC = (* 2C settings with isosceles AB=AC *)
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		 (dAC,thACB,thCAB,arcB)) = 
    (disjoint_I dAB dAC or dBC >> dAC or a >> aK) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

let init2Cps_isosceles_BC_AC = (* 2C settings with isosceles BC=AC *)
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		 (dAC,thACB,thCAB,arcB)) = 
    (disjoint_I dBC dAC or dAB >> dAC or a >> aK) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

(* N.B. We could add more constraints
   or dAB >> dAC or dBC >> dAC 
   or disjoint_I dAC ( merge_I (two*kappa) (179//100)) *)

let init2Cps_isosceles_AC = (* 2C settings with isosceles AC=either other *)
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		 (dAC,thACB,thCAB,arcB)) = 
    (a >> aK or (disjoint_I dBC dAC && disjoint_I dAB dAC)) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;


let reset_peri ps = 
  let _ = Hashtbl.reset phash in
  Some(phash,ps);;

let mk_peri = 0;;

(* ************************************************************ *)
(* start calcs *)
(* ************************************************************ *)

let test1_centralpent_1237() = (* repeated calc from pent.ml *)
  let cluster_areacut = (m 1.2 (* debug *)) in
  let pdata = None in
  let cencut = cluster_areacut.high in
  let outdomfn _ = false in
  let keyfns = [] in
  let k2 = merge_I (two*kappa) in
  let dAB_dBC_dAC = (k2(21//10),k2(21//10),k2(two)) in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let ccs = [(coord5(dAB_dBC_dAC),cencut);] in 
  time_mitm cluster_areacut pdata cfn ccs;;

let test1_centralpent_172() = (* repeated calc from pent.ml *)
  let cluster_areacut = aK in
  let pdata = None in
  let cencut = cluster_areacut.high in
  let outdomfn _ = false in 
  let keyfns = [] in
  let k2 = merge_I (two*kappa) (172//100) in
  let dAB_dBC_dAC = (k2,k2,k2) in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let ccs = [(coord5(dAB_dBC_dAC),cencut);] in 
  time_mitm cluster_areacut pdata cfn ccs;;
    
(* June 7, 2016: completed running : *)
(*
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=204
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=2828
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=29756
 length(ps)=24180 maxkey=100 keysum=546726 phash=1880
i=4, w=0.03125, length(ccs)=95128
 length(ps)=104230 maxkey=75 keysum=2173318 phash=5175
i=5, w=0.01562, length(ccs)=20528
 length(ps)=640510 maxkey=75 keysum=12656700 phash=10937
val calc_pent4 : bool = true
*)
(* Needs about 1GB of memory. A few hours to run on my laptop. *)
(* [QPJDYDB] -deprecated version *)
let calc_pent4_postcluster() = 
  let cluster_areacut = four*aK in
  let pdata = reset_peri init2Cps in 
  let outdomfn _ = false in 
  let keyfns = [ckeyfnAB;ckeyfnBC;ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let dAB_dBC_dAC = (d_subcrit_shared,d_subcrit_shared,d_subcrit_contact) in
  let cencut = (aK + int 3*epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report "pent4_postcluster" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 14, 2016. This includes calc_pent4_postcluster. So that can be removed.
pent4_6D_postcluster_experimental
i=0, w=0.50000, length(ccs)=27
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=864
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=16545
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=229169
 length(ps)=24180 maxkey=100 keysum=546726 phash=1867
i=4, w=0.03125, length(ccs)=648475
 length(ps)=104230 maxkey=75 keysum=2173318 phash=4958
i=5, w=0.01562, length(ccs)=29554
 length(ps)=553293 maxkey=75 keysum=11021385 phash=9007
CPU time (user): 14870.108
val calc_pent4_6D_postcluster : bool = true
*)
(* [QPJDYDB] *)
let calc_pent4_6D_postcluster() = 
  let cluster_areacut = four*aK in
  let pdata = reset_peri init2Cps in 
  (* symmetry: in domain AB longest, then BC, then AC *)
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << dBC or dAB << dAC or dBC << dAC) in
  let keyfns = [ckeyfn6AB;ckeyfn6BC;ckeyfn6AC] in
  let cfn = (unit_extra,fillfn6,outdomfn,areafn2Ce,keyfns) in
  let dAB_dBC_dAC = (d_subcrit_shared,d_subcrit_shared,d_subcrit_shared) in
  let cencut = (aK + int 3*epsN_I).high in
  let ccs = [(coord6 dAB_dBC_dAC,cencut);] in 
  let _ = report "pent4_6D_postcluster_experimental" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* started about 2:30pm on June 14, 2016
pent3_6D_postcluster
i=0, w=0.50000, length(ccs)=27
 length(ps)=205 maxkey=18 keysum=2210 phash=24
i=1, w=0.25000, length(ccs)=1080
 length(ps)=1165 maxkey=64 keysum=25565 phash=128
i=2, w=0.12500, length(ccs)=17694
 length(ps)=6700 maxkey=60 keysum=122464 phash=359
i=3, w=0.06250, length(ccs)=235618
 length(ps)=31676 maxkey=100 keysum=726422 phash=1570
i=4, w=0.03125, length(ccs)=1577180
 length(ps)=94118 maxkey=100 keysum=2017786 phash=4337
i=5, w=0.01562, length(ccs)=1039552
 length(ps)=191231 maxkey=64 keysum=3787986 phash=7632
i=6, w=0.00781, length(ccs)=100559
 length(ps)=140157 maxkey=48 keysum=2590521 phash=6318
i=7, w=0.00391, length(ccs)=183
 length(ps)=55437 maxkey=45 keysum=986729 phash=2406
CPU time (user): 73430.968
val calc_pent3_6D_postcluster : bool = true
*)
(* [HUQEJAT] *)
let calc_pent3_6D_postcluster() = 
  let cluster_areacut = int 3*aK + epsM_I in
  (* deform both sides separately so that both peripherals are isosceles *)
  let pdata = reset_peri init2Cps_isosceles_AC in 
  (* symmetry: in domain AB longer than BC. AC not shared. *)
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),_) =
    (dAB << dBC) in
  let keyfns = [ckeyfn6AB;ckeyfn6BC] in
  let cfn = (unit_extra,fillfn6,outdomfn,areafn2Ce,keyfns) in
  let d_subcrit_isosc = merge_I (172//100) (179//100) in (* XX use this *)
  let d_short = merge_I (two*kappa) (202//100) in (* see "202" *)
  let dAB_dBC_dAC = (d_subcrit_shared,d_subcrit_shared,d_short) in
  let cencut = (aK + two*epsN_I + epsM_I).high in
  let ccs = [(coord6 dAB_dBC_dAC,cencut);] in 
  let _ = report "pent3_6D_postcluster" in
  time_mitm cluster_areacut pdata cfn ccs;;


(* up to i=3 the peripheral numbers are the same as in pent4.
   This suggests that no case-dependent filtering happens *)
(*
  -- this comes very close to running out of memory.
pent3AB
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=178
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=1872
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=16012
 length(ps)=24180 maxkey=100 keysum=546726 phash=1781
i=4, w=0.03125, length(ccs)=63824
 length(ps)=104194 maxkey=75 keysum=2172586 phash=4732
i=5, w=0.01562, length(ccs)=77121
 length(ps)=579101 maxkey=75 keysum=11492761 phash=11308
i=6, w=0.00781, length(ccs)=42474
 length(ps)=1676426 maxkey=60 keysum=32468871 phash=18190
i=7, w=0.00391, length(ccs)=3202
 length(ps)=1189092 maxkey=60 keysum=22413008 phash=18315
CPU time (user): 17214.976
val calc_pent3AB_postcluster : bool = true
*)
(* [HUQEJAT] *)
let calc_pent3AB_postcluster() =
  let cluster_areacut = int 3*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn _ = false in 
  let keyfns = [ckeyfnBC; ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let _ = area_I (172//100) (172//100) (202//100) >> 
    (aK + two * epsN_I + epsM_I) or failwith "202" in
  let d_short = merge_I (two*kappa) (202//100) in
  (* AB is not shared with a subcritical. It can be short. *)
  let dAB_dBC_dAC = (d_short,d_subcrit_shared,d_subcrit_contact) in
  let cencut = (aK + two*epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent3AB") in
  time_mitm cluster_areacut pdata cfn ccs;;


(* done, June 12, 2016 restarted ocaml to clear memory 
 pent3BC
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=204
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=2470
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=21713
 length(ps)=24180 maxkey=100 keysum=546726 phash=1787
i=4, w=0.03125, length(ccs)=90059
 length(ps)=104230 maxkey=75 keysum=2173318 phash=4650
i=5, w=0.01562, length(ccs)=79275
 length(ps)=487032 maxkey=75 keysum=9597249 phash=9805
i=6, w=0.00781, length(ccs)=17076
 length(ps)=891165 maxkey=60 keysum=17473751 phash=12487
i=7, w=0.00391, length(ccs)=242
 length(ps)=433719 maxkey=60 keysum=8296300 phash=9928
CPU time (user): 7679.304
val calc_pent3BC_postcluster : bool = true
*)
(* [HUQEJAT] *)
let calc_pent3BC_postcluster() = 
  let cluster_areacut = int 3*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn _ = false in 
  let keyfns = [ckeyfnAB;ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let d_short = merge_I (two*kappa) (202//100) in
  let dAB_dBC_dAC=(d_subcrit_shared,d_short,d_subcrit_contact) in
  let cencut = (aK + int 2*epsN_I +epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent3BC") in
  time_mitm cluster_areacut pdata cfn ccs;;


(* (re)done June 12, 2016 
pent3AC
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=180
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=2619
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=27287
 length(ps)=24180 maxkey=100 keysum=546726 phash=1840
i=4, w=0.03125, length(ccs)=114408
 length(ps)=104229 maxkey=75 keysum=2173302 phash=4919
i=5, w=0.01562, length(ccs)=81368
 length(ps)=510482 maxkey=75 keysum=10203859 phash=10036
i=6, w=0.00781, length(ccs)=22518
 length(ps)=357195 maxkey=60 keysum=6849153 phash=9474
i=7, w=0.00391, length(ccs)=247
 length(ps)=146631 maxkey=45 keysum=2635204 phash=4944
CPU time (user): 4953.868
val calc_pent3AC_postcluster : bool = true
  *)
(* [HUQEJAT] *)
let calc_pent3AC_postcluster() = 
  let cluster_areacut = int 3*aK +epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn _ = false in 
  let keyfns = [ckeyfnAB; ckeyfnBC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let d_short = merge_I (two*kappa) (202//100) in
  (* AC not shared with a subcritical. It can be short. *)
  let dAB_dBC_dAC=(d_subcrit_shared,d_subcrit_shared,d_short) in
  let cencut = (aK + int 2*epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent3AC") in
  time_mitm cluster_areacut pdata cfn ccs;;


(* redone June 13, 2016
pent2_case0 covers 2C+2C situation
i=0, w=0.50000, length(ccs)=204
 length(ps)=210 maxkey=18 keysum=2290 phash=32
i=1, w=0.25000, length(ccs)=673
 length(ps)=1145 maxkey=64 keysum=28215 phash=160
i=2, w=0.12500, length(ccs)=2952
 length(ps)=5923 maxkey=80 keysum=116268 phash=493
i=3, w=0.06250, length(ccs)=14883
 length(ps)=24180 maxkey=100 keysum=546726 phash=2015
i=4, w=0.03125, length(ccs)=58672
 length(ps)=102809 maxkey=75 keysum=2146056 phash=4871
i=5, w=0.01562, length(ccs)=58365
 length(ps)=376767 maxkey=75 keysum=7558950 phash=8679
i=6, w=0.00781, length(ccs)=1531
 length(ps)=287414 maxkey=48 keysum=5584270 phash=7523
i=7, w=0.00391, length(ccs)=1
 length(ps)=11061 maxkey=45 keysum=215495 phash=915
CPU time (user): 2830.476
val calc_pent2_postcluster_case0 : bool = true
 *)
(* FHBGHHY *)
let calc_pent2_postcluster_case0() = 
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let range = merge_I (172//100) (193//100) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18//10 or dBC >> 179//100 or disjoint_I dAC range or
       forall_alpha_constraint_pseudo_dimer (thABC,thBAC)) in
    (* note AB is the egressive edge, AC is the shared edge *)
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  (* init central ccs *)
  let cencut = (aK + epsN_I + epsM_I).high in 
  let assertAC = area_I (193//100) (18//10) (two*kappa) >>. cencut or 
    failwith "please reset 1.93 bound and rerun" in
  let assertBC = area_I (18//10) (172//100) (179//100) >>. cencut or
    failwith "please reset 1.79 bound and rerun" in
  let ccs = [(coord2Ce,cencut);] in 
  let _ = report "pent2_case0 covers 2C+2C situation" in
  time_mitm cluster_areacut pdata cfn ccs;;



(* rerun June 13, 2016
 pent2_postcluster_case1:AB shared, AC egressive. 
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=54
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=205
 length(ps)=5923 maxkey=80 keysum=116268 phash=385
i=3, w=0.06250, length(ccs)=781
 length(ps)=23503 maxkey=100 keysum=532919 phash=1346
i=4, w=0.03125, length(ccs)=2183
 length(ps)=60670 maxkey=75 keysum=1307955 phash=2786
i=5, w=0.01562, length(ccs)=555
 length(ps)=62091 maxkey=60 keysum=1270767 phash=2752
i=6, w=0.00781, length(ccs)=37
 length(ps)=25793 maxkey=45 keysum=493034 phash=1066
CPU time (user): 393.188
val calc_pent2_postcluster_case1 : bool = true
*)
(* FHBGHHY *)
let calc_pent2_postcluster_case1() = 
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		(dAC,thACB,thCAB,arcB)) = 
       forall_alpha_constraint_pseudo_dimer (thACB,thCAB) in
  (* note AB is shared, AC is egressive *)
  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let dAB_dBC_dAC=(d_subcrit_shared,d_third_pseudo,d_18) in
  let cencut = (aK + epsN_I + epsM_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent2_postcluster_case1:AB shared, AC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(*
rerun June 13, 2016
pent2_postcluster_case2:AB shared, BC egressive. 
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=72
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=333
 length(ps)=5923 maxkey=80 keysum=116268 phash=406
i=3, w=0.06250, length(ccs)=1320
 length(ps)=24093 maxkey=100 keysum=545130 phash=1491
i=4, w=0.03125, length(ccs)=3005
 length(ps)=71321 maxkey=75 keysum=1520743 phash=3267
i=5, w=0.01562, length(ccs)=2381
 length(ps)=64337 maxkey=75 keysum=1282728 phash=3840
i=6, w=0.00781, length(ccs)=543
 length(ps)=37205 maxkey=60 keysum=723806 phash=2637
i=7, w=0.00391, length(ccs)=33
 length(ps)=7684 maxkey=45 keysum=148313 phash=937
CPU time (user): 516.204
val calc_pent2_postcluster_case2 : bool = true
*)
(* FHBGHHY *)
let calc_pent2_postcluster_case2() = 
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
    forall_alpha_constraint_pseudo_dimer (thBCA,thCBA) in (* case *)
    (* note AB is shared, BC is egressive *)
  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let d_contact = merge_I (two*kappa) two in
  let dAB_dBC_dAC=(d_subcrit_shared,d_18,d_contact) in (* case *)
  let cencut = (aK + epsN_I + epsM_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent2_postcluster_case2:AB shared, BC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(*
rerun June 13, 2016
pent2_postcluster_case3:BC shared, AC egressive. 
i=0, w=0.50000, length(ccs)=7
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=46
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=108
 length(ps)=5923 maxkey=80 keysum=116268 phash=363
i=3, w=0.06250, length(ccs)=533
 length(ps)=22932 maxkey=100 keysum=523218 phash=1293
i=4, w=0.03125, length(ccs)=908
 length(ps)=46753 maxkey=75 keysum=1024227 phash=2500
i=5, w=0.01562, length(ccs)=142
 length(ps)=32599 maxkey=60 keysum=625233 phash=2094
i=6, w=0.00781, length(ccs)=21
 length(ps)=5172 maxkey=45 keysum=100067 phash=674
CPU time (user): 266.188
val calc_pent2_postcluster_case3 : bool = true
*)
(* FHBGHHY *)
let calc_pent2_postcluster_case3() = 
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
    forall_alpha_constraint_pseudo_dimer (thACB,thCAB) in (* case *)
  let keyfns = [ckeyfnBC] in (* case *)
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let dAB_dBC_dAC = (d_third_pseudo,d_subcrit_shared,d_18) in (*case*)
  let cencut = (aK + epsN_I + epsM_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent2_postcluster_case3:BC shared, AC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(*
rerun June 13, 2016
pent2_postcluster_case4:BC shared, AB egressive. 
i=0, w=0.50000, length(ccs)=7
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=56
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=227
 length(ps)=5923 maxkey=80 keysum=116268 phash=393
i=3, w=0.06250, length(ccs)=1220
 length(ps)=23910 maxkey=100 keysum=541885 phash=1464
i=4, w=0.03125, length(ccs)=3560
 length(ps)=60291 maxkey=75 keysum=1272339 phash=3233
i=5, w=0.01562, length(ccs)=3425
 length(ps)=89268 maxkey=75 keysum=1814594 phash=4151
i=6, w=0.00781, length(ccs)=867
 length(ps)=56043 maxkey=60 keysum=1087994 phash=3297
i=7, w=0.00391, length(ccs)=73
 length(ps)=16614 maxkey=45 keysum=322667 phash=1284
CPU time (user): 584.42
val calc_pent2_postcluster_case4 : bool = true
*)
(* FHBGHHY *)
let calc_pent2_postcluster_case4() = 
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
    forall_alpha_constraint_pseudo_dimer (thABC,thBAC) in (* case *)
  let keyfns = [ckeyfnBC] in (* case *)
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let d_contact = merge_I (two*kappa) two in
  let dAB_dBC_dAC = (d_18,d_subcrit_shared,d_contact) in (* case *)
  let cencut = (aK + epsN_I + epsM_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent2_postcluster_case4:BC shared, AB egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(*
 precluster1_case0
i=0, w=0.50000, length(ccs)=117
 length(ps)=210 maxkey=18 keysum=2290 phash=32
i=1, w=0.25000, length(ccs)=242
 length(ps)=1145 maxkey=64 keysum=28215 phash=160
i=2, w=0.12500, length(ccs)=1316
 length(ps)=5923 maxkey=80 keysum=116268 phash=494
i=3, w=0.06250, length(ccs)=6575
 length(ps)=24180 maxkey=100 keysum=546726 phash=1824
i=4, w=0.03125, length(ccs)=25772
 length(ps)=94159 maxkey=75 keysum=1964242 phash=4137
i=5, w=0.01562, length(ccs)=31544
 length(ps)=305333 maxkey=75 keysum=6064392 phash=6673
i=6, w=0.00781, length(ccs)=19239
 length(ps)=722584 maxkey=60 keysum=14248464 phash=7068
i=7, w=0.00391, length(ccs)=33
 length(ps)=511557 maxkey=60 keysum=9880684 phash=5928
CPU time (user): 4609.216
val precluster1_case0 : bool = true
*)
(* done June 10 *)
(* NKQNXUN *)
let precluster1_case0() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let range = merge_I (18//10) (192//100) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (disjoint_I dAC range or disjoint_I dAB range or disjoint_I dBC (merge_I (two*kappa) (17//10))) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  (* init central ccs *)
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord2Ce,cencut);] in 
  let _ = area_I (18//10) (192//100) (two*kappa) >> aK+epsN_I or 
    failwith "range_check" in
  let _ = area_I (18//10) (18//10) (17//10) >> aK+epsN_I or
    failwith "range_check" in
  let _ = report "precluster1_case0" in
  time_mitm cluster_areacut pdata cfn ccs;;

(*
precluster1 case1 midpointer
i=0, w=0.50000, length(ccs)=4
 length(ps)=210 maxkey=18 keysum=2290 phash=20
i=1, w=0.25000, length(ccs)=12
 length(ps)=1025 maxkey=64 keysum=25304 phash=96
i=2, w=0.12500, length(ccs)=28
 length(ps)=4942 maxkey=80 keysum=97104 phash=273
i=3, w=0.06250, length(ccs)=96
 length(ps)=17352 maxkey=100 keysum=402550 phash=1042
i=4, w=0.03125, length(ccs)=144
 length(ps)=27954 maxkey=60 keysum=589836 phash=1469
i=5, w=0.01562, length(ccs)=19
 length(ps)=51395 maxkey=60 keysum=1078836 phash=1391
CPU time (user): 168.652
val precluster1_case1 : bool = true
*)
(* NKQNXUN *)
let precluster1_case1() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central *)
  (* the midpointer edge AC gives triangle 1,kappa,1.8 *)
  let theta' = iarc one (18//10) kappa in
  let out_of_theta' t = 
    forall_alpha (fun t -> disjoint_I theta' (abs_I t)) t in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = out_of_theta' thACB in
    (* note AB is shared, AC is egressive and contact *)
  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_18 = (18//10) in
  let d_shared = merge_I (18//10) (192//100) in
  let d_short = merge_I (two*kappa) (17//10) in
  let dAB_dBC_dAC = (d_shared,d_short,d_18) in
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster1 case1 midpointer") in
  time_mitm cluster_areacut pdata cfn ccs;;


(* done June 10, 2016:
precluster1 case2 slider
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=20
i=1, w=0.25000, length(ccs)=66
 length(ps)=1145 maxkey=64 keysum=28215 phash=96
i=2, w=0.12500, length(ccs)=286
 length(ps)=5923 maxkey=80 keysum=116268 phash=337
i=3, w=0.06250, length(ccs)=1247
 length(ps)=24179 maxkey=100 keysum=546710 phash=1459
i=4, w=0.03125, length(ccs)=1871
 length(ps)=84884 maxkey=75 keysum=1802461 phash=3383
i=5, w=0.01562, length(ccs)=1717
 length(ps)=137741 maxkey=75 keysum=2858631 phash=4165
i=6, w=0.00781, length(ccs)=926
 length(ps)=119119 maxkey=60 keysum=2293112 phash=3467
CPU time (user): 809.716
val precluster1_case2 : bool = true
  *)
(* NKQNXUN *)
let precluster1_case2() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let notslider1 (t, t') = disjoint_I zero (t+t') in
  let notslider (t, t') = 
    forall_alpha_pair notslider1 (t,t') in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
    (disjoint_I dAC (18//10) && disjoint_I dBC (18//10) or
       notslider (thACB,thCAB)) in 
    (* note AB is shared, AC is contact slider, either AB,AC egressive *)
  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_shared = merge_I (18//10) (192//100) in
  let d_full = merge_I (two*kappa) (192//100) in
  let dAB_dBC_dAC = (d_shared,d_full,d_full) in
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster1 case2 slider") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* next precluster2, done, June 10
precluster2_case0
i=0, w=0.50000, length(ccs)=252
 length(ps)=210 maxkey=18 keysum=2290 phash=32
i=1, w=0.25000, length(ccs)=949
 length(ps)=1145 maxkey=64 keysum=28215 phash=160
i=2, w=0.12500, length(ccs)=3315
 length(ps)=5923 maxkey=80 keysum=116268 phash=480
i=3, w=0.06250, length(ccs)=16099
 length(ps)=24180 maxkey=100 keysum=546726 phash=2016
i=4, w=0.03125, length(ccs)=61245
 length(ps)=102924 maxkey=75 keysum=2148172 phash=4811
i=5, w=0.01562, length(ccs)=72771
 length(ps)=365407 maxkey=75 keysum=7377912 phash=9040
i=6, w=0.00781, length(ccs)=48573
 length(ps)=536620 maxkey=60 keysum=10578028 phash=8798
i=7, w=0.00391, length(ccs)=29053
 length(ps)=907408 maxkey=60 keysum=17794227 phash=8325
i=8, w=0.00195, length(ccs)=2940
 length(ps)=179253 maxkey=45 keysum=3293751 phash=4553
CPU time (user): 7714.216
val precluster2_case0 : bool = true *)
(* RWWHLQT pseudo2 *)
let precluster2_case0() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central, 2C+2C, AB is longest edge on T0 *)
  let fillfn () = mk2Ce d_shared_pseudo in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		(dAC,thACB,thCAB,arcB)) = 
    (disjoint_I dAC d_shared_pseudo or disjoint_I dAB d_shared_pseudo or 
       disjoint_I dBC d_third_pseudo or
    dAB << dAC or dAB << dBC) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  (* init central ccs *)
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord2Ce,cencut);] in 
  let _ = report "precluster2_case0" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* 
precluster2 case1 midpointer
i=0, w=0.50000, length(ccs)=4
 length(ps)=210 maxkey=18 keysum=2290 phash=20
i=1, w=0.25000, length(ccs)=16
 length(ps)=1145 maxkey=64 keysum=28215 phash=96
i=2, w=0.12500, length(ccs)=61
 length(ps)=5923 maxkey=80 keysum=116268 phash=305
i=3, w=0.06250, length(ccs)=170
 length(ps)=23926 maxkey=100 keysum=540416 phash=1132
i=4, w=0.03125, length(ccs)=423
 length(ps)=40047 maxkey=75 keysum=843150 phash=1689
i=5, w=0.01562, length(ccs)=834
 length(ps)=72935 maxkey=60 keysum=1526252 phash=2052
i=6, w=0.00781, length(ccs)=723
 length(ps)=184917 maxkey=60 keysum=3793816 phash=2672
i=7, w=0.00391, length(ccs)=90
 length(ps)=136332 maxkey=60 keysum=2680781 phash=1937
CPU time (user): 817.244
val precluster2_case1 : bool = true
*)
(* RWWHLQT pseudo2 *)
let precluster2_case1() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central, midpointer A->C, isosceles, AB shared. *)
  (* midpointer edge AC gives triangle 1,kappa,1.8 *)
  let out_of_midpointer dAC thACB =
    forall_alpha (fun t -> disjoint_I kappa (iloc one dAC (abs_I t))) thACB in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = out_of_midpointer dAC thACB 
    or (disjoint_I dAB dAC && disjoint_I dBC dAC) 
    or (disjoint_I dAB d_shared_pseudo) 
    or (disjoint_I dAC d_third_pseudo)
    or (disjoint_I dBC d_third_pseudo) in
  let keyfns = [ckeyfnAB] in (* case AB *)
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let dAB_dBC_dAC = (d_shared_pseudo,d_third_pseudo,d_third_pseudo) in
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster2 case1 midpointer") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* done:
precluster2 case2 slider
i=0, w=0.50000, length(ccs)=7
 length(ps)=210 maxkey=18 keysum=2290 phash=20
i=1, w=0.25000, length(ccs)=28
 length(ps)=1145 maxkey=64 keysum=28215 phash=112
i=2, w=0.12500, length(ccs)=197
 length(ps)=5923 maxkey=80 keysum=116268 phash=333
i=3, w=0.06250, length(ccs)=672
 length(ps)=24048 maxkey=100 keysum=544298 phash=1218
i=4, w=0.03125, length(ccs)=1069
 length(ps)=75067 maxkey=75 keysum=1615927 phash=2883
i=5, w=0.01562, length(ccs)=629
 length(ps)=63638 maxkey=60 keysum=1302287 phash=2941
CPU time (user): 440.08
val precluster2_case2 : bool = true
 *)
(* RWWHLQT pseudo2 *)
let precluster2_case2() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central, AB shared edge, isosc. slider AC.  *)
  let notslider1 (t, t') = disjoint_I zero (t+t') in
  let notslider (t, t') = 
    forall_alpha_pair notslider1 (t,t') in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
      (disjoint_I dAC dAB && disjoint_I dAC dBC)
      or        notslider (thACB,thCAB) in 
    (* note AB is shared, AC is contact slider, either AB,AC egressive *)
  let keyfns = [ckeyfnAB] in (* case *)
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let dAB_dBC_dAC = (d_shared_pseudo,d_third_pseudo,d_third_pseudo) in
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster2 case2 slider") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* done: June 8, dimer.
dimer with Tin isosceles
i=0, w=0.50000, length(ccs)=261
 length(ps)=205 maxkey=18 keysum=2210 phash=32
i=1, w=0.25000, length(ccs)=1813
 length(ps)=1085 maxkey=64 keysum=24567 phash=160
i=2, w=0.12500, length(ccs)=11000
 length(ps)=5339 maxkey=60 keysum=102918 phash=426
i=3, w=0.06250, length(ccs)=56598
 length(ps)=16448 maxkey=100 keysum=375387 phash=1829
i=4, w=0.03125, length(ccs)=135282
 length(ps)=29827 maxkey=75 keysum=642091 phash=3425
i=5, w=0.01562, length(ccs)=149587
 length(ps)=63553 maxkey=60 keysum=1296080 phash=4396
i=6, w=0.00781, length(ccs)=121837
 length(ps)=60677 maxkey=60 keysum=1127945 phash=3598
i=7, w=0.00391, length(ccs)=18442
 length(ps)=22548 maxkey=45 keysum=404523 phash=1879
CPU time (user): 4955.264
val dimer_isosceles_precluster : bool = true
*)
(* KUGAKIK dimer-isosc *)
let dimer_isosceles_precluster() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps_isosceles_AB_AC in (* note isosceles contraint on Tin *)
  (* init central *)
  let fillfn () = mk2Ce d_subcrit_shared in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		(dAC,thACB,thCAB,arcB)) = 
    (dAB >> dAC or dBC >> dAC or disjoint_I dAC d_subcrit_shared) in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,[ckeyfn2Ce]) in
  (* init central ccs *)
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord2Ce,cencut);] in 
  let _ = report ("dimer with Tin isosceles") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 9, 2016. Memory failure: (on 3.7GB computer) *)
(* 
i=0, w=0.50000, length(ccs)=252
 length(ps)=210 maxkey=18 keysum=2290 phash=32
i=1, w=0.25000, length(ccs)=950
 length(ps)=1145 maxkey=64 keysum=28215 phash=160
i=2, w=0.12500, length(ccs)=4556
 length(ps)=5923 maxkey=80 keysum=116268 phash=479
i=3, w=0.06250, length(ccs)=23391
 length(ps)=24180 maxkey=100 keysum=546726 phash=2001
i=4, w=0.03125, length(ccs)=88294
 length(ps)=102654 maxkey=75 keysum=2143078 phash=4754
i=5, w=0.01562, length(ccs)=129534
 length(ps)=377416 maxkey=75 keysum=7540074 phash=8495
i=6, w=0.00781, length(ccs)=176206
 length(ps)=982750 maxkey=60 keysum=19206568 phash=10958
Failed after (user) CPU time of 12897.904: Out of memory during evaluation.

Rerunning with isosceles constraint, the process
gets killed (not by me):
...
i=10, w=0.00049, length(ccs)=449541
 length(ps)=692552 maxkey=36 keysum=12078074 phash=19039
i=11, w=0.00024, length(ccs)=580385
 length(ps)=1009136 maxkey=36 keysum=17587311 phash=27470
i=12, w=0.00012, length(ccs)=626882
Killed
*)
(* June 9, it dies on me: *)
(* experimental version finishes!
 precluster4_case0 isosceles Tin AB=AC --experimental
i=0, w=0.50000, length(ccs)=252
 length(ps)=205 maxkey=18 keysum=2210 phash=32
i=1, w=0.25000, length(ccs)=939
 length(ps)=1085 maxkey=64 keysum=24567 phash=160
i=2, w=0.12500, length(ccs)=4520
 length(ps)=5339 maxkey=60 keysum=102918 phash=425
i=3, w=0.06250, length(ccs)=23120
 length(ps)=16448 maxkey=100 keysum=375387 phash=1792
i=4, w=0.03125, length(ccs)=74980
 length(ps)=29804 maxkey=75 keysum=641711 phash=3199
i=5, w=0.01562, length(ccs)=109821
 length(ps)=69786 maxkey=60 keysum=1414763 phash=4471
i=6, w=0.00781, length(ccs)=131857
 length(ps)=127273 maxkey=48 keysum=2469680 phash=5731
i=7, w=0.00391, length(ccs)=147996
 length(ps)=260315 maxkey=48 keysum=4833546 phash=8035
i=8, w=0.00195, length(ccs)=164419
 length(ps)=386003 maxkey=36 keysum=6820911 phash=10844
i=9, w=0.00098, length(ccs)=166327
 length(ps)=360713 maxkey=36 keysum=6297826 phash=10593
i=10, w=0.00049, length(ccs)=79629
 length(ps)=359161 maxkey=36 keysum=6260804 phash=11178
i=11, w=0.00024, length(ccs)=442
 length(ps)=173580 maxkey=36 keysum=3022141 phash=6966
CPU time (user): 14058.144
val precluster4_case0_experimental : bool = true
*)
(* BXZBPJW pseudo-area *)
let precluster4_case0_experimental() = 
  let cluster_areacut = two*aK - epsM_I in
  let pdata = reset_peri init2Cps_isosceles_AB_AC in
  let fillfn () = mk2Ce d_shared_pseudo in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18//10 or dBC >> 18//10 or disjoint_I dAC d_shared_pseudo) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  let cencut = (aK + epsN_I - epsM_I).high in 
  let ccs = [(coord2Ce,cencut);] in 
  let _ = report "precluster4_case0 isosceles Tin AB=AC --experimental" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* done. experimental constant
 precluster4_case1 isosceles Tin BC=AC experimental
i=0, w=0.50000, length(ccs)=252
 length(ps)=205 maxkey=18 keysum=2210 phash=32
i=1, w=0.25000, length(ccs)=939
 length(ps)=1085 maxkey=64 keysum=24567 phash=160
i=2, w=0.12500, length(ccs)=4520
 length(ps)=5339 maxkey=60 keysum=102918 phash=425
i=3, w=0.06250, length(ccs)=23119
 length(ps)=16448 maxkey=100 keysum=375387 phash=1799
i=4, w=0.03125, length(ccs)=81823
 length(ps)=29807 maxkey=75 keysum=641763 phash=3320
i=5, w=0.01562, length(ccs)=113460
 length(ps)=70888 maxkey=60 keysum=1435769 phash=4608
i=6, w=0.00781, length(ccs)=150496
 length(ps)=144768 maxkey=60 keysum=2807985 phash=6745
i=7, w=0.00391, length(ccs)=225086
 length(ps)=332199 maxkey=60 keysum=6147846 phash=10241
i=8, w=0.00195, length(ccs)=221131
 length(ps)=739732 maxkey=45 keysum=13110831 phash=18276
i=9, w=0.00098, length(ccs)=171971
 length(ps)=656717 maxkey=45 keysum=11504972 phash=20868
i=10, w=0.00049, length(ccs)=80652
 length(ps)=463893 maxkey=36 keysum=8088731 phash=13093
i=11, w=0.00024, length(ccs)=442
 length(ps)=214179 maxkey=36 keysum=3729458 phash=7840
CPU time (user): 22446.852
val precluster4_case1_experimental : bool = true
*)
(* BXZBPJW pseudo-area *)
let precluster4_case1_experimental() = 
  let cluster_areacut = two*aK - epsM_I in
  let pdata = reset_peri init2Cps_isosceles_BC_AC in
  let fillfn () = mk2Ce d_shared_pseudo in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18//10 or dBC >> 18//10 or disjoint_I dAC d_shared_pseudo) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  let cencut = (aK + epsN_I - epsM_I).high in 
  let ccs = [(coord2Ce,cencut);] in 
  let _ = report "precluster4_case1 isosceles Tin BC=AC experimental" in
  time_mitm cluster_areacut pdata cfn ccs;;

let init2Cps_precluster6 = (* T_S for precluster6 *)
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,ddAB,ddBC,(dAC,thACB,thCAB,arcB)) = 
    ((dAC << 18//10) && outdomfn (a,ddAB,ddBC,(dAC,thACB,thCAB,arcB))) or
      (a >> aK + epsM_I) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

(* done June 13, 2016
precluster6 case1 AB shared Tin, egress BC
i=0, w=0.50000, length(ccs)=7
 length(ps)=244 maxkey=18 keysum=2650 phash=24
i=1, w=0.25000, length(ccs)=28
 length(ps)=1314 maxkey=64 keysum=31051 phash=128
i=2, w=0.12500, length(ccs)=239
 length(ps)=7071 maxkey=80 keysum=136916 phash=409
i=3, w=0.06250, length(ccs)=2698
 length(ps)=31771 maxkey=100 keysum=734798 phash=1610
i=4, w=0.03125, length(ccs)=16650
 length(ps)=128432 maxkey=100 keysum=2681334 phash=4623
i=5, w=0.01562, length(ccs)=21352
 length(ps)=419912 maxkey=75 keysum=8457559 phash=9809
i=6, w=0.00781, length(ccs)=640
 length(ps)=379620 maxkey=60 keysum=7202886 phash=9174
CPU time (user): 2461.944
val precluster6_case1 : bool = true
*)
(* JQMRXTH pseudo-area3 *)
let precluster6_case1() = 
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAB in (* case *)
  let keyfnS = ckeyfnBC in (* case *)
  let cfn = 
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_shared_pseudo,d_egress,d_third_pseudo) in
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster6 case1 AB shared Tin, egress BC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 13, 2016
precluster6 case2 AB shared Tin, egress AC
i=0, w=0.50000, length(ccs)=7
 length(ps)=244 maxkey=18 keysum=2650 phash=24
i=1, w=0.25000, length(ccs)=28
 length(ps)=1314 maxkey=64 keysum=31051 phash=127
i=2, w=0.12500, length(ccs)=155
 length(ps)=7071 maxkey=80 keysum=136916 phash=380
i=3, w=0.06250, length(ccs)=1386
 length(ps)=31771 maxkey=100 keysum=734798 phash=1380
i=4, w=0.03125, length(ccs)=8327
 length(ps)=118667 maxkey=100 keysum=2476272 phash=3917
i=5, w=0.01562, length(ccs)=26215
 length(ps)=374015 maxkey=75 keysum=7403943 phash=7378
i=6, w=0.00781, length(ccs)=8039
 length(ps)=1017129 maxkey=60 keysum=20105264 phash=11018
CPU time (user): 5665.572
val precluster6_case2 : bool = true
*)
(* JQMRXTH pseudo-area3 *)
let precluster6_case2() = 
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAB in (* case *)
  let keyfnS = ckeyfnAC in (* case *)
  let cfn = 
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_shared_pseudo,d_third_pseudo,d_egress) in
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster6 case2 AB shared Tin, egress AC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 13, 2016
precluster6 case3 BC shared Tin, egress AB
i=0, w=0.50000, length(ccs)=9
 length(ps)=244 maxkey=18 keysum=2650 phash=24
i=1, w=0.25000, length(ccs)=36
 length(ps)=1314 maxkey=64 keysum=31051 phash=128
i=2, w=0.12500, length(ccs)=335
 length(ps)=7071 maxkey=80 keysum=136916 phash=417
i=3, w=0.06250, length(ccs)=3380
 length(ps)=31771 maxkey=100 keysum=734798 phash=1741
i=4, w=0.03125, length(ccs)=17734
 length(ps)=134072 maxkey=100 keysum=2788537 phash=4807
i=5, w=0.01562, length(ccs)=41632
 length(ps)=446935 maxkey=75 keysum=9008284 phash=10798
i=6, w=0.00781, length(ccs)=1117
 length(ps)=524489 maxkey=60 keysum=10001913 phash=11008
CPU time (user): 3206.716
val precluster6_case3 : bool = true
 *)
(* JQMRXTH pseudo-area3 *)
let precluster6_case3() = 
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnBC in (* case *)
  let keyfnS = ckeyfnAB in (* case *)
  let cfn = 
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_egress,d_shared_pseudo,d_third_pseudo) in 
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster6 case3 BC shared Tin, egress AB") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 13 
precluster6 case4: BC shared Tin, egress AC
i=0, w=0.50000, length(ccs)=7
 length(ps)=244 maxkey=18 keysum=2650 phash=24
i=1, w=0.25000, length(ccs)=27
 length(ps)=1314 maxkey=64 keysum=31051 phash=127
i=2, w=0.12500, length(ccs)=107
 length(ps)=7071 maxkey=80 keysum=136916 phash=383
i=3, w=0.06250, length(ccs)=826
 length(ps)=31771 maxkey=100 keysum=734798 phash=1456
i=4, w=0.03125, length(ccs)=2874
 length(ps)=123965 maxkey=100 keysum=2600210 phash=3898
i=5, w=0.01562, length(ccs)=2762
 length(ps)=325598 maxkey=75 keysum=6562016 phash=7031
i=6, w=0.00781, length(ccs)=682
 length(ps)=769424 maxkey=60 keysum=14816718 phash=10114
CPU time (user): 3061.752
val precluster6_case4 : bool = true
*)
(* JQMRXTH pseudo-area3 *)
let precluster6_case4() = 
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnBC in (* case *)
  let keyfnS = ckeyfnAC in (* case *)
  let cfn = 
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_third_pseudo,d_shared_pseudo,d_egress) in 
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster6 case4: BC shared Tin, egress AC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 13, 2016
precluster6 case5: AC shared Tin, egress AB
i=0, w=0.50000, length(ccs)=9
 length(ps)=244 maxkey=18 keysum=2650 phash=24
i=1, w=0.25000, length(ccs)=36
 length(ps)=1314 maxkey=64 keysum=31051 phash=128
i=2, w=0.12500, length(ccs)=326
 length(ps)=7071 maxkey=80 keysum=136916 phash=411
i=3, w=0.06250, length(ccs)=2798
 length(ps)=31771 maxkey=100 keysum=734798 phash=1672
i=4, w=0.03125, length(ccs)=12119
 length(ps)=134072 maxkey=100 keysum=2788537 phash=4481
i=5, w=0.01562, length(ccs)=23075
 length(ps)=439025 maxkey=75 keysum=8697877 phash=9282
i=6, w=0.00781, length(ccs)=3582
 length(ps)=1054823 maxkey=60 keysum=20897865 phash=13857
CPU time (user): 5322.54
val precluster6_case5 : bool = true
 *)
(* JQMRXTH pseudo-area3 *)
let precluster6_case5() = 
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAC in (* case *)
  let keyfnS = ckeyfnAB in (* case *)
  let cfn = 
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_egress,d_third_pseudo,d_shared_pseudo) in 
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster6 case5: AC shared Tin, egress AB") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 13, 2016
 precluster6 case6: AC shared Tin, egress BC
i=0, w=0.50000, length(ccs)=7
 length(ps)=244 maxkey=18 keysum=2650 phash=24
i=1, w=0.25000, length(ccs)=28
 length(ps)=1314 maxkey=64 keysum=31051 phash=128
i=2, w=0.12500, length(ccs)=150
 length(ps)=7071 maxkey=80 keysum=136916 phash=403
i=3, w=0.06250, length(ccs)=1183
 length(ps)=31771 maxkey=100 keysum=734798 phash=1532
i=4, w=0.03125, length(ccs)=3455
 length(ps)=121944 maxkey=100 keysum=2559754 phash=3994
i=5, w=0.01562, length(ccs)=4571
 length(ps)=258808 maxkey=75 keysum=5264459 phash=6592
i=6, w=0.00781, length(ccs)=6537
 length(ps)=521777 maxkey=60 keysum=10091869 phash=7954
i=7, w=0.00391, length(ccs)=751
 length(ps)=643076 maxkey=45 keysum=12248922 phash=10324
CPU time (user): 3654.536
val precluster6_case6 : bool = true
*)
(* JQMRXTH pseudo-area3 *)
let precluster6_case6() = 
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAC in (* case *)
  let keyfnS = ckeyfnBC in (* case *)
  let cfn = 
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_third_pseudo,d_egress,d_shared_pseudo) in 
  let cencut = (aK + epsN_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster6 case6: AC shared Tin, egress BC") in
  time_mitm cluster_areacut pdata cfn ccs;;

let mitm_time_seconds = 
[14870;73430;17214;7679;4953;
 2830;393;516;266;584;
 4609;168;809;7714;817;
 440;4955;14058;22446;2461;
 5665;3206;3061;5322;3624];;
(* about 202090 seconds or about 56 hours *)

(* end of file *)
