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
   *)

open Meet;;

let time_mitm cluster_areacut pdata cfn ccs =
  let i = 0 in
  let width = 1//2 in
  let initialized = false in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;

let unit_extra = ();;

let coord5 (dAB,dBC,dAC) = 
  let z2pi25 = zero2 pi25 in
  [dAB;z2pi25;z2pi25;dBC;dAC];;

let coord2Ce = 
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in (* extended coords *)
    [xalpha;alpha;xalpha;alpha];;

let fillfn5 _ [dAB;thABC;thBAC;dBC;dAC] = 
  fillout5D ((dAB,thABC,thBAC),dBC,dAC);;

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
    forall f (outerpair s s');;


(* in case pent2_postcluster the cluster is not a pseudo-dimer
   but shares the egressive edge with a pseudo-dimer.
   The angle condition on the egress edge is antisymmetric.
   Thus, the pent2 cluster is enirely outof domain if it is fully in
   the pseudo-dimer domain *)

let forall_alpha_constraint_pseudo_dimer (th,th') = 
  forall_alpha0 (fun a -> a >>pi15) (th+th');;

(* dead code.
  let alpha = th + th' in
  let alpha' = Pet.periodize_pent0 alpha in
  forall (fun a -> a >> pi15) alpha';;
*)

let d_subcrit_shared = 
  let _ = area_I (two*kappa) (two*kappa) (21//10) >> aK or failwith "21" in
  merge_I (172//100) (21//10);;

let d_subcrit_contact = 
  merge_I (172//100) two;;

let d_shared_dimer = merge_I (172//100) (18//10);;

let ckeyfnBC w fs = key_inverts w (edge5D_BCs fs);;
let ckeyfnAC w fs = key_inverts w (edge5D_ACs fs);;
let ckeyfnAB w fs = key_inverts w (edge5D_ABs fs);;
let ckeyfn2Ce w (_,_,_,(dAC,thACB,thCAB,_)) = 
  key_invert w (dAC,thACB,thCAB);;

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

let reset_peri ps = 
  let _ = Hashtbl.reset phash in
  Some(phash,ps);;

let mk_peri = 0;;
    
(* June 7, 2016: completed running : *)
(* Needs about 1GB of memory. A few hours to run on my laptop. *)
let calc_pent4_postcluster() = 
  let cluster_areacut = four*aK in
  let pdata = reset_peri init2Cps in 
  (* init central *)
  let outdomfn _ = false in 
  let keyfns = [ckeyfnAB;ckeyfnBC;ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let dAB_dBC_dAC = (d_subcrit_shared,d_subcrit_shared,d_subcrit_contact) in
  let cencut = (aK + int 3*epso_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report "pent4_postcluster" in
  time_mitm cluster_areacut pdata cfn ccs;;

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

(* up to i=3 the peripheral numbers are the same as in pent4.
   This suggests that no case-dependent filtering happens *)
(*
pent3AB
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=166
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=1751
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=13628
 length(ps)=24180 maxkey=100 keysum=546726 phash=1789
i=4, w=0.03125, length(ccs)=46829
 length(ps)=104154 maxkey=75 keysum=2171842 phash=4703
i=5, w=0.01562, length(ccs)=47768
 length(ps)=567307 maxkey=75 keysum=11271902 phash=10771
i=6, w=0.00781, length(ccs)=15484
 length(ps)=1347131 maxkey=60 keysum=26105694 phash=15760
i=7, w=0.00391, length(ccs)=48
 length(ps)=425746 maxkey=45 keysum=8053812 phash=9154
CPU time (user): 9183.764
val calc_pent3AB_postcluster : bool = true
*)
let calc_pent3AB_postcluster() =
  let cluster_areacut = int 3*aK in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let outdomfn _ = false in 
  let keyfns = [ckeyfnBC; ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_short = merge_I (two*kappa) (21//10) in
  (* AB is not shared with a subcritical. It can be short. *)
  let dAB_dBC_dAC = (d_short,d_subcrit_shared,d_subcrit_contact) in
  let cencut = (aK + int 2*epso_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent3AB") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* done, June 8, 2016 restarted ocaml to clear memory 
pent3BC
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=168
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=2170
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=18109
 length(ps)=24180 maxkey=100 keysum=546726 phash=1793
i=4, w=0.03125, length(ccs)=68760
 length(ps)=104229 maxkey=75 keysum=2173302 phash=4572
i=5, w=0.01562, length(ccs)=51299
 length(ps)=451150 maxkey=75 keysum=8895515 phash=9427
i=6, w=0.00781, length(ccs)=5563
 length(ps)=796653 maxkey=60 keysum=15629999 phash=11215
CPU time (user): 5576.392
val calc_pent3BC_postcluster : bool = true
*)
let calc_pent3BC_postcluster() = 
  let cluster_areacut = int 3*aK in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let outdomfn _ = false in 
  let keyfns = [ckeyfnAB;ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_short = merge_I (two*kappa) (21//10) in
  (* BC not shared with a subcritical, can be short. *)
  let dAB_dBC_dAC=(d_subcrit_shared,d_short,d_subcrit_contact) in
  let cencut = (aK + int 2*epso_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent3BC") in
  time_mitm cluster_areacut pdata cfn ccs;;


(* done June 9, 2016 
pent3AC
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=144
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=2282
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=25118
 length(ps)=24180 maxkey=100 keysum=546726 phash=1837
i=4, w=0.03125, length(ccs)=99087
 length(ps)=104229 maxkey=75 keysum=2173302 phash=4856
i=5, w=0.01562, length(ccs)=53598
 length(ps)=464768 maxkey=75 keysum=9342866 phash=9320
i=6, w=0.00781, length(ccs)=6670
 length(ps)=255324 maxkey=60 keysum=4840764 phash=7661
CPU time (user): 3701.076
val calc_pent3AC_postcluster : bool = true
  *)
let calc_pent3AC_postcluster() = 
  let cluster_areacut = int 3*aK in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let outdomfn _ = false in 
  let keyfns = [ckeyfnAB; ckeyfnBC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_short = merge_I (two*kappa) two in
  (* AC not shared with a subcritical. It can be short. *)
  let dAB_dBC_dAC=(d_subcrit_shared,d_subcrit_shared,d_short) in
  let cencut = (aK + int 2*epso_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent3AC") in
  time_mitm cluster_areacut pdata cfn ccs;;



(*
pent2_case0 covers 2C+2C situation
i=0, w=0.50000, length(ccs)=201
 length(ps)=210 maxkey=18 keysum=2290 phash=32
i=1, w=0.25000, length(ccs)=673
 length(ps)=1145 maxkey=64 keysum=28215 phash=160
i=2, w=0.12500, length(ccs)=2932
 length(ps)=5923 maxkey=80 keysum=116268 phash=490
i=3, w=0.06250, length(ccs)=14729
 length(ps)=24180 maxkey=100 keysum=546726 phash=2014
i=4, w=0.03125, length(ccs)=57444
 length(ps)=102762 maxkey=75 keysum=2145040 phash=4859
i=5, w=0.01562, length(ccs)=54214
 length(ps)=372398 maxkey=75 keysum=7473699 phash=8591
i=6, w=0.00781, length(ccs)=1078
 length(ps)=263475 maxkey=48 keysum=5119546 phash=7036
CPU time (user): 2657.424
val calc_pent2_postcluster_case0 : bool = true
*)
let calc_pent2_postcluster_case0() = (* done June 8 2016 *)
  let cluster_areacut = two*aK + epso'_I in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let range = merge_I (172//100) (192//100) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18//10 or dBC >> 179//100 or disjoint_I dAC range or
       forall_alpha_constraint_pseudo_dimer (thABC,thBAC)) in
    (* note AB is the egressive edge, AC is the shared edge *)
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  (* init central ccs *)
  let cencut = (aK + epso_I + epso'_I).high in 
  let assertAC = area_I (192//100) (18//10) (two*kappa) >>. cencut or 
    failwith "please reset 1.92 bound and rerun" in
  let assertBC = area_I (18//10) (172//100) (179//100) >>. cencut or
    failwith "please reset 1.79 bound and rerun" in
  let ccs = [(coord2Ce,cencut);] in 
  let _ = report "pent2_case0 covers 2C+2C situation" in
  time_mitm cluster_areacut pdata cfn ccs;;


(* June 8, 2016. done:
pent2_postcluster_case1:AB shared, AC egressive. 
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=60
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=247
 length(ps)=5923 maxkey=80 keysum=116268 phash=397
i=3, w=0.06250, length(ccs)=738
 length(ps)=24060 maxkey=100 keysum=544590 phash=1373
i=4, w=0.03125, length(ccs)=1892
 length(ps)=64905 maxkey=75 keysum=1378153 phash=2795
i=5, w=0.01562, length(ccs)=521
 length(ps)=60505 maxkey=60 keysum=1220138 phash=3021
i=6, w=0.00781, length(ccs)=43
 length(ps)=42695 maxkey=48 keysum=816152 phash=1353
CPU time (user): 425.74
val calc_pent2_postcluster_case1 : bool = true *)
let calc_pent2_postcluster_case1() = 
  let cluster_areacut = two*aK + epso'_I in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 172//100 or 
       disjoint_I dBC (merge_I (two*kappa) (21//10)) or
       forall_alpha_constraint_pseudo_dimer (thACB,thCAB)) in
    (* note AB is shared, AC is egressive *)
  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_18 = (18//10) in
  let d_short = merge_I (two*kappa) (21//10) in
  let dAB_dBC_dAC=(d_subcrit_shared,d_short,d_18) in
  let cencut = (aK + epso_I + epso'_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent2_postcluster_case1:AB shared, AC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 8, 2016 done:
pent2_postcluster_case2:AB shared, BC egressive. 
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=72
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=333
 length(ps)=5923 maxkey=80 keysum=116268 phash=406
i=3, w=0.06250, length(ccs)=1320
 length(ps)=24086 maxkey=100 keysum=545010 phash=1491
i=4, w=0.03125, length(ccs)=2833
 length(ps)=70442 maxkey=75 keysum=1502796 phash=3254
i=5, w=0.01562, length(ccs)=2195
 length(ps)=61152 maxkey=75 keysum=1219198 phash=3709
i=6, w=0.00781, length(ccs)=461
 length(ps)=31550 maxkey=60 keysum=612688 phash=2484
i=7, w=0.00391, length(ccs)=6
 length(ps)=4551 maxkey=45 keysum=87700 phash=738
CPU time (user): 492.764
val calc_pent2_postcluster_case2 : bool = true
  *)
let calc_pent2_postcluster_case2() = 
  let cluster_areacut = two*aK + epso'_I in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
    forall_alpha_constraint_pseudo_dimer (thBCA,thCBA) in (* case *)
    (* note AB is shared, BC is egressive *)
  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_18 = (18//10) in
  let d_short = merge_I (two*kappa) (21//10) in
  let d_contact = merge_I (two*kappa) two in
  let dAB_dBC_dAC=(d_subcrit_shared,d_18,d_contact) in (* case *)
  let cencut = (aK + epso_I + epso'_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent2_postcluster_case2:AB shared, BC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* June 8, done 
pent2_postcluster_case3:BC shared, AC egressive. 
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=56
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=155
 length(ps)=5923 maxkey=80 keysum=116268 phash=375
i=3, w=0.06250, length(ccs)=480
 length(ps)=21847 maxkey=100 keysum=501983 phash=1316
i=4, w=0.03125, length(ccs)=852
 length(ps)=54718 maxkey=75 keysum=1180580 phash=2675
i=5, w=0.01562, length(ccs)=112
 length(ps)=52448 maxkey=60 keysum=1031616 phash=2543
i=6, w=0.00781, length(ccs)=16
 length(ps)=2870 maxkey=45 keysum=55307 phash=557
CPU time (user): 295.116
val calc_pent2_postcluster_case3 : bool = true
*)
let calc_pent2_postcluster_case3() = 
  let cluster_areacut = two*aK + epso'_I in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
    forall_alpha_constraint_pseudo_dimer (thACB,thCAB) in (* case *)
  let keyfns = [ckeyfnBC] in (* case *)
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_18 = (18//10) in
  let d_short = merge_I (two*kappa) (21//10) in
  let d_contact = merge_I (two*kappa) two in
  let dAB_dBC_dAC = (d_short,d_subcrit_shared,d_18) in (*case*)
  let cencut = (aK + epso_I + epso'_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("pent2_postcluster_case3:BC shared, AC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* done June 8, 2016:
pent2_postcluster_case4:BC shared, AB egressive. 
i=0, w=0.50000, length(ccs)=7
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=56
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=227
 length(ps)=5923 maxkey=80 keysum=116268 phash=393
i=3, w=0.06250, length(ccs)=1220
 length(ps)=23887 maxkey=100 keysum=541495 phash=1464
i=4, w=0.03125, length(ccs)=3398
 length(ps)=59859 maxkey=75 keysum=1264131 phash=3214
i=5, w=0.01562, length(ccs)=3192
 length(ps)=86227 maxkey=75 keysum=1752765 phash=4065
i=6, w=0.00781, length(ccs)=759
 length(ps)=48511 maxkey=60 keysum=940549 phash=3108
i=7, w=0.00391, length(ccs)=17
 length(ps)=11138 maxkey=45 keysum=215872 phash=1033
CPU time (user): 547.272
val calc_pent2_postcluster_case4 : bool = true
*)
let calc_pent2_postcluster_case4() = 
  let cluster_areacut = two*aK + epso'_I in
  let pdata = reset_peri init2Cps in
  (* init central *)
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = 
    forall_alpha_constraint_pseudo_dimer (thABC,thBAC) in (* case *)
  let keyfns = [ckeyfnBC] in (* case *)
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let d_18 = (18//10) in
  let d_short = merge_I (two*kappa) (21//10) in
  let d_contact = merge_I (two*kappa) two in
  let dAB_dBC_dAC = (d_18,d_subcrit_shared,d_contact) in (* case *)
  let cencut = (aK + epso_I + epso'_I).high in 
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
  let cencut = (aK + epso_I).high in 
  let ccs = [(coord2Ce,cencut);] in 
  let _ = area_I (18//10) (192//100) (two*kappa) >> aK+epso_I or 
    failwith "range_check" in
  let _ = area_I (18//10) (18//10) (17//10) >> aK+epso_I or
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
  let cencut = (aK + epso_I).high in 
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
  let cencut = (aK + epso_I).high in 
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
let precluster2_case0() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central, 2C+2C, AB is longest edge on T0 *)
  let fillfn () = mk2Ce d_shared_dimer in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		(dAC,thACB,thCAB,arcB)) = 
    (disjoint_I dAC d_shared_dimer or disjoint_I dAB d_shared_dimer or 
       disjoint_I dBC (merge_I (two*kappa) (18//10)) or
    dAB << dAC or dAB << dBC) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  (* init central ccs *)
  let cencut = (aK + epso_I).high in 
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
let precluster2_case1() = 
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in
  (* init central, midpointer A->C, isosceles, AB shared. *)
  (* midpointer edge AC gives triangle 1,kappa,1.8 *)
  let d_fullrange = merge_I (two*kappa) (18//10) in
  let out_of_midpointer dAC thACB =
    forall_alpha (fun t -> disjoint_I kappa (iloc one dAC (abs_I t))) thACB in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = out_of_midpointer dAC thACB 
    or (disjoint_I dAB dAC && disjoint_I dBC dAC) 
    or (disjoint_I dAB d_shared_dimer) 
    or (disjoint_I dAC d_fullrange)
    or (disjoint_I dBC d_fullrange) in
  let keyfns = [ckeyfnAB] in (* case AB *)
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  (* init central ccs *)
  let dAB_dBC_dAC = (d_shared_dimer,d_fullrange,d_fullrange) in
  let cencut = (aK + epso_I).high in 
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
  let d_full = merge_I (two*kappa) (18//10) in
  let dAB_dBC_dAC = (d_shared_dimer,d_full,d_full) in
  let cencut = (aK + epso_I).high in 
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
  let cencut = (aK + epso_I).high in 
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
let precluster4_case0_experimental() = 
  let epso'_I = epso''_I in (* experimental *)
  let cluster_areacut = two*aK - epso'_I in
  let pdata = reset_peri init2Cps_isosceles_AB_AC in
  (* init central *)
  let fillfn () = mk2Ce d_shared_dimer in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18//10 or dBC >> 18//10 or disjoint_I dAC d_shared_dimer) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  (* init central ccs *)
  let cencut = (aK + epso_I - epso'_I).high in 
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
let precluster4_case1_experimental() = 
  let epso'_I = epso''_I in (* experimental *)
  let cluster_areacut = two*aK - epso'_I in
  let pdata = reset_peri init2Cps_isosceles_BC_AC in
  (* init central *)
  let fillfn () = mk2Ce d_shared_dimer in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18//10 or dBC >> 18//10 or disjoint_I dAC d_shared_dimer) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  (* init central ccs *)
  let cencut = (aK + epso_I - epso'_I).high in 
  let ccs = [(coord2Ce,cencut);] in 
  let _ = report "precluster4_case1 isosceles Tin BC=AC experimental" in
  time_mitm cluster_areacut pdata cfn ccs;;

let init2Cps_precluster6 = (* T_S for precluster6 *)
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,ddAB,ddBC,(dAC,thACB,thCAB,arcB)) = 
    ((dAC << 18//10) && outdomfn (a,ddAB,ddBC,(dAC,thACB,thCAB,arcB))) or
      (a >> aK + epso''_I) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

let precluster6_case1() = 
  let _ = failwith "in prep" in
  let cluster_areacut = (int 3)*aK + epso''_I in
  let pdata = reset_peri init2Cps_precluster6 in
  (* init central *)
  let outdomfn _ = false in
  let keyfnT = ckeyfnAB in (* case *)
  let keyfnS = ckeyfnBC in (* case *)
  let cfn = 
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  (* init central ccs *)
  let d_S = merge_I (18//10) (21//10) in
  let d_AC = merge_I (two*kappa) two in
  let d_third = merge_I (two*kappa) (18//10) in
  let dAB_dBC_dAC = (d_shared_dimer,d_S,d_third) in
  let cencut = (aK + epso_I).high in 
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in 
  let _ = report("precluster6 case1 AB shared Tin, S shared BC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* end of file *)
