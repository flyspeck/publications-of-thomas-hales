(* run the various hypothesis verifications *)

open Meet;;

let init2Cps = (* standard 2C settings for peripheral triangles *)
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
  (fn,[(pcoord,keys,area)]);;
  
  
(* June 7, 2016: completed running : *)
(* Needs about 1GB of memory. A few hours to run on my laptop. *)
let calc_pent4_postcluster() = 
  let i = 0 in
  let cluster_areacut = four*aK in
  let width = (1//2) in
  (* init peripheral *)
  let ps = init2Cps in
  let _ = Hashtbl.reset phash in
  let pdata = Some(phash,ps) in
  (* init central *)
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn _ = false in 
  let areafn (a,_) = a in
  let keyfnAB w fs = key_inverts w (edge5D_ABs fs) in
  let keyfnBC w fs = key_inverts w (edge5D_BCs fs) in
  let keyfnAC w fs = key_inverts w (edge5D_ACs fs) in
  let keyfns = [keyfnAB;keyfnBC;keyfnAC] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  (* init central ccs *)
  let z2 = zero2 pi25 in
  let k2 = merge_I (172//100) (21//10) in
  let k2' = merge_I (172//100) two in
  let ccoord = [k2;z2;z2;k2;k2'] in
  let cencut = (aK + int 3*epso_I).high in
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  let _ = report "pack4" in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;
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
i=1, w=0.25000, length(ccs)=144
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=1311
 length(ps)=5923 maxkey=80 keysum=116268 phash=408
i=3, w=0.06250, length(ccs)=11907
 length(ps)=24180 maxkey=100 keysum=546726 phash=1739
i=4, w=0.03125, length(ccs)=45939
 length(ps)=103932 maxkey=75 keysum=2167549 phash=4619
i=5, w=0.01562, length(ccs)=39876
 length(ps)=555691 maxkey=75 keysum=11051338 phash=10346
i=6, w=0.00781, length(ccs)=2910
 length(ps)=1205028 maxkey=60 keysum=23335499 phash=13736
CPU time (user): 6333.316
val calc_pent3AB : bool = true
*)
let calc_pent3AB_postcluster() = (* done *)
  let i = 0 in
  let cluster_areacut = int 3*aK in
  let width = (1//2) in
  (* init peripheral *)
  let ps = init2Cps in
  let _ = Hashtbl.reset phash in
  let pdata = Some(phash,ps) in
  (* init central *)
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn _ = false in 
  let areafn (a,_) = a in
(*  let keyfnAB w fs = key_inverts w (edge5D_ABs fs) in *)
  let keyfnBC w fs = key_inverts w (edge5D_BCs fs) in 
  let keyfnAC w fs = key_inverts w (edge5D_ACs fs) in
  let keyfns = [(* keyfnAB;*) keyfnBC; keyfnAC] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  (* init central ccs *)
  let z2 = zero2 pi25 in
  let k2 = merge_I (172//100) (21//10) in
  let k2' = merge_I (172//100) two in
  let ccoord = [k2;z2;z2;k2;k2'] in
  let cencut = (aK + int 2*epso_I).high in
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  let _ = report("pent3AB") in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;

(* done, June 7, 2016 restarted ocaml to clear memory 
pent3BC
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=144
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=1311
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=11698
 length(ps)=24180 maxkey=100 keysum=546726 phash=1736
i=4, w=0.03125, length(ccs)=48180
 length(ps)=104176 maxkey=75 keysum=2172298 phash=4489
i=5, w=0.01562, length(ccs)=14393
 length(ps)=428881 maxkey=75 keysum=8449981 phash=8846
CPU time (user): 2728.724
val calc_pent3BC : bool = true *)
let calc_pent3BC_postcluster() = 
  let i = 0 in
  let cluster_areacut = int 3*aK in
  let width = (1//2) in
  (* init peripheral *)
  let ps = init2Cps in
  let _ = Hashtbl.reset phash in
  let pdata = Some(phash,ps) in
  (* init central *)
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn _ = false in 
  let areafn (a,_) = a in
  let keyfnAB w fs = key_inverts w (edge5D_ABs fs) in
(*  let keyfnBC w fs = key_inverts w (edge5D_BCs fs) in *)
  let keyfnAC w fs = key_inverts w (edge5D_ACs fs) in
  let keyfns = [keyfnAB;(* keyfnBC; *)keyfnAC] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  (* init central ccs *)
  let z2 = zero2 pi25 in
  let k2 = merge_I (172//100) (21//10) in
  let k2' = merge_I (172//100) two in
  let ccoord = [k2;z2;z2;k2;k2'] in
  let cencut = (aK + int 2*epso_I).high in
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  let _ = report("pent3BC") in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;

(* done June 7, 2016 
pent3AC
i=0, w=0.50000, length(ccs)=9
 length(ps)=210 maxkey=18 keysum=2290 phash=24
i=1, w=0.25000, length(ccs)=144
 length(ps)=1145 maxkey=64 keysum=28215 phash=128
i=2, w=0.12500, length(ccs)=1311
 length(ps)=5923 maxkey=80 keysum=116268 phash=409
i=3, w=0.06250, length(ccs)=11936
 length(ps)=24180 maxkey=100 keysum=546726 phash=1792
i=4, w=0.03125, length(ccs)=56587
 length(ps)=104176 maxkey=75 keysum=2172298 phash=4781
i=5, w=0.01562, length(ccs)=9977
 length(ps)=439424 maxkey=75 keysum=8870936 phash=8702
CPU time (user): 2156.648
val calc_pent3AC : bool = true
  *)
let calc_pent3AC_postcluster() = 
  let i = 0 in
  let cluster_areacut = int 3*aK in
  let width = (1//2) in
  (* init peripheral *)
  let ps = init2Cps in
  let _ = Hashtbl.reset phash in
  let pdata = Some(phash,ps) in
  (* init central *)
  let extra = () in
  let fillfn _ [dAB;thABC;thBAC;dBC;dAC] = fillout5D ((dAB,thABC,thBAC),dBC,dAC) in
  let outdomfn _ = false in 
  let areafn (a,_) = a in
  let keyfnAB w fs = key_inverts w (edge5D_ABs fs) in 
  let keyfnBC w fs = key_inverts w (edge5D_BCs fs) in 
(*  let keyfnAC w fs = key_inverts w (edge5D_ACs fs) in *)
  let keyfns = [keyfnAB; keyfnBC; (*keyfnAC*)] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  (* init central ccs *)
  let z2 = zero2 pi25 in
  let k2 = merge_I (172//100) (21//10) in
  let k2' = merge_I (172//100) two in
  let ccoord = [k2;z2;z2;k2;k2'] in
  let cencut = (aK + int 2*epso_I).high in
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  let _ = report("pent3AC") in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;

(* in case pent2_postcluster the cluster is not a pseudo-dimer
   but shares the egressive edge with a pseudo-dimer.
   The angle condition on the egress edge is antisymmetric.
   Thus, the pent2 cluster is enirely outof domain if it is fully in
   the pseudo-dimer domain *)

let forall_alpha_constraint_pseudo_dimer (th,th') = 
  let alpha = th + th' in
  let alpha' = Pet.periodize_pent0 alpha in
  forall (fun a -> a >> pi15) alpha';;
  
let calc_pent2_postcluster_case0 = (* running June 8 2016 *)
  let i = 0 in
  let cluster_areacut = two*aK + epso'_I in
  let width = (1//2) in
  (* init peripheral *)
  let ps = init2Cps in
  let _ = Hashtbl.reset phash in
  let pdata = Some(phash,ps) in
  (* init central *)
  let extra = () in
  let range = merge_I (172 // 100) (192//100) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18 // 10 or dBC >> 179 // 100 or disjoint_I dAC range or
       forall_alpha_constraint_pseudo_dimer (thABC,thBAC)) in
    (* note AB is the egressive edge, AC is the shared edge *)
  let areafn (a,_,_,_) = a in
  let keyfn w (_,_,_,(dAC,thACB,thCAB,_)) = key_invert w (dAC,thACB,thCAB) in
  let keyfns = [keyfn] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in (* extended coords *)
  let ccoord = 
    [xalpha;alpha;xalpha;alpha] in
  (* init central ccs *)
  let cencut = (aK + epso_I + epso'_I).high in 
  let assertAC = area_I (192//100) (18//10) (two*kappa) >>. cencut or 
    failwith "please reset 1.92 bound and rerun" in
  let assertBC = area_I (18//10) (172//100) (179//100) >>. cencut or
    failwith "please reset 1.79 bound and rerun" in
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  let _ = report "pent2_case0 covers 2C+2C situation" in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;


(* June 7, 2016. Goes out to i=6, then come close
   to exhausting memory. Process killed.  *)
(* partial data:
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
  C-c C-cFailed after (user) CPU time of 11434.192: Interrupted.
*)

let hyp4_precluster = 
  let i = 0 in
  let cluster_areacut = two*aK - epso'_I in
  let width = (1//2) in
  (* init peripheral *)
  let ps = init2Cps in
  let _ = Hashtbl.reset phash in
  let pdata = Some(phash,ps) in
  (* init central *)
  let extra = () in
  let range = merge_I (172 // 100) (18//10) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = 
    (dAB << 18 // 10 or dBC >> 18 // 10 or disjoint_I dAC range) in
  let areafn (a,_,_,_) = a in
  let keyfn w (_,_,_,(dAC,thACB,thCAB,_)) = key_invert w (dAC,thACB,thCAB) in
  let keyfns = [keyfn] in
  let cfn = (extra,fillfn,outdomfn,areafn,keyfns) in
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in (* extended coords *)
  let ccoord = 
    [xalpha;alpha;xalpha;alpha] in
  (* init central ccs *)
  let cencut = (aK + epso_I - epso'_I).high in 
  let ccs = [(ccoord,cencut);] in 
  let initialized = false in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;

Hashtbl.reset phash;;
Gc.full_major();;

Obj.size(Obj.repr (Some (pi45,pi15,zero,one,pi),Some 3,Some 1.0));;
pi45;;
1_345;;
1345n;;
(Obj.magic(Obj.field (Obj.repr pi45) 1):int);;
(Obj.magic(Obj.field (Obj.repr pi45.low) 3):int);;
aK + four*epso_I;;
float_of_int(1 lsl 30) /. (1.0e9);;
aK - epso_I;;
