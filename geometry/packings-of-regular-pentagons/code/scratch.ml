(* prove the pre-cluster hypotheses *)

(* extend slider to the domain [0,4sigma], swapping sign above 2sigma *)
(* the extension is continuous across 2sigma *)

let ellthetax_slider xalpha = 
  let swap xa = 
    let (d,th,th') = ellthetax (four*sigma  - xa) zero in
    (d,th',th) in
  mergefn (fun xalpha -> ellthetax xalpha zero) swap
    (fun (x1,y1,z1) (x2,y2,z2) -> merge_I x1 x2,merge_I y1 y2, merge_I z1 z2) 
    (two*sigma)
    xalpha;;

let ellthetax_midpointer  = 
  ellthetax sigma ;;

(* notation for ps-dimers:
   AC is the shared  edge and B is the nonshared pentagon on T_in
   D is the nonshared edge on T0.
	  Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB))
*)

let mkT0_sliderAD dDCrange [xalphaAD] (dAC,thACD,thCAD) = 
  let (dAD,thADC,thDAC) = ellthetax_slider xalphaAD in
  match fillout2C dDCrange (dAD,thDAC,thADC) (dAC,thCAD,thACD) with
  | None -> None
  | Some (a,(dAD,thDAC,thADC,arcC),(dAC,thCAD,thACD,arcD),(dDC,thDCA,thCDA,arcA)) ->
    Some (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD));;


let mkT0_sliderDC dADrange [xalphaDC] (dAC,thACD,thCAD) =
  let (dDC,thCDA,thDCA) = ellthetax_slider xalphaDC in
  match fillout2C dADrange (dAC,thACD,thCAD) (dDC,thDCA,thCDA) with
  | None -> None
  | Some (a, (dAC,thACD,thCAD,arcD), (dDC,thDCA,thCDA,arcA), (dAD,thADC,thDAC,arcC)) ->
    Some (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD));;

let dom_slider = [zero2 (four*sigma)];;

let mkT0_midpointerAD dDCrange [alphaAD] (dAC,thACD,thCAD) = 
  let (dAD,thADC,thDAC) = ellthetax_midpointer alphaAD in
  match fillout2C dDCrange (dAD,thDAC,thADC) (dAC,thCAD,thACD) with
  | None -> None
  | Some (a,(dAD,thDAC,thADC,arcC),(dAC,thCAD,thACD,arcD),(dDC,thDCA,thCDA,arcA)) ->
    Some (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD));;

let mkT0_midpointerDC dADrange [alphaDC] (dAC,thACD,thCAD) =
  let (dDC,thCDA,thDCA) = ellthetax_midpointer alphaDC in
  match fillout2C dADrange (dAC,thACD,thCAD) (dDC,thDCA,thCDA) with
  | None -> None
  | Some (a, (dAC,thACD,thCAD,arcD), (dDC,thDCA,thCDA,arcA), (dAD,thADC,thDAC,arcC)) ->
    Some (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD));;

let dom_midpointer = [zero2 pi45];;

let mkT0_generalAD dDCrange [xalphaAD;alphaAD] (dAC,thACD,thCAD) = 
  let (dAD,thADC,thDAC) = ellthetax xalphaAD alphaAD in
  match fillout2C dDCrange (dAD,thDAC,thADC) (dAC,thCAD,thACD) with
  | None -> None
  | Some (a,(dAD,thDAC,thADC,arcC),(dAC,thCAD,thACD,arcD),(dDC,thDCA,thCDA,arcA)) ->
    Some (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD));;

let dom_general = [(zero2 (two*sigma));zero2 pi45];;

let mkTin_T0 = 0;;

let one_Tin_T0 
    drange_Tin
    disjoint_from_domain_Tin
    mkT0 drange_T0
    disjoint_from_domain_T0  xs = 
  try
    match xs with
    | xalphaAB :: alphaAB :: xalphaBC :: alphaBC :: xss ->
      let v_in = mk2Ce drange_Tin [xalphaAB;alphaAB;xalphaBC;alphaBC] in
      (match v_in with
      | None -> true
      | Some d_in ->  (disjoint_from_domain_Tin d_in) or 
	let _,_,_,(dAC,thACB,thCAB,_) = d_in in
	let v0 = mkT0 drange_T0 xss (dAC,-thACB,-thCAB) in
	(match v0 with
	| None -> true
	| Some d0 -> disjoint_from_domain_T0 d_in d0))
    | _ -> failwith "wrong number of args"
  with Unstable -> false;;

let dom_Tin = [(zero2 (two*sigma));(zero2 pi45);(zero2 (two*sigma));(zero2 pi45)];;  

ellthetax_slider (merge_I (two*sigma - m 0.1) (two*sigma + m 0.2));;

two*sigma;;

(* let's try hypothesis 1. *)

(* upper bound because otherwise not subcrtical *)
let hyp1_drange_Tin = merge_I (18 // 10) (21 // 10);;  

let hyp1_Tin_disjoint_from_domain d_in = 
  let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = d_in in
  (a >> aK) or (disjoint_I dAC hyp1_drange_Tin) or (dAB >> dAC) or (dBC >> dAC);;

let hyp1_drange_T0 = merge_I (two*kappa) (232 // 100);;



let hyp1_T0_disjoint_from_domain is_2C d_in d0 = 
  let (a_in,_,_,_) = d_in in
  let (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD)) = d0 in
  (a_in + a >> two*aK) or (max2_I dAD dDC << 18 // 10) or 
    (dAD << two*kappa) or (dDC << two*kappa) or (is_2C && not(pent_contact2 dAC thACD thCAD));;

let hyp1 = 0;;

let recurse_hyp1 (f,dom,is_2C) = 
  recurs_xeps 
    (one_Tin_T0 hyp1_drange_Tin hyp1_Tin_disjoint_from_domain 
		    f
		    hyp1_drange_T0 (hyp1_T0_disjoint_from_domain is_2C)) [(dom_Tin @ dom)];;

(* test 
let xx = two*sigma - zero2 (m 0.1);;
let xx2 = pi25 + mk (- 0.1) (0.1);;
let xx2 = pi45 - zero2 (m 0.1);;
let yy = zero2 (four * sigma);;
Random.init 0;;
let random x w = 
  let z = inter_I x (min_I x + m(Random.float (width_I x).high) + zero2 (m w)) in
  z;;
let qq = 
  let w = 0.4 in
  let x1 = random (zero2 (two*sigma)) w in
  let y1 = random (zero2 pi45) w in
  let x2 = random (zero2 (two*sigma)) w in
  let y2 = random (zero2 pi45) w in
  let zz = random (zero2 (four*sigma)) w in
  (w,x1,y1,x2,y2,zz,
  time (recurs_xeps (one_Tin_T0 hyp1_drange_Tin hyp1_Tin_disjoint_from_domain 
		    mkT0_sliderAD
		    hyp1_drange_T0 hyp1_T0_disjoint_from_domain)) [[x1;y1;x2;y2;zz]]);;
qq1 (* 74 secs *)
let qq2 = qq;;
dom_Tin;;

theta'_banana;;
*)

(* run hyp1 cases *)

(* commented out to make reload easier ...
time recurse_hyp1 (mkT0_sliderAD,dom_slider,false);; (* CPU time (user): 14541.908 : int * bool = (24811279, true) *)
recurse_hyp1 (mkT0_sliderDC,dom_slider,false);;  (* exclude by symmetry *)
recurse_hyp1 (mkT0_midpointerAD,dom_midpointer,false);; (* completes in 8*10^6 steps *)
recurse_hyp1 (mkT0_midpointerDC,dom_midpointer,false);; (* done by symmetry *)
recurse_hyp1 (mkT0_generalAD,dom_general,true);;  (* running, interrupted,
  ran all night, making gradual progress,
  reached count=128400000, length=9, vol=19.3444, starting with vol=25.3297.
  So it might terminate after a few days.  *)
*)

(* let's try hypothesis 2. *)

let hyp2_drange_Tin = merge_I (172 // 100) (18 // 10);;  

let hyp2_Tin_disjoint_from_domain d_in = 
  let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = d_in in
  (a >> aK) or (disjoint_I dAC hyp2_drange_Tin) or (dAB >> dAC) or (dBC >> dAC);;

let hyp2_drange_T0 = merge_I (172 // 100) (18 // 10);;

let hyp2_T0_disjoint_from_domain d_in d0 = 
  let (a_in,_,_,_) = d_in in
  let (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD)) = d0 in
  (a_in + a >> two*aK) or 
    (disjoint_I dAD hyp2_drange_T0) or 
    (disjoint_I dDC hyp2_drange_T0) or
    max2_I dAD dDC << dAC;;

let recurse_hyp2 (f,dom) = recurs_xeps (one_Tin_T0 hyp2_drange_Tin hyp2_Tin_disjoint_from_domain 
		    f
		    hyp2_drange_Tin hyp2_T0_disjoint_from_domain) [(dom_Tin @ dom)];;

(* commented out to speed up reload 
time recurse_hyp2 (mkT0_sliderAD,dom_slider);; (* CPU time (user): 1730.108
- : int * bool = (2967249, true)  *)
recurse_hyp2 (mkT0_sliderDC,dom_slider);;  (* exclude by symmetry *)
time recurse_hyp2 (mkT0_midpointerAD,dom_midpointer);;  (* CPU time (user): 5809.192
- : int * bool = (9918329, true) *)
recurse_hyp2 (mkT0_midpointerDC,dom_midpointer);;  (* exclude by symmetry *)
recurse_hyp2 (mkT0_generalAD,dom_general);;   (* not done yet *)
*)

(* Old hyp 3 *)
area_I (m 1.8) (m 1.72) (m 1.77) - (aK + epso_I);;

(* Now hypothesis 4. XX not done yet. *)

let hyp4_drange_Tin = merge_I (172 // 100) (18 // 10);;  

let hyp4_Tin_disjoint_from_domain d_in = 
  let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = d_in in
  (a >> aK) or (disjoint_I dAC hyp4_drange_Tin) or (dAB >> dAC) or (dBC >> dAC);;


(* let hyp4_drange_T0 = merge_I (18 // 100) (195 // 100);; *)


let hyp4_T0_disjoint_from_domain d_in d0 = 
  let (a_in,_,_,_) = d_in in
  let (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD)) = d0 in
  (a_in + a >> two*aK) or 
    (disjoint_I dAD hyp4_drange_T0) or 
    (disjoint_I dDC hyp4_drange_T0) or
    max2_I dAD dDC << dAC;;

let recurse_hyp4 (f,dom) = recurs_xeps (one_Tin_T0 hyp4_drange_Tin hyp4_Tin_disjoint_from_domain 
		    f
		    hyp4_drange_Tin hyp4_T0_disjoint_from_domain) [(dom_Tin @ dom)];;

(* hyp4 only has the generic case *)
recurse_hyp4 (mkT0_generalAD,dom_general);; (* not done *)


(* June 13, 2016 addition 
Test deformability and badness of 2C isosceles triangles.


*)

(* repeat from mitm-calcs.ml *)
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

let coord2Ce = 
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in (* extended coords *)
    [xalpha;alpha;xalpha;alpha];;

(* end repeat *)

recursetoeps;;


let outofdomain_2Cisos_ZE = 
  let _ = area_I (178//100) (178//100) (two*kappa) >> (aK - epso''_I) or
    failwith "178" in
  fun xs ->
    try 
      let range = merge_I (172//100) (178//100) in 
      match mk2Ce range xs with
      | None -> true
      | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	      (dAC,thACB,thCAB,arcB)) ->
	a >> aK - epso''_I or
	  disjoint_I dAC range or
	  disjoint_I dAC dBC or
	  forall_alpha (fun th -> th << zero) thCBA or
	  forall_alpha_pair 
	  (fun (thCBA,thBCA) -> abs_I thCBA >> abs_I thBCA) (thCBA,thBCA)
    with Unstable -> false ;;

(* - : int * bool = (265215, true) *)
recursetoeps outofdomain_2Cisos_ZE [coord2Ce];;

let outofdomain_2Cisos_ZF = 
  let _ = area_I (179//100) (179//100) (two*kappa) >> (aK) or
    failwith "179" in
  fun xs ->
    try 
      let range = merge_I (172//100) (177//100) in 
      match mk2Ce range xs with
      | None -> true
      | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	      (dAC,thACB,thCAB,arcB)) ->
	a >> aK  or
	  disjoint_I dAC range or
	  disjoint_I dAC dBC or
	  forall_alpha (fun th -> th << zero) thCBA or
	  forall_alpha_pair 
	  (fun (thCBA,thBCA) -> abs_I thCBA >> abs_I thBCA) (thCBA,thBCA)
    with Unstable -> false ;;

(* - : int * bool = (329467, true) *)
let _ = report "single triangle, isosceles 2C, edge length" in
recursetoeps outofdomain_2Cisos_ZF [coord2Ce];;

area_I (177//100) (177//100) (168//100) - (aK + two*epso''_I);;

      
