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

let hyp1_T0_disjoint_from_domain d_in d0 = 
  let (a_in,_,_,_) = d_in in
  let (a,(dAD,thADC,thDAC,arcC),(dDC,thCDA,thDCA,arcA),(dAC,thACD,thCAD,arcD)) = d0 in
  (a_in + a >> two*aK) or (max2_I dAD dDC << 18 // 10) or 
    (dAD << two*kappa) or (dDC << two*kappa) 
   (* XX need to add touching constraint on 2C case *);;

let hyp1 = 0;;
let recurse_hyp1 (f,dom) = recurs_xeps (one_Tin_T0 hyp1_drange_Tin hyp1_Tin_disjoint_from_domain 
		    f
		    hyp1_drange_T0 hyp1_T0_disjoint_from_domain) [(dom_Tin @ dom)];;

(* debug test *)
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




(* run hyp1 cases *)
time recurse_hyp1 (mkT0_sliderAD,dom_slider);;
recurse_hyp1 (mkT0_sliderDC,dom_slider);;
recurse_hyp1 (mkT0_midpointerAD,dom_midpointer);; (* completes in 8*10^6 steps *)
recurse_hyp1 (mkT0_midpointerDC,dom_midpointer);;
recurse_hyp1 (mkT0_generalAD,dom_general);;

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


