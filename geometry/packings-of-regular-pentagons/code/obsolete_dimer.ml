(*
Note: June 2016.
This is all old stuff.
I think that it can be deleted as soon as the BMIEZDS "squeez" lemma
is redone.
*)

(* continuation of pent.hl
   Dimer calculations *)



(* ******************************************************************************** *)
(* BMIEZDS test that comes up in dimer contraction of middle edge AA' to contact.
   We want to show that if edges are at most 2.1. and
   AA'B triangle, B is a double pointer, angles beta+gamma<= 0.941
   Then area > 1.345.  *)

  (* See Diagram BMIEZDS  *)
(* ******************************************************************************** *)

let areaBMIEZDS xbeta beta xgamma gamma = 
  let ellxb = ellx xbeta beta in
  let ellxc = ellx xgamma gamma in
  let hb = xbeta - iee in
  let hc = xgamma - iee in
  let rb = sqrt_I (hb * hb + irho * irho) in
  let rc = sqrt_I (hc * hc + irho * irho) in
  let phib = iarc one ellxb rb in
  let phic = iarc one ellxc rc in
  let angleB = ratpi 2 5  + phib + phic in
    ellxb * ellxc * sin_I (angleB) / two;;

let opedgeBMIEZDS xbeta beta xgamma gamma = 
  let ellxb = ellx xbeta beta in
  let ellxc = ellx xgamma gamma in
  let hb = xbeta - iee in
  let hc = xgamma - iee in
  let rb = sqrt_I (hb * hb + irho * irho) in
  let rc = sqrt_I (hc * hc + irho * irho) in
  let phib = iarc one ellxb rb in
  let phic = iarc one ellxc rc in
  let angleB = ratpi 2 5  + phib + phic in
    iloc ellxb ellxc angleB;;

let oneopBM abx = 
  let [xbeta;beta;xgamma;gamma] = abx in 
  let ab = beta+gamma in
    if m (0.313) >> ab then true
    else
      try
	let opedge = opedgeBMIEZDS xbeta beta xgamma gamma in
	  (opedge >> m 2.1) 	  
      with | Unstable -> false;;

let oneareaBM abx = 
  let [xbeta;beta;xgamma;gamma] = abx in 
  let ab = beta+gamma in
    if m (0.313) >> ab then true
    else
      try
	let ar = areaBMIEZDS xbeta beta xgamma gamma in
	let opedge = opedgeBMIEZDS xbeta beta xgamma gamma in
	  (ar >> m 1.345) or (opedge >> m 2.1)  	  
      with | Unstable -> false;;

mktest("oneopBM",fun() ->
	 recursetoeps oneopBM 
	   [[(mk_interval (0.0, ee)); 
	     (mk_interval(0.0,0.313));
	     (mk_interval (0.0, ee)); 
	     (mk_interval(0.0,0.313))]]);; 

mktest("oneareaBM",fun()->
	 recursetoeps oneareaBM 
	   [[(mk_interval (ee,2.0*. ee)); 
	     (mk_interval(0.0,0.313));
	     (mk_interval (0.0,2.0 *. ee)); 
	     (mk_interval(0.0,0.313))]]);; 

opedgeBMIEZDS (m 0.5877) (m 0.2347) (m 0.0) (m 0.078);;

(* end BMIEZDS *)


(* ******************************************************************************** *)
(* ISOCELES calculations, subcritical.
   Assume the subcritical is "2C", but not "3C".
   On subcritical side, we assume we have an isoceles triangle (two long edges)
   We show that the two long edges are never less than 1.76.
   We show that the area is never less than 1.265. (was 1.27)
   We show that the longitudinal angles theta, theta' are ...
*)
(* ******************************************************************************** *)

(* ******************************************************************************** *)
(* sliders *)
(* ******************************************************************************** *)

let slider h = 
  let trho = two * irho in
  let alpha = iatan (h / trho) in
  let m = sqrt_I (h * h + trho * trho) in
    (m,alpha);;

slider (m 0.0);;
ellx (two * iee) (ratpi 2 5);;
thetax (two * iee) (ratpi 2 5);;


(* Case SS = slider+slider *)

let slider_slider h1 h2 = 
  let (m1,alpha1) = slider h1 in
  let (m2,alpha2) = slider h2 in
  let beta = ratpi 2 5 + alpha1 + alpha2 in
    (m1,m2,(iloc m1 m2 beta),alpha1,alpha2);;

let rec minlist f (d, fd)  = function
  | [] -> d
  | x:: xs -> let fx = f x in
      if (fx < fd) then minlist f (x,fx) xs else minlist f (d,fd) xs;;

let rec maxlist f (d,fd) = function
  | [] -> d
  | x:: xs -> let fx = f x in
      if (fx > fd) then maxlist f (x,fx) xs else maxlist f (d,fd) xs;;


minlist (fun x -> x) (-1,12) [3;4;5;2;4;7;11;9];;
maxlist (fun x -> x) (-1,5) [3;4;5;2;4;7;11;9];;

(* uses Euclidean angles *)

let unique_maxsin_congruent th = 
  let t25 = ratpi 2 5 in
  let triple i = 
    let th' = th + m (float_of_int i *. t25) in
      (i,th',sin_I th') in
  let ths  = map triple [0;1;2;3;4] in
  let hth = hd ths in
  let f (_,_,l) = l.hi in
  let (i,th0,l0) = maxlist f  (hth,f hth) ths in
  let unique = forall (fun (j,_,l) -> (j=i) or l.hi < l0.lo) ths in
    (unique,th0);;

unique_maxsin_congruent zero;;
unique_maxsin_congruent (- ratpi 1 10);;

let rot5 = 
  let c = cos_I (ratpi 2 5) in
  let s = sin_I (ratpi 2 5) in
   fun (x,y) -> (c * x - s * y, s * x + c * y);;

let rotm =   
  let c = cos_I (ratpi 2 5) in
  let s = - sin_I (ratpi 2 5) in
   fun (x,y) -> (c * x - s * y, s * x + c * y);;

rot5 (rotm (m 0.3,m 0.4));;

let csv theta = (cos_I theta,sin_I theta);;

let subv (x1,y1) (x2,y2) = (x1 - x2, y1 - y2);;

(* uses Euclidean angles.
   Finds the congruent of angleC that points into the slider pent
   along pentA with given peak angle *)

let pointer_angleC peak_angleA angleC =
  let th = peak_angleA in
  let w = rot5 (subv (csv (th - ratpi 2 5) ) (csv th)) in
  let pos_orient (x1,x2) (y1,y2) = (x1 * y2 - x2 * y1 >> zero) in
  let t25 = ratpi 2 5 in
  let data i =
    let a = angleC + m(t25 *. float_of_int i) in
      (i,a,csv a) in
  let thCs = map data [0;1;2;3;4] in
  let test (_,_,u) = pos_orient (subv (rotm u) u) w &&
    pos_orient w (subv u (rot5 u)) in
  let fiCs = List.filter test thCs in
    fiCs;;

time (pointer_angleC (ratpi 1 2)) zero;;    



(*
theta2 is the congruent of thetaACB that minimizes sin.
NB. Warning, there can be interval overlap making theta2 not well-defined!

To do. Next implement choice of thteta' a congruent of thetaCAB.
*)

let peak_slider dAC thetaACB thetaCAB = 
  (* fist convert thetax angles to Euclidean angles *)
  let eutheta = - thetaACB in
  let eutheta' = m pi + thetaCAB in 
  let (b,peakA) = unique_maxsin_congruent eutheta in
  let _ = b or failwith "sliderh:nonunique" in
  let pC = pointer_angleC peakA eutheta'  in
  let _ = List.length pC = 1 or failwith "sliderh:nonunique pointer" in
  let (_,pointer_angle,_) = hd pC in
  let theta' = m pi - pointer_angle in
  let el2 = iloc one dAC theta' in
  let phi = iarc dAC el2 one in
  let theta2 = peakA in
  let theta1 = theta2 - ratpi 2 5 in 
  let phi1 = theta1 - phi in 
  let phi2 = theta2 - phi in 
  let t1 = iloc one el2 phi1 in
  let t2 = iloc one el2 phi2 in
  let psi = iarc (two * iee) t1 t2 in
  let psi' = psi- ratpi 3 5 in 
  let (h,_) = lawsines t1 (ratpi 3 5) psi' psi in
    h;;

let test_peak_slider()  = 
  let xalpha = m 0.1 in
  let alpha = m 0.0 in
  let xbeta = m 0.1 in
  let beta =  ratpi 1 5 in 
  let v x = (x.lo,x.hi) in
  let (dAB,thBAC,thABC) = thetax xalpha alpha in
  let (dBC,thBCA,thCBA) = thetax xbeta beta in
  let bAC = mk 1.7 2.3 in
  let v = fillout dAB thABC thBAC dBC thBCA thCBA bAC in
  let _ = not (v = None) or failwith "find_slider/test/none" in
  let p = periodize_pent in 
  let Some (arcA,arcB,arcC,dAC,thACB,thCAB) = v in
  let _ =   (dAB,dBC,dAC,p thABC,p thBAC,p thBCA,p thCBA,p thCAB,p thACB) in
  let _ =   (dAC,p thACB,p thCAB) in
    sliderh dAC (hd (p thACB)) (hd (p thCAB));;

time test_peak_slider ();;


(* ******************************************************************************** *)
(* MIDPOINTER *)
(* ******************************************************************************** *)

(* There exist midpointers that are exactly the
   double lattice delaunay, with area aK.

   We prove a slightly weaker bound that area > 1.2903
   and that any subcritical must have thetax parameters:
   and 1.809 < dAC < 1.81.
     abs (thACB ) < 1.e-4
     abs (thCAB + pi/5 ) < 1.e-4

   In fact, we can twist B whenever sgnbeta=true.
   We are reduced to sgnbeta=false, pinwheel (otherwise slide C) 
   midpinter with alpha-beta.
   angles at most 1.0e-4, hence a very small neighborhood of
   the double lattice.

*)

let one_midpointer sgnbeta xs =
  let sgnalpha = true in 
  let xalpha = iee in
  let bAC = mk 1.72 2.1 in
  let [alpha;  xbeta; beta] = xs in
  let p = periodize_pent in
  let abslteps x = (x.lo > -. 1.0e-4 && x.hi < 1.0e-4) in
    try
      let (dAB,thABC,thBAC) = ellthetax xalpha alpha sgnalpha in
      let (dBC,thCBA,thBCA) = ellthetax xbeta beta sgnbeta in
      let v = fillout dAB thABC thBAC dBC thBCA thCBA bAC in
	if v = None then true
	else 
	  let Some (_,_,_,dAC,thACB,thCAB) = v in
	  let a = areamin_acute dAB dBC dAC in
	    if dBC >> dAC then true
	    else if dAB >> dAC then true
	    else if (a >> aK) then true
	    else 
	      (
		(a >> 1.2903) && (m 1.81 >> dAC) && (dAC >> m 1.809) &&
		(forall abslteps (p thACB)) &&
		(forall abslteps (p (thCAB + ratpi 1 5)))
	      )

(* further optional properties:

   (* twistable: *)
	    else if (sgnbeta && beta >> ratpi 1 5 && xbeta >> iee) then true
	    else (
	       not (sgnbeta) &&
		m 1.0e-4 >> alpha && m 1.0e-4 >> beta && 
		iee >> xbeta &&
		dAC >> m 1.77 && m 1.77 >> dAB && m 1.77 >> dBC )
*)
    with Unstable -> false;;

let init_midpointer = [[(mk_interval (0.0,ratpi 2 5 ));(mk_interval (0.0,2.0*. ee));(mk_interval (0.0,ratpi 2 5))]];;


let run_midpointer_t = recursetoeps (one_midpointer true) init_midpointer;;
let run_midpointer_f = recursetoeps (one_midpointer false) init_midpointer;;

(* debug
let ces = [(true,[(0.,9.36267570731e-09);(0.812299222175,0.812299230934);(1.25663705207,1.25663706144)])];;

let delM sgnbeta ce = 
  let sgnalpha = true in
  let xalpha = iee in
  let low (x,_) = m x in
  let [alpha;xbeta;beta] = (* map (low) *) map mk_interval ce in
  let (dAB,thABC,thBAC) = ellthetax xalpha alpha sgnalpha in
  let (dBC,thCBA,thBCA) = ellthetax xbeta beta sgnbeta in
  let bAC = mk 1.72 2.1 in
  let v = fillout dAB thABC thBAC dBC thBCA thCBA bAC in
  let _ = not (v = None) or failwith "delAcoordinates" in
  let Some (_,_,_,dAC,thACB,thCAB) = v in
    (dAB.lo,dAC.lo,dBC.lo,thABC.lo,thBAC.lo,thCAB.lo);;

let get = 
  let (sgnbeta,ce) = hd ces in
    delM sgnbeta ce;;
*)

(* ******************************************************************************** *)
(* ISOCELES *)
(* ******************************************************************************** *)


let one_two_isoceles sgnalpha sgnbeta xs =
  let [xalpha; alpha;  xbeta; beta] = xs in
  let ratpi15 = ratpi 1 5 in
    try
      let (dAB,thABC,thBAC) = ellthetax xalpha alpha sgnalpha in
      let dAC = dAB in
      let (dBC,thCBA,thBCA) = ellthetax xbeta beta sgnbeta in
      let arcB = iarc_mono dAB dBC dAC in
      let arcC = arcB in
      let arcA = iarc_mono dAC dAB dBC in
      let pB = periodize_pent (thBAC+thBCA +arcB) in
      let a = areamin_acute dAC dAB dBC in
      let twistableBtt = not (sgnalpha) or not (sgnbeta) or
	(ratpi15 >> alpha && beta >> ratpi15) or
	   (ratpi15 >> beta && alpha >> ratpi15) in
      let has0 x = (x.lo <= 0.0) && (0.0 <= x.hi) in
      let neg x = (x.hi <= 0.0) in
      let posmax x = (x.hi <= 0.2) in (* test added 2 may 2015 *)
      let pos x = (x.lo >= 0.0) in
      let negr x = neg x && (x.lo +. ratpi 1 5 >= 0.0) in
      let negr x = (x.lo >= -0.464 && x.hi <= -0.164) in (* modified 8 may *)
(*      let negr x = (x.lo >= -0.37 && x.hi <= -0.16) in (* fails on -0.37 *) *)
      let old_sumt x = (x.lo >> 0.15) in (* was 0.2 nix, alpha open out condition *)
      let sumt x = (x.lo >> 0.18) in (* was 0.2 nix, alpha open out condition *)
(*      let minedge = m 1.74 in  was 1.76 nix, was 1.75 nix, was 1.74 nix *)
      let minarea = 1.265 in (* was 1.27 nix *)
	if dBC >> dAB then true
	  (* next line rules out both pointersB being the same vertex of B*)
	else if sgnalpha && sgnbeta && 
	  (four * iee >> dAC + xalpha + xbeta) then true
	else if not(exists has0 pB) then true
	else if (a >> aK) then true
	else
	  let thACB = - thABC - arcA in
	  let thCAB = - thCBA - arcC in
	    if not(pet dAC thACB thCAB) then true
	    else 
	      let m2 = m 0.2 in
	      let thACBm2 = periodize_pent (thACB + m2) in
	      let thCABm2 = periodize_pent (thCAB + m2) in
	      let thACBs = periodize_pent (thACB) in
	      let thCABs = periodize_pent (thCAB) in
	      let thsum = periodize_pent (thACB + thCAB) in
	      let mm4 = m (-. 0.4) in
	      let small ths = forall (fun x -> mm4 >> x) ths in
	      let notableBff = sgnalpha or sgnbeta or
		(iee >> xalpha && xbeta >> iee) or
		(xalpha >> iee && iee >> xbeta) or
		(dAC >> m 1.77 && small thACBs && small thCABs) in
	      let isopin = 
		((a >> minarea) && 
		   (forall sumt thsum) &&
		   (forall neg thACBm2) &&
		   (forall neg thCABm2) &&
		   twistableBtt && notableBff
		) in
	      let symtj_type = 
		((* (a >> 1.28)  && don't need, 1.282 follow from 1.78 iso *) 
		  not (sgnalpha) &&
		    (alpha.lo >>  ratpi 1 5) && (* ==> pentA rotatable *)
		    (dAC.lo >> 1.78) &&
		   (forall pos thACBs) && 
		   (forall posmax thACBs) && 
		  (forall negr thsum)) in
		isopin or symtj_type
    with Unstable -> false;;

let init_1_2_iso = [[(mk_interval (0.0,2.0*. ee));(mk_interval (0.0,ratpi 2 5 ));(mk_interval (0.0,2.0*. ee));(mk_interval (0.0,ratpi 2 5))]];;


let isott = recursetoeps (one_two_isoceles true true) init_1_2_iso (* 53684627,true *);; (* (232983, true) *) (* (251249, true) *)


let isotf = recursetoeps (one_two_isoceles true false) init_1_2_iso;; (* (55492767, true) *) (*  (953901, true) *)  (* (1917319, true) *)

let isoft = recursetoeps (one_two_isoceles false true) init_1_2_iso;; (* (4176583, true) *) (* (1083813, true) *) (* (2193405, true) *)

let isoff = recursetoeps (one_two_isoceles false false) init_1_2_iso;; (* (53688491, true) *)  (* (398189, true) *) (* (479279, true) *)

let ces = [
((false,false),[(0.,8.75868279178e-09);(0.294524301911,0.294524311274);(8.75868279178e-09,1.75173655836e-08);(0.0392697864551,0.0392697958178)]);
((false,false),[(0.,8.75868279178e-09);(0.311704886736,0.311704896098);(8.75868279178e-09,1.75173655836e-08);(0.00490861680645,0.00490862616913)]);
((false,false),[(0.,8.75868279178e-09);(0.311704886736,0.311704896098);(8.75868279178e-09,1.75173655836e-08);(0.00490861680645,0.00490862616913)]);
((true,true),[(0.,8.75868279178e-09);(0.311704886736,0.311704896098);(0.,8.75868279178e-09);(0.00490862616913,0.0049086355318)]);
((false,true),[(0.547162122398,0.547162131157);(1.01111623644,1.0111162458);(1.05158452665,1.05158453541);(1.25663705207,1.25663706144)]);
((false,true),[(0.614911514765,0.614911523524);(0.903207878544,0.903207887907);(0.0296782010495,0.0296782098082);(0.,9.36267570731e-09)]);
];;


(*   
   ISOCELES COMPENSATOR

   if dACsub thetaACBsub thetaCABsub are the edge data for subcritical,
   and dACcomp thetaACBcomp thetaCABcomp are the data for the compensator.
   then dACsub = dACcomp, thetaACBsub = - thetaACBcomp, thetaCABsub = -thetaCABcomp
   So we must negate the theta conditions.

   Note the conditions are symmetrical in thetaACB and thetaCAB.
*)


let compensator_canfit_isopin thetaACBcomp thetaCABcomp = 
  let thACB = - thetaACBcomp in
  let thCAB = - thetaCABcomp in
  let m2 = m 0.2 in
  let thACBm2 = periodize_pent (thACB + m2) in
  let thCABm2 = periodize_pent (thCAB + m2) in
  let thsum = periodize_pent (thACB + thCAB) in
  let neg x = (x.lo <= 0.0) in (* NB x.hi becomes x.lo here *)
  let sumt x = (x.hi >= 0.18) in 
		(
		   (exists sumt thsum) &&
		   (exists neg thACBm2) &&
		   (exists neg thCABm2)
		);;

let compensator_canfit_notableBff_isopin thetaACBcomp thetaCABcomp = 
  let thACB = - thetaACBcomp in
  let thCAB = - thetaCABcomp in
  let thACBs = periodize_pent (thACB) in
  let thCABs = periodize_pent (thCAB) in
  let thsum = periodize_pent (thACB + thCAB) in

(* XXD not finished *)
  let neg x = (x.lo <= 0.0) in (* NB x.hi becomes x.lo here *)
  let sumt x = (x.hi >= 0.18) in 
		(
		   (exists sumt thsum) &&
		   (exists neg thACBm2) &&
		   (exists neg thCABm2)
		);;


let compensator_canfit_isotj dAC thetaACBcomp thetaCABcomp = 
  let thACB = - thetaACBcomp in
  let thCAB = - thetaCABcomp in
  let thACBs = periodize_pent (thACB) in
  let thsum = periodize_pent (thACB + thCAB) in
  let posr x = (x.hi >= 0.0) && (x.lo <= 0.2) in
  let negr x = (x.hi >= -0.464 && x.lo <= -0.164) in (* modified 8 may *)
		(
		  (dAC.hi >> 1.78) &&
		   (exists posr thACBs) && 
		  (exists negr thsum)
		);;



let compensator_canfit is_isopin dAC thetaACBcomp thetaCABcomp = 
  if is_isopin then compensator_canfit_isopin thetaACBcomp thetaCABcomp
  else compensator_canfit_isotj dAC thetaACBcomp thetaCABcomp;;

let one_isocompensator sgnalpha sgnbeta is_isopin xs =
  let [xalpha; alpha;  xbeta; beta] = xs in
    try
      let areamin_subcritical_iso = 
	if is_isopin then 1.265 else 1.2827 in
      let atarget = aK +. (aK -. areamin_subcritical_iso) in
      let (dAB,thABC,thBAC) = ellthetax xalpha alpha sgnalpha in
      let (dBC,thCBA,thBCA) = ellthetax xbeta beta sgnbeta in
      let bAC = 
	if is_isopin then mk (*  *) 1.72 1.79 else mk 1.78 1.79 in
      let v = fillout dAB thABC thBAC dBC thBCA thCBA bAC in
      let isotj_rotatableA = not(is_isopin) &&
	sgnalpha && (not sgnbeta or alpha.lo >> 0.0) && (ee >> xalpha.hi) in
      let isotj_rotatableB = not(is_isopin) &&
	not sgnalpha && not sgnbeta && (xalpha >> iee) && (iee >> xbeta) in
	if v = None then true
	else 
	  let Some (_,_,_,dAC,thACB,thCAB) = v in
	  let a = areamin_acute dAB dBC dAC in
	    if a >> atarget then true
	    else
	      if not(compensator_canfit is_isopin dAC thACB thCAB) then true
	      else isotj_rotatableA or isotj_rotatableB
    with Unstable -> false;;

let isocompttt = recursetoeps (one_isocompensator true true true) init_1_2_iso;; (* (217557, true) *)

(* gives ce *)
let isocomptft = recursetoeps (one_isocompensator true false true) init_1_2_iso;; 

(* false,true,true not needed by symmetry *)

(* not yet done *)
let isocompfft = recursetoeps (one_isocompensator false false true) init_1_2_iso;; 



(* Compensator for isotj series. -- they all pass! *)
let isocompttf = recursetoeps (one_isocompensator true true false) init_1_2_iso;; (* (17707, true) *)

let isocomptff = recursetoeps (one_isocompensator true false false) init_1_2_iso;; (*  (20061, true) *)

(*  needed canfit is not symmetric here *) 
let isocompftf = recursetoeps (one_isocompensator false true false) init_1_2_iso;;  (* (29095, true) *)


let isocompfff = recursetoeps (one_isocompensator false false false) init_1_2_iso;;  (* (21253, true) *)



(* Math'ca plots *)
let delAcoordinates sgnalpha sgnbeta ce = 
  let low (x,_) = m x in
  let [xalpha;alpha;xbeta;beta] = (* map (low) *) map mk_interval ce in
  let (dAB,thABC,thBAC) = ellthetax xalpha alpha sgnalpha in
  let (dBC,thCBA,thBCA) = ellthetax xbeta beta sgnbeta in
  let bAC = mk 1.72 1.79 in
  let v = fillout dAB thABC thBAC dBC thBCA thCBA bAC in
  let _ = not (v = None) or failwith "delAcoordinates" in
  let Some (_,_,_,dAC,thACB,thCAB) = v in
    (dAB.lo,dAC.lo,dBC.lo,thABC.lo,thBAC.lo,thCAB.lo);;



let ces = [


(* isopin *)

((true,false),[(0.,8.75868279178e-09);(0.116198960418,0.116198969781);(0.320723405696,0.320723414455);(0.692119529332,0.692119538695)]);

((false,false),[(0.146103228544,0.146103237302);(0.779249647447,0.77924965681);(0.137757535163,0.137757543922);(0.029068861029,0.0290688703917)]);

((true,false),[(0.,8.75868279178e-09);(0.0732474609068,0.0732474702694);(0.3773906119,0.377390620659);(0.735071000756,0.735071010119)]);

((true,false),[(0.,8.75868279178e-09);(0.116198960418,0.116198969781);(0.320723405696,0.320723414455);(0.692119529332,0.692119538695)]);

((true,false),[(0.0524139985991,0.0524140073578);(0.101460114605,0.101460123968);(0.392058664109,0.392058672867);(0.706858337695,0.706858347058)]);

(* isotj *)

((true,true),[(0.440408423684,0.440408432443);(0.195568646882,0.195568656245);(0.835757146845,0.835757155603);(1.25663705207,1.25663706144)]);

((false,false),[(0.808204152588,0.808204161346);(1.2179423867,1.21794239606);(0.292192714714,0.292192723473);(0.235600152545,0.235600161907)]);

((true,true),[(0.440408423684,0.440408432443);(0.195568646882,0.195568656245);(0.835757146845,0.835757155603);(1.25663705207,1.25663706144)]);

((true,true),[(0.440408423684,0.440408432443);(0.195568646882,0.195568656245);(0.835757146845,0.835757155603);(1.25663705207,1.25663706144)]);

((false,true),[(0.275488452689,0.275488461447);(0.157079623317,0.157079632679);(0.291596546211,0.29159655497);(0.132533533866,0.132533543228)]);

((false,true),[(0.206051297183,0.206051305941);(0.390244703075,0.390244712438);(0.109993123821,0.109993132579);(0.0196349447223,0.0196349540849)]);

((true,true),[(0.,8.75868279178e-09);(0.309734726975,0.309734736337);(0.,8.75868279178e-09);(0.,9.36267570731e-09)]);

];;



let dax = 
  let bce = hd ces in
  let ((sgnalpha,sgnbeta),ce) = bce in
    delAcoordinates sgnalpha sgnbeta ce;;


let debug = 
  let bce = hd ces in
  let p = periodize_pent in
  let ((sgnalpha,sgnbeta),ce) = bce in
  let [xalpha;alpha;xbeta;beta] = map mk_interval ce in
  let (dAB,thABC,thBAC) = ellthetax xalpha alpha sgnalpha in
  let (dBC,thCBA,thBCA) = ellthetax xbeta beta sgnbeta in
  let bAC = mk 1.72 1.79 in
  let v = fillout dAB thABC thBAC dBC thBCA thCBA bAC in
  let _ = not (v = None) or failwith "delAcoordinates" in
  let Some (_,_,_,dAC,thACB,thCAB) = v in
    (dAB,dBC,dAC,"thABC",p thABC,"thBAC",p thBAC,"thBCA:",p thBCA,"thCBA:",
     p thCBA,"thCAB:",p thCAB,"thACB:",p thACB,"thsumAC",p (thCAB+thACB));;


(* moved from dimer.ml, August 2016 *)

(*
let onedACfail (sgnalpha,sgnbeta) xs  = 
  try
  let v = mk_isosceles sgnalpha sgnbeta xs in
  if (v = None) then true
  else 
    let (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in
       (dAC >> 173 // 100)
  with Unstable -> false;;
  
recursesgn onedACfail domain2C;;

[(0.0680620423078,0.0680620510665);(0.217492662825,0.217492672188);(0.0671386581745,0.0671386669332);(0.193473317509,0.193473326872)];;

let onedACmaxfail (sgnalpha,sgnbeta) xs  = 
  try
  let v = mk_isosceles sgnalpha sgnbeta xs in
  if (v = None) then true
  else 
    let (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in
       (dAC <<  178 // 100) (* 179, 178 fails *)
  with Unstable -> false;;
[(0.,8.75868279178e-09);(0.313545663681,0.313545673044);(0.,8.75868279178e-09);(0.00122708164088,0.00122709100355)];;

*)

(********************************************************************************* *)

(* cut from pent.ml 9/2016 *)
(*
let mk_isosceles sgnalpha sgnbeta xs =
  let [xalpha; alpha;  xbeta; beta] = xs in
  let range = mk 172.0 179.0 / m 100.0 in
  let range' = merge_I (two * kappa) range in
    try
      let (dAB,thABC,thBAC) = ellthetax_sgn xalpha alpha sgnalpha in
      let (dBC,thCBA,thBCA) = ellthetax_sgn xbeta beta sgnbeta in
      if disjoint_I range dAB or disjoint_I range' dBC then None
      else
	let dAB = inter_I range dAB in
	let dBC = inter_I range' dBC in
	let dAC = dAB in
	let arcB = iarc dAB dBC dAC in
	let arcC = arcB in
	let arcA = iarc dAC dAB dBC in
	let a = areamin_acute dAC dAB dBC in
	let thACB = pi25 - (arcA + thABC) in
	let thCAB = pi25 - (arcC + thCBA) in
	if (a >> aK) or 
	  not(hasint ((arcB+thBAC+thBCA)/pi25)) or
	  not(pet dAC thACB thCAB)
	then None
	else
	  Some (a,dAB,dAC,dBC,arcA,arcB,arcC,thABC,thBAC,thCBA,thBCA,thACB,thCAB)
    with e -> raise e;;
*)


(********************************************************************************* *)

(* cut from pent.ml september 2016.
   This non-anomaly lemma is no longer used. *)

(* non anonaly test JJZ area > 1.345 *)

let oneJJZ = 
  let m1345 =  1345 // 1000 in
  fun abx ->
    try
      let (alpha,beta,xalpha) = abx in
      disjoint_from_lj alpha beta or
	let ((xbeta,_),(l1,l2,l3)) = ljedge_extended alpha beta xalpha in
	(area_exceeds l1 l2 l3 m1345) or (xbeta >> sigma) or (sigma >> xbeta) 
    with | Unstable -> false;;

mktest ("oneJJZ",fun() ->
	  recursetofinish oneJJZ 
	    [[zero2 pi25;zero2 pi25;two*sigma]]);;


(* cut from pent.ml september 2016  *)

(*
let tjedge =
    fun alpha beta xgamma ->
  let gamma = pi - (alpha + beta) in
  let alpha' = pi25 - alpha in
  let beta' = pi25 - beta in
  let gamma' = pi25 - gamma in
  let delta1 = pi - (gamma' + pi25) in
  let delta2 = pi - delta1 in
  let delta3 = pi - (alpha' + delta2) in
  let delta4 = pi - (beta' + pi25) in
  let (x1,x2) = lawsines xgamma delta1 pi25 gamma' in
  let x3 = two * sigma - x1 in
  let (x4, x5) = lawsines x3 delta3 delta2 alpha' in
  let x6 = two * sigma - (x5 - x2) in
  let (x7,x8) = lawsines x6 pi25 beta' delta4 in
  let x9 = x4 - x7 in
  let t = x1,x2,x3,x4,x5,x6,x7,x8,x9 in
  (* x6 -> x8 3/10/2016 *)
    ((ellxmono x9 alpha),(ellxmono x8 beta),(ellxmono xgamma gamma));;
*)

