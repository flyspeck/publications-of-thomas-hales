(*  dimer *)

(* This file contains all the dimer calculations,
   excluding local optimality near the pentagonal ice-ray arrangement
   and excluding pseudo-dimers *)

(* The documentation for this file is contained in 
   handwritten notes "Dimer March 2016"
*)

reneeds "pent.ml";;
reneeds "pet.ml";;


module Dimer = struct

open Pent;;
open Pet;;

(* ************************************************** *)
(* iso_2C and iso_2C are footnotes in article *)
(* ************************************************** *)


(* true if isosceles subcritical, with condition on thABC *)

(* true if param xs fall outside domain of subcrit AB=AC isosc tri *)

(* 
From the article about iso2C and iso2C'
We have a long isosceles triangle,
double contact,
one of contacts is between A and B,
contact between A and B is slider or midpointer.
We claim such is not subcritical.
*)

let one_iso2C xs = 
  let dACrange = merge_I (172//100) (179//100) (* mk 1.72 1.79 *) in
  try
    match  mk2C dACrange xs with
    | None -> true
    | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	    (dAC,thACB,thCAB,arcB)) ->
      (let th = Pet.periodize_pent thABC in
       (a >> aK ) or disjoint_I dAB dAC or 
	 forall (fun t -> t >> zero) th)
  with Unstable -> false;;

(* true if params xs out of domain of subcrit BC AB isosc tri *)

let one_iso2C' xs = 
  let dACrange = merge_I (two*kappa) (179//100) (* m 1.79 *) in
  try
    match  mk2C dACrange xs with
    | None -> true
    | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	    (dAC,thACB,thCAB,arcB)) ->
       (a >> aK) or disjoint_I dBC dAB or dAC >> dAB
  with Unstable -> false;;

(* 
   one_scaleneto3C_deprecated was used in an early approach
   to to squeezing lemma.

   the xalpha + xbeta condition removes the trivial case of
   a cloverleaf 
*)

let one_scaleneto3C_deprecated xs = 
  try
    let pi310 = ratpi 3 10 in
    let dACrange = mk 1.72 2.0 in
    let ([xalpha; alpha;  xbeta; beta],_) = xs in
    let is_cloverleaf = xalpha + xbeta << m 0.1 in
    if (alpha + beta >> pi310) or is_cloverleaf then true
    else
      match  mk2C dACrange xs with
      |None -> true
      |Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	     (dAC,thACB,thCAB,arcB)) ->
	(a >> aK) or (dAC >> m 1.79) 
  with Unstable -> false;;

(* one_pintx is a footnote in the article.
   What gets used is that longest edge is BC *)

let pint_outdomfn (a,alpha,beta,xa,xb,xc,dBC,dAC,dAB) =
  (dAC << 172 // 100) &&
    (xb >>= 9 // 10) && (* 1.0 fails *)
    (beta >>= 12 // 10) &&  (* 1.25 fails *)
    (dBC >> dAB && dBC >> dAC);;   

let one_pintx xs = 
  try
  let ([alpha;beta;xa],_) = xs in
  if outdomfn_pint alpha beta then true
      else 
      let (dBC,dAC,dAB,xc,xb)= pintedge_extended alpha beta xa in
      let a = areamin_acute dBC dAC dAB in
      let inadmissible xc a = xc >> two*sigma or (a >> aK+epsN_I) in
      inadmissible xc a or 
	pint_outdomfn (a,alpha,beta,xa,xb,xc,dBC,dAC,dAB)
  with Unstable -> false;;

(* one_pinwheelx gets used in pent.ml to restrict the domain
   of a shared pinwheel 3C.  See pent.ml  *)

let one_pinwheelx xs =
  try
  let ([alpha;beta;xc],_) = xs in
  if alpha+beta >> pi15 then true
      else 
      let (d1,d2,d3)= pinwheeledge alpha beta xc in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epsN_I) in
      let one_pinwheelx_constant = 8 // 10 in (* 0.7 fails *)
      let outdom = (xc << one_pinwheelx_constant) in 
      inadmissible or outdom
  with Unstable -> false;;

(* needed for the numerical stability of L3 type L-junctions
   in coordinates.
   one_ljx and one_tjx are both footnotes in the article.
 *)

let one_ljx xs =
  try
    let ([alpha;beta;xa],_) = xs in
    if outdomfn_lj alpha beta then true
    else 
      let (d1,d2,d3)= ljedge alpha beta xa in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epsN_I) in
      let one_ljx_constant = 9//10 in (* 0.8 fails *)
      let outdom = (beta << one_ljx_constant) in 
      inadmissible or outdom
  with Unstable -> false;;

let one_tjx xs =
  try
    let ([alpha;beta;xc],_) = xs in
    if outdomfn_tj alpha beta then true
    else 
      let (d1,d2,d3)= tjedge alpha beta xc in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epsN_I) in
      let one_tjx_constant = one in
      let outdom = (beta >>  one_tjx_constant) in 
      inadmissible or outdom
  with Unstable -> false;;

let domain_iso2C =   (* sgnalpha=false means A points to B *)
  let zpi25 = zero2 (ratpi 2 5) in
  let z2sig = zero2 (two*sigma) in
  let r_slider = [z2sig;zero;z2sig;zpi25] in
  let r_midpointer = [sigma;zpi25;z2sig;zpi25] in
  let b = [(false,true);(false,false)] in
  let f r = map (fun t -> (r,t)) b in
  f r_slider @ f r_midpointer;;

let domain_iso2C' =   (* sgnbeta=true means B points to C *)
  let zpi25 = zero2 (ratpi 2 5) in
  let zpi5 = zero2 (ratpi 1 5) in
  let z2sig = zero2 (two*sigma) in
  let r_slider = [z2sig;zpi25;z2sig;zero] in
  let r_midpointer = [z2sig;zpi25;sigma;zpi5] in
  let b = [(false,true);(true,true)] in
  let f r = map (fun t -> (r,t)) b in
  f r_slider @ f r_midpointer;;

let domain_scaleneto3C_deprecated = 
  [(map zero2 [two*sigma;pi25;two*sigma;pi25],(true,true))];;

let dummybool = (map (fun t->(t,(true,true))));;

let run_group1() = 
  [recursepairtoeps one_iso2C domain_iso2C;
   recursepairtoeps one_iso2C' domain_iso2C';
(*   recursepairtoeps one_scaleneto3C_deprecated domain_scaleneto3C_deprecated; *)
   recursepairtoeps one_pintx (dummybool pintdomain);
   recursepairtoeps one_pinwheelx (dummybool pinwheeldomain);
   recursepairtoeps one_ljx (dummybool ljdomain);
   recursepairtoeps one_tjx (dummybool tjdomain)
];;

(* ************************************************************ *)
(* dimer stuff *)
(* ************************************************************ *)

let dimer_outdomfn_null alphaB betaB xbetaB alphaD = false;;

let dimer_outdomfn_eps eps alphaB betaB xbetaB alphaD = 
  let nearlyt t x = (x << t + eps) && x >> t - eps in
  nearlyt pi15 betaB && 
    nearlyt sigma xbetaB &&
    nearlyt zero alphaB &&
    nearlyt zero alphaD;;

(* deprecated let dimer_outdomfn1 = dimer_outdomfn_eps (m 0.1);; *)

let ice_ray_nbd = 1 // 100;;

let dimer_outdomfn_01 = dimer_outdomfn_eps ice_ray_nbd;;

let one_dimer_eps pseudo eps dimer_outdomfn xs = 
  let ([alphaB;betaB;xbetaB;alphaD],
       ((sB,edgeB,disjointB),(sD,edgeD,disjointD))) = xs in
  try
    (* subcritical triangle ABC: *)
    if disjointB alphaB betaB xbetaB then true 
    else
      let (dBC,dAC,dAB) = edgeB alphaB betaB xbetaB in
      let aABC = areamin_acute dBC dAC dAB in
      if aABC >> aK or dAC << dAB or dAC << dBC then true
      else
      (* second triangle ADC of dimer: *)
      let betaD = pi25 - betaB in
      let xbetaD = two*sigma - xbetaB in
      if disjointD alphaD betaD xbetaD then true
      else 
	let (dCD,dAC',dAD) = edgeD alphaD betaD xbetaD in
	let aADC = areamin_acute dCD dAC' dAD in
	let pseudodimer = dAD >> dAC' +  3 // 100 (*  m 0.03 *) 
	  && dAD >>  18 // 10 (* m 1.8 *) in 
	aABC + aADC >> two * aK - eps or 
	  (pseudo && pseudodimer) or
	  dimer_outdomfn alphaB betaB xbetaB alphaD
  with | Unstable -> false;;

let one_dimer = one_dimer_eps false zero;;

let dimer_types = [
  ("pint",shared_pintedge,outdomfn_shared_pint)  ;
  ("pinw",shared_pinwheeledge,outdomfn_shared_pinwheel);
  ("lj1",shared_lj1edge,outdomfn_shared_lj1);
  ("lj2",shared_lj2edge,outdomfn_shared_lj2);
  ("lj3",shared_lj3edge,outdomfn_shared_lj3);
  ("tj1",shared_tj1edge,outdomfn_shared_tj1);
  ("tj2",shared_tj2edge,outdomfn_shared_tj2);
  ("tj3",shared_tj3edge,outdomfn_shared_tj3);];;

let dtype = List.nth dimer_types;;

let dimer_domain (i,j) = 
  ((map zero2 [pi25;pi25;two*sigma;pi25]),
  (dtype i,dtype j));;

let dtype_labels xs = 
  let (_,((sB,_,_),(sD,_,_))) = xs in
  (sB,sD);;

let recurse_dimer pseudo eps f d =
    try 
      let _ = report "..." in
      recurserpair (1.0e-8) 0 (one_dimer_eps pseudo eps f) [d]
    with Failure s ->
      let (sB,sD) = dtype_labels d in
      failwith ("one_dimer("^sB^","^sD^") "^s);;

(* This does cases that don't approach the pentagonal ice-ray dimer. *)
(* all run on 3/10/2016: *)
let recurse0 s = recurse_dimer false zero 
  dimer_outdomfn_null (dimer_domain s);;

let run_group2 () = 
  [
    map (fun i -> recurse0 (0,i)) (0--7);
    map (fun i -> recurse0 (i,0)) (0--7);
    map (fun i -> recurse0 (4,i)) (0--7);
    map (fun i -> recurse0 (i,4)) (0--7);
    map (fun i -> recurse0 (5,i)) (0--7);
    map (fun i -> recurse0 (i,5)) (0--7);
    map (fun i -> recurse0 (6,i)) (0--7);
    map (fun i -> recurse0 (i,6)) (0--7)];;

let needsmore = [1;2;3;7];;

let morecases = outer pair needsmore needsmore;;

(* deprecated let recurse1 pseudo s = recurse_dimer pseudo zero 
  dimer_outdomfn1 (dimer_domain s);;
*)

let recurse_01 pseudo s = recurse_dimer pseudo zero 
  dimer_outdomfn_01 (dimer_domain s);;

(* This reduces dimers to 0.01 nbd of pentagonal ice-ray dimer.
   The "true" cases also explicitly exclude pseudo-dimers. *)

let run_group3() = 
  [
    recurse_01 false (1,1);
    recurse_01 false (2,1);
    recurse_01 false (3,1);
    recurse_01 false (7,1);

    recurse_01 false (1,2);
    recurse_01 false (2,2);
    recurse_01 false (3,2);
    recurse_01 false (7,2);
    
    recurse_01 false (2,3);
    recurse_01 false (7,3);

    recurse_01 false (2,7);
    recurse_01 false (7,7);

(* last 4 cases exclude pseudo-dimers.
   These tests fail with input pseudo=false. *)
    recurse_01 true (1,3);
    recurse_01 true (3,3);
    recurse_01 true (1,7);
    recurse_01 true (3,7)];;

(* ************************************************************ *)
(* pseudo-dimer stuff *)
(* ************************************************************ *)

(* Calculate 3C+3C bound on dimer/pseudo-dimer *)

(* 0.007 good, 0.006 fails, 
   so pseudo-dimer area sum is off by at most 0.007 
   The paper uses epsM = 0.008.
*)
let recurseN s = recurse_dimer false (7//1000) (* m 0.007 *)
  dimer_outdomfn_null (dimer_domain s);;

let run_group4() = 
  [
    recurseN (1,3);
    recurseN (3,3);
    recurseN (1,7);
    recurseN (3,7);
  ];;

(* ************************************************** *)
(* general form of squeeze_calc for squeezing lemma *)
(* ************************************************** *)

(* squeeze_calc is documented in article.
   
*)

let safetan_I x = if (x.high < 1.57) && (x.low > -. 1.57) then
    tan_I x else raise Unstable;;
(* failwith "tan out of range";; *)

let one_sigma arcA thBAC thABC alpha = 
  let f0 alpha = safetan_I (-arcA + thBAC + pi310 + (pi25 - alpha)) in
  let f1 alpha = safetan_I (-arcA - thABC + pi310 + alpha) in
  (mergefn f0 f1 merge_I pi25) alpha;;

let _ = one_sigma (m 1.0) (m 0.3) (m 0.2) (m 0.4);;

let test =
  let arcA = m 1.0 in
  let thBAC = m 0.3 in
  let thABC t = t - thBAC in
  let e = m (1.0e-6) in
  let t0 = pi25 - e in
  let t1 = pi25 + e in
  (one_sigma arcA thBAC (thABC t0) t0,
   one_sigma arcA thBAC (thABC t1) t1);;

let squeezable dACrange outofdomfn xs =
  let [xalpha;alpha;xbeta;beta] = xs in
  try 
  match mk2Ce dACrange xs with
  | None -> true
  | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	  (dAC,thACB,thCAB,arcB)) ->
    (if outofdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	  (dAC,thACB,thCAB,arcB)) then true
     else 
	let dAB_sinA =dAB * sin_I (arcA) in
	let sigmaA = one_sigma arcA thBAC thABC alpha in
	let sigmaC = one_sigma arcC thBCA thCBA beta in
	sigmaA << dAB_sinA/dAC or
	  sigmaC << dAB_sinA/dAC or
	  (one/sigmaA + one/sigmaC)*dAB_sinA >> dAC)
  with Unstable -> false;;

let domain2Ce =   [map zero2 [two*sigma;pi45;two*sigma;pi45]];;


let squeeze_calc() =
  let top = 232//100 in
  let _ =  kappa*  (sqrt_I(square_I top - square_I(two*kappa))) >> 
    (aK+epsN_I) or failwith "232" in
  let dACrange = merge_I (two*kappa) (232//100) in
  let outofdomfn (a,_,_,_) = (a >> aK+epsN_I) in
  recursetoeps (squeezable dACrange outofdomfn) domain2Ce;;



(* ************************************************************ *)
(* unsorted stuff *)
(* ************************************************************ *)


(* Junk: check that the second part of 
   pseudo-dimer can be subcritical away from ice-ray.
(*	aABC + aADC >> two * aK - eps or *)
	  aADC >> aK or

let recurseM s = recurse_dimer zero dimer_outdomfn1 (dimer_domain s);;
recurseM (1,3);;
recurseM (3,3);;
recurseM (1,7);;
recurseM (3,7);;

*)

(* this verifies a lower bound 1.27 on subcritical isosceles triangles.
   I believe this is no longer needed.  *)

let one127 (sgnalpha,sgnbeta) xs  = 
  try
    let dACrange = merge_I (172//100) (179//100) (* mk 1.72 1.79 *) in
    let v = mk2C dACrange (xs,( sgnalpha, sgnbeta)) in
    if (v = None) then true
    else 
      let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = the v in 
      (a >> 127 // 100) or disjoint_I dAB dAC or
	dAC >> dAB
  with Unstable -> false;;

let domain2C =   [map zero2 [two*sigma;ratpi 2 5;two*sigma;ratpi 2 5]];;

let recursesgn f dom = 
  map (fun t -> recursetoeps (f t) dom)
    [(true,true);(true,false);(false,true);(false,false)];;

let run_group5() = 
  (squeeze_calc(),
  recursesgn one127 domain2C);;




    end;;
