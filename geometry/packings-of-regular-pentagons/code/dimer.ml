(*  dimer *)

(* This file contains all the dimer calculations,
   excluding local optimality near the Kuperberg arrangement
   and excluding pseudo-dimers *)


reneeds "pent.ml";;
reneeds "pet.ml";;


module Dimer = struct

open Pent;;
open Pet;;

  let range = mk 172.0 178.0 / m 100.0;;


  let inf = one / mk_interval (-1.0,1.0);;
disjoint_I eps_I inf;;



(* true if isosceles subcritical, with condition on thABC *)

let one_iso2C xs = 
  let dACrange = mk 1.72 1.79 in
  try
    let v = mk2C dACrange xs in
    if (v = None) then true
    else 
      let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = the v in 
(*
(a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in *)
      let th = Pet.periodize_pent thABC in
       (a >> aK) or disjoint_I dAB dAC or 
	 forall (fun t -> t >> zero) th
  with Unstable -> false;;

let one_iso2C' xs = 
  let dACrange = merge_I (two*kappa) (m 1.79) in
  try
    let v = mk2C dACrange xs in
    if (v = None) then true
    else 
      let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = the v in
(* (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in *)
       (a >> aK) or disjoint_I dBC dAB or dAC >> dAB
  with Unstable -> false;;

(* the xalpha + xbeta condition removes the trivial case of
   a cloverleaf *)

let one_scaleneto3C xs = 
  let pi310 = ratpi 3 10 in
  let dACrange = mk 1.72 2.0 in
  let ([xalpha; alpha;  xbeta; beta],_) = xs in
  if (alpha + beta >> pi310) or (xalpha + xbeta << m 0.1) then true
  else
    try
      let v = mk2C dACrange xs in
      if (v = None) then true
      else 
	let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = the v in 
(* (a,dAB,dAC,dBC,arcA,arcB,arcC,
	     thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in *)
	(a >> aK) or (dAC >> m 1.79) 
    with Unstable -> false;;

let pint_domain_constraint (a,alpha,beta,xa,xb,xc,dBC,dAC,dAB) =
  (dAC << 172 // 100) &&
    (xb >>= 9 // 10) && (* 1.0 fails *)
    (beta >>= 12 // 10) ;;   (* 1.25 fails *)


let one_pintx xs = 
  let ([alpha;beta;xa],_) = xs in
  if disjoint_from_pint alpha beta then true
      else 
      let (dBC,dAC,dAB,xc,xb)= pintedge_extended alpha beta xa in
      let a = areamin_acute dBC dAC dAB in
      let inadmissible xc a = xc >> two*sigma or (a >> aK+epso_I) in
      inadmissible xc a or 
	pint_domain_constraint (a,alpha,beta,xa,xb,xc,dBC,dAC,dAB);;

let one_pinwheelx xs =
  let ([alpha;beta;xc],_) = xs in
  if alpha+beta >> pi15 then true
      else 
      let (d1,d2,d3)= pinwheeledge alpha beta xc in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epso_I) in
      let domain_constraint = (xc << m 0.8) in (* 0.7 fails 0.8 works *)
      inadmissible or domain_constraint;;

(* needed for the numerical stability of L3 type L-junctions
   in 3C dimer coordinates *)

let one_ljx xs =
  let ([alpha;beta;xa],_) = xs in
  if disjoint_from_lj alpha beta then true
  else 
    try
      let (d1,d2,d3)= ljedge alpha beta xa in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epso_I) in
      let domain_constraint = (beta << m 0.9) in (* 0.8 fails *)
      inadmissible or domain_constraint
    with Unstable -> false;;

let one_tjx xs =
  let ([alpha;beta;xc],_) = xs in
  if disjoint_from_tj alpha beta then true
  else 
    try
      let (d1,d2,d3)= tjedge alpha beta xc in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epso_I) in
      let domain_constraint = (beta >>  m 1.0) in (* 1.0 works *)
      inadmissible or domain_constraint
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

let domain_scaleneto3C = 
  [(map zero2 [two*sigma;pi25;two*sigma;pi25],(true,true))];;

let dummybool = (map (fun t->(t,(true,true))));;

recursepairtoeps one_iso2C domain_iso2C;;
recursepairtoeps one_iso2C' domain_iso2C';;
recursepairtoeps one_scaleneto3C domain_scaleneto3C;;
recursepairtoeps one_pintx (dummybool pintdomain);;
recursepairtoeps one_pinwheelx (dummybool pinwheeldomain);;
recursepairtoeps one_ljx (dummybool ljdomain);;
recursepairtoeps one_tjx (dummybool tjdomain);;


(* dimer stuff *)

let dimer_constraint0 alphaB betaB xbetaB alphaD = false;;

let dimer_constraint_eps eps alphaB betaB xbetaB alphaD = 
  let nearlyt t x = (x << t + eps) && x >> t - eps in
  nearlyt pi15 betaB && 
    nearlyt sigma xbetaB &&
    nearlyt zero alphaB &&
    nearlyt zero alphaD;;

let dimer_constraint1 = dimer_constraint_eps (m 0.1);;

let dimer_constraint2 = dimer_constraint_eps (m 0.01);;

let one_dimer_eps pseudo eps dimer_constraint xs = 
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
	  dimer_constraint alphaB betaB xbetaB alphaD
  with | Unstable -> false;;

let one_dimer = one_dimer_eps false zero;;

let dimer_types = [
  ("pint",dimer_pintedge,disjoint_from_dimer_pint)  ;
  ("pinw",dimer_pinwheeledge,disjoint_from_dimer_pinwheel);
  ("lj1",dimer_lj1edge,disjoint_from_dimer_lj1);
  ("lj2",dimer_lj2edge,disjoint_from_dimer_lj2);
  ("lj3",dimer_lj3edge,disjoint_from_dimer_lj3);
  ("tj1",dimer_tj1edge,disjoint_from_dimer_tj1);
  ("tj2",dimer_tj2edge,disjoint_from_dimer_tj2);
  ("tj3",dimer_tj3edge,disjoint_from_dimer_tj3);];;

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

(* This does cases that don't approach the Kuperberg dimer. *)
(* all run on 3/10/2016: *)
let recurse0 s = recurse_dimer false zero 
  dimer_constraint0 (dimer_domain s);;
map (fun i -> recurse0 (0,i)) (0--7);;
map (fun i -> recurse0 (i,0)) (0--7);;
map (fun i -> recurse0 (4,i)) (0--7);;
map (fun i -> recurse0 (i,4)) (0--7);;
map (fun i -> recurse0 (5,i)) (0--7);;
map (fun i -> recurse0 (i,5)) (0--7);;
map (fun i -> recurse0 (6,i)) (0--7);;
map (fun i -> recurse0 (i,6)) (0--7);;

let needsmore = [1;2;3;7];;

let morecases = outer pair needsmore needsmore;;

let recurse1 pseudo s = recurse_dimer pseudo zero 
  dimer_constraint1 (dimer_domain s);;
let recurse2 pseudo s = recurse_dimer pseudo zero 
  dimer_constraint2 (dimer_domain s);;

(* This reduces dimers to 0.01 nbd of Kuperberg dimer.
   The "true" cases also explicitly exclude pseudo-dimers. *)
recurse2 false (1,1);;
recurse2 false (2,1);;
recurse2 false (3,1);;
recurse2 false (7,1);;

recurse2 false (1,2);;
recurse2 false (2,2);;
recurse2 false (3,2);;
recurse2 false (7,2);;

recurse2 false (2,3);;
recurse2 false (7,3);;

recurse2 false (2,7);;
recurse2 false (7,7);;

(* last 4 cases exclude pseudo-dimers.
   These tests fail with input pseudo=false. *)
recurse2 true (1,3);;  
recurse2 true (3,3);; 
recurse2 true (1,7);;
recurse2 true (3,7);;


(* 0.007 good, 0.006 fails, 
   so pseudo-dimer area sum is off by at most 0.007 *)
let recurseN s = recurse_dimer false (m 0.007)
  dimer_constraint0 (dimer_domain s);;
recurseN (1,3);;
recurseN (3,3);;
recurseN (1,7);;
recurseN (3,7);;
(* 0.007 good *)


(* Junk: check that the second part of 
   pseudo-dimer can be subcritical away from Kup.
(*	aABC + aADC >> two * aK - eps or *)
	  aADC >> aK or

let recurseM s = recurse_dimer zero dimer_constraint1 (dimer_domain s);;
recurseM (1,3);;
recurseM (3,3);;
recurseM (1,7);;
recurseM (3,7);;

*)

(*
ratpi 1 5;;
ratpi 2 5;;
sigma;;

"pinw,lj2";;
let ce13 = map mk_interval [(0.157041264434,0.157041273797);(0.23595946395,0.235959473313);(0.237635650368,0.237635659127);(0.,9.36267570731e-09)];;
"lj2,lj2";;
let ce33 = map mk_interval [(0.314159255996,0.314159265359);(0.314159255996,0.314159265359);(0.301264967108,0.301264975867);(0.,9.36267570731e-09)];;
"pinw,tj3";;
let ce17 = map mk_interval [(0.157040665223,0.157040674586);(0.235959772919,0.235959782281);(0.237636333545,0.237636342304);(0.,9.36267570731e-09)];;
let ce37 = map mk_interval [(0.314159255996,0.314159265359);(0.314159255996,0.314159265359);(0.301264967108,0.301264975867);(0.,9.36267570731e-09)];;

"pinw,lj2";;
let ce = map mk_interval [(0.313957621412,0.313957630775);(0.307715338265,0.307715347627);(0.416314741265,0.416314750024);(0.,9.36267570731e-09)];;
let [ce'alphaB;ce'beta;ce'xbeta;ce'alphaD] = ce;;
let ce'betaD = pi25 - ce'beta;;
let ce'xbetaD = two*sigma - ce'xbeta;;

let (d1,d2,d3)=dimer_lj2edge ce'alphaD ce'betaD ce'xbetaD;;
disjoint_from_dimer_lj2 ce'alphaD ce'betaD ce'xbetaD;;
areamin_acute d1 d2 d3;;
aK;;
aK;;

dimer_lj3edge_extended ce'alphaD ce'betaD ce'xbetaD;;
ce'alphaD;;
ce'betaD;;
ce'xbetaD;;
dimer_lj3edge;;
let [ce'alpha;ce'beta;ce'xc] = ce;;
tjedge ce'alpha ce'beta ce'xc;;
let [alpha1;beta1;xa1] = ce;;
pintedge_extended alpha1 beta1 xa1;;
two*sigma;;
areamin_acute (m 1.85) (m 1.85) (two*kappa) - aK;;
aK + epso_I;;
ratpi 2 5;;

*)


let one127 (sgnalpha,sgnbeta) xs  = 
  try
  let dACrange = mk 1.72 1.79 in
  let v = mk2C dACrange (xs,( sgnalpha, sgnbeta)) in
  if (v = None) then true
  else 
    let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = the v in 
(* (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in *)
       (a >> 127 // 100) or disjoint_I dAB dAC or
	 dAC >> dAB
  with Unstable -> false;;

let domain2C =   [map zero2 [two*sigma;ratpi 2 5;two*sigma;ratpi 2 5]];;

let recursesgn f dom = 
  map (fun t -> recursetoeps (f t) dom)
    [(true,true);(true,false);(false,true);(false,false)];;

recursesgn one127 domain2C;;

end;;

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
