(* OCaml used to generate some of the
figures in the tex file.

This is not polished code, just some
informal calculations.   The graphics were
produced on two occasions: shortly before version I
was posted to the archive, and Sept 9, 2016.

*)

#directory "/Users/namaste/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/";;
#use "obsolete_interval.ml";;
#use "init.ml";;


let eta x y z = 
  let s = (x + y + z) / two in
  let r = s * (s - x) * (s - y) * (s -z) in
  x*y*z / (four*sqrt_I (r));;

(* exploring obtuse clusters *)
let ff t =
  mk2C (mk 1.5 3.0) ([m t;m 1.2 ;m t;m 1.2],(true,true));;
let ff t =
  mk2C (mk 2.9 3.2) ([m t;m 0.0001 ;m t;m 0.0001],(true,true));;
iloc (two*kappa) (two*kappa) (pi45);;

ff 0.001;;
let fg t = 
  let Some (_,(dAB,_,_,_),(dBC,_,_,_),(dAC,_,_,_)) = ff t in
  (eta dAB dBC dAC,area_I dAB dBC dAC);;
fg 0.85;;
ff 0.2;;
ellthetax_sgn (m 0.1) (m 1.2) true;;
ellthetax_sgn (sigma) pi15 true;;

let double_slider x = 
  let theta = pi45 - two * sin_I (x / (two * kappa)) in
  let ell = sqrt_I (four*kappa*kappa + x*x) in
  let ell' = iloc ell ell theta in
  let theta2 = theta/two in
  (ell*cos_I theta2,ell*sin_I theta2,ell,area_I ell ell ell');;

double_slider (m 0.17);;

(m 180.0 / pi_I ) *(pi2 - (iarc two two (m 1.62) + iarc two two (two*kappa)));;

(* compute three pents numerically from delA coords.
   (a1,a2,thA) : (a1,a2) = center of pentagon, thA vertex angle, etc. 
   This is used to generate graphics.
*)

let arc a b c = (iarc (m a) (m b) (m c)).high;;

let delToPent3AC (dAB,dAC,dBC,thABC,thBAC,thCAB) = 
  let arcA = iarc dAC dAB dBC in
  let (a1,a2) = (zero,zero) in
  let (b1,b2) = (dAB * cos_I(arcA), dAB *  sin_I (arcA)) in
  let (c1,c2) = (dAC,zero) in
  let thA = arcA + thABC in
  let thB = arcA + pi - thBAC in
  let thC = pi + thCAB in
    (a1,a2,thA),(b1,b2,thB),(c1,c2,thC);;

let delToPent3BC (dAC,dBC,dAB,thCAB,thACB,thBCA) = 
  delToPent3AC (dAC,dBC,dAB,thCAB,thACB,thBCA);;

let delToPent3AB (dBC,dAB,dAC,thBAC,thCBA,thABC) = 
  delToPent3AC (dBC,dAB,dAC,thBAC,thCBA,thABC) ;;
  

let degofrad x = x *. 180.0 /. pi.high;;

let deg3 (x,y,z) = (x,y,m (degofrad z.low));;

let formatpent3 ((a1,a2,a3),(b1,b2,b3),(c1,c2,c3)) = 
  Printf.sprintf "{%.2f,%.2f,%.2f},{%.2f,%.2f,%.2f},{%.2f,%.2f,%.2f}" a1 a2 a3 b1 b2 b3 c1 c2 c3;;

let formatpent3deg ((a1,a2,a3),(b1,b2,b3),(c1,c2,c3)) = 
  Printf.sprintf "{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}" a1 a2 (degofrad a3) b1 b2 (degofrad b3) c1 c2 (degofrad c3);;

let formatpent3deg ((a1,a2,a3),(b1,b2,b3),(c1,c2,c3)) = 
  Printf.sprintf "{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}{%.2f}" 
  a1.low a2.low (degofrad a3.low) 
    b1.low b2.low (degofrad b3.low) 
    c1.low c2.low (degofrad c3.low);;



(* pinwheel *)

let pinwheeledge_ext =
  fun alpha beta xgamma ->
    let gamma = pi15 - (alpha + beta) in
    (* N.B. unusual ordering comes from Figure in article *)
    let (xalpha,xbeta) = 
      lawsines xgamma (pi25 - alpha) (pi25 - beta) (pi25 - gamma) in
    ((thetax xalpha alpha), 
     (thetax xbeta beta), 
     (thetax xgamma gamma));;

pinwheeledge_ext zero zero (m 0.16246);;

let shared_pinwheeledge_ext alpha beta xbeta = 
  let gamma = pi15 - (alpha+beta) in
  let dAB,dBC,dAC = pinwheeledge_ext gamma alpha xbeta in
  dBC,dAC,dAB;;

let ljedge_ext =
  fun alpha beta xalpha ->
  let gamma = pi35 - (alpha+beta) in
  let alpha' = pi25 - alpha in
  let beta' = pi25 - beta in
  let gamma' = pi25 - gamma in
  let delta' = pi - (alpha' + beta') in
  let (s1,b1) = lawsines xalpha delta' beta' alpha' in
  let s2 = two*sigma - s1 in
  let (b2,xgamma) = lawsines s2 pi25 gamma' delta' in
  let xbeta = b1 - b2 in
    ((thetax xalpha alpha),
     (thetax xbeta beta),
     (thetax xgamma gamma));;

let shared_lj2edge_ext alpha beta xbeta =
  let ((dAC,thCAB,thACB),(dBC,thBCA,thCBA),(dAB,thBAC,thABC)) = ljedge_ext beta alpha xbeta in
(dBC,thBCA,thCBA),(dAC,thCAB,thACB),(dAB,thABC,thBAC);;
  

shared_pinwheeledge_ext (m 0.4) (m 0.2) (m 0.3);;
shared_lj2edge_ext (m 0.4) (m 0.2) (m 0.3);;
shared_lj2edge_ext (m 0.1) (pi25 - (m 0.2)) (two*sigma -(m 0.3));;

let format_shared_pinwheelAC alpha beta xbeta = 
  let (dBC,_,_),(dAC,thCAB,_),(dAB,thABC,thBAC) = shared_pinwheeledge_ext alpha beta xbeta in
  let x = delToPent3AC (dAB,dAC,dBC,thABC,thBAC,thCAB) in
  formatpent3deg x;;

let format_shared_lj2edgeAC alpha beta xbeta = 
  let (dBC,_,_),(dAC,thCAB,_),(dAB,thABC,thBAC) = shared_lj2edge_ext alpha beta xbeta in
  let x = delToPent3AC (dAB,dAC,dBC,thABC,thBAC,thCAB) in
  formatpent3deg x;;

let format_ljedgeAC alpha beta xbeta = 
  let (dBC,thCBA,thBCA),(dAC,thACB,thCAB),(dAB,thABC,thBAC) 
			      = ljedge_ext alpha beta xbeta in
  let x = delToPent3AC (dAB,dAC,dBC,thABC,thBAC,thCAB) in
  formatpent3deg x;;

shared_pinwheeledge_ext (m 0.157) (m 0.2359) (m 0.2376);;
shared_lj2edge_ext zero (pi25 - (m 0.2)) (two*sigma -(m 0.3));;


format_shared_pinwheelAC (m 0.157) (m 0.2359) (m 0.2376);;
format_shared_lj2edgeAC zero (pi25-(m 0.2359)) (two*sigma  - (m 0.2376));;
let (a,b,c) = shared_lj2edge zero (pi25-(m 0.2359)) (two*sigma - (m 0.2376)) in
let (a',b',c') = shared_pinwheeledge (m 0.157) (m 0.2359) (m 0.2376) in
area_I a b c + area_I a' b' c' - two*acrit;;


let format_pinwheelAC alpha beta xgamma = 
  let (dBC,_,_),(dAC,thCAB,_),(dAB,thABC,thBAC) = pinwheeledge_ext alpha beta xgamma in
  let x = delToPent3AC (dAB,dAC,dBC,thABC,thBAC,thCAB) in
  formatpent3deg x;;

let format_pinwheelAB alpha beta xgamma = 
  let (dBC,thBCA,thCBA),(dAC,thCAB,thACB),(dAB,thABC,thBAC) = 
    pinwheeledge_ext alpha beta xgamma in
  let x = delToPent3AB (dBC,dAB,dAC,thBCA,thCBA,thABC) in
  formatpent3deg x;;



sigma - m 0.35;;
format_pinwheelAB zero zero sigma;;
format_pinwheelAB zero zero (sigma - m 0.25);;
format_pinwheelAB zero zero (sigma + m 0.25);;

format_pinwheelAB zero zero (zero);;
format_pinwheelAB zero zero sigma;;
format_pinwheelAB zero zero (two*sigma - (m 0.35));;
format_pinwheelAB zero zero (zero);;

format_pinwheelAB (m 0.1) (m 0.1) (sigma);;
format_shared_lj2edgeAC zero (pi25-(m 0.2359)) (two*sigma  - (m 0.2376));;

(* subcritical *)
format_ljedgeAC (ratpi 3 10) zero (m 0.68);;
let ((a,_,_),(b,_,_),(c,_,_)) = ljedge_ext (ratpi 3 10) zero (m 0.68) in
area_I a b c;;

let deg23 (a,b,c) = (a,degofrad b.low,degofrad c.low);;
deg23 (thetax (m 0.02) (m 0.02));;
deg23 (thetax (m 0.3) (m 0.3));;

(* fig:extended *)
deg23 (ethetax (m 0.8) (pi25 - m 0.25));;
deg23 (ethetax (m 0.8) (pi25 - m 0.0));;
deg23 (ethetax (m 0.8) (pi25 + m 0.25));;
(ethetax (m 0.8) (pi25 - m 0.25));;
let threex f (a,b,c) = f a b c;;
threex Pet.pet (thetax (m 0.8) (pi25 - m 0.25));;
threex Pet.pet (thetax sigma (m 0.1));;
deg23 (thetax sigma (m 0.1));;

(* fig:banana2 *)
let Some a = (theta_banana (m 1.82) (m 0.1)) in 
degofrad a.high;;
let Some a = theta_banana (m 1.82) (m (-. 0.1)) in
degofrad a.high;;
degofrad 0.1;;

(* fig:p-triangle *)
format_pinwheelAC (m 0.1) (m 0.1) (m 0.3);;


pi25;;
let (a,b,c) = pinwheeledge zero zero (m 0.35) in
area_I a b c;;
let (a,b,c) = pinwheeledge zero zero (m 0.35) in
let (a',b',c') = pinwheeledge zero zero (two*sigma - (m 0.35)) in
area_I a b c + area_I a' b' c' - two*acrit;;

kappa;;
acrit;;
(pinwheeledge pi115 pi115 zero);;
let pi115 = ratpi 1 15;;
format_pinwheelAB (pi115) pi115 (m 0.18);;
pinwheeledge pi115 pi115 (m 0.18);;


1;;
(* two pentagon. First is (a1,a2,thA). Compute (b1,b2,thB).
*)

let pointerAtoBf k (a1,a2,thA) (xalpha,alpha) =
  let (el,theta,theta') = thetax (m xalpha) (m alpha) in
  let l x = x.lo in
  let (el,theta,theta') = (l el,l theta,l theta') in
  let barg = thA -. theta' +. (2.0 *. pi /. 5.0) *. float_of_int k in
  let (b1,b2) = (a1 +. el *. cos barg, a2 +. el *. sin barg) in
  let thB = pi -. alpha +. thA in
    (b1,b2,thB);;

let receptorAtoBf (a1,a2,thA) (xalpha,alpha) =
  let (el,theta,theta') = thetax (m xalpha) (m alpha) in
  let l x = x.lo in
  let (el,theta,theta') = (l el,l theta,l theta') in
  let barg = thA +. theta in
  let (b1,b2) = (a1 +. el *. cos barg, a2 +. el *. sin barg) in
  let thB = pi +. alpha +. thA in
    (b1,b2,thB);;

let f3 (b1,b2,b3) = Printf.sprintf "{%.2f,%.2f,%.2f}" b1 b2 b3;;
 (deg3 (pointerAtoBf 3 (0.0,0.0,pi /. 2.0 ) (0.0,1.)));;

deg3 (pointerAtoBf 3 (0.0,0.0, 0.0 -. pi /. 2.0) (0.4,1.));;
f3 (pointerAtoBf 4 (0.0,0.0,0.0 -. pi/. 2.0) (0.4,0.0));;
f3 (pointerAtoBf 0 (0.0,0.0,0.0 -. pi/. 2.0) (0.4,0.0));;
deg3 (pointerAtoBf 0 (0.0,0.0,0.0) (0.3,0.2));;

 (receptorAtoBf (0.0,0.0,0.1) (0.4,1.));;

