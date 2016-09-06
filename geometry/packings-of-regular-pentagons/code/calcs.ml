(* This file contains constants computed for
   in the article *)

(*
# (5.0 -. sqrt(5.0)) /. 3.0;;
- : float = 0.921310674166736732
# (1.0 +. sqrt(5.0))/. 4.0;;
- : float = 0.809016994374947451
# let pi = 4.0 *. atan(1.0);;
val pi : float = 3.14159265358979312
# let kappa = cos(pi /. 5.0);;
val kappa : float = 0.809016994374947451
# let sigma = sin(pi/. 5.0);;
val sigma : float = 0.587785252292473137
# let aK = 3.0 *. sigma *. kappa *. (1.0 +. kappa) /. 2.0;;
val aK : float = 1.29035805044172536
# let areaP = 5.0 *. sigma *. kappa;;
val areaP : float = 2.37764129073788411
# areaP /. (2.0 *. aK);;
- : float = 0.921310674166736732
# let a0 = 1.237;;
val a0 : float = 1.237
# let epsN = aK -. a0;;
val epsN : float = 0.0533580504417252577
# 2.0 *. kappa *. kappa;;
- : float = 1.30901699437494745
areaP /. (2.0 *. a0);;
- : float = 0.96105145138960546
# sqrt(4.0*. kappa*. kappa +. sigma *. sigma);;
- : float = 1.72148932368528529
*)


let kappa_ = (one + sqrt_I (int 5))/ int 4;;

let pi_ = int 4 * atan_I one;;

let kappa_ = cos_I (pi / int 5);;

let sigma_ = sin_I (pi / int 5);;

let aK_ = int 3 * sigma_ * kappa_ * (one + kappa_) / int 2;;

let areaP_ = int 5 * sigma_ * kappa_ ;;

let density_ = 
  let five = int 5 in
  (five - sqrt_I five) / int 3;;

let density_ = areaP_ / (int 2 * aK_);;

let a0_ = 1237 // 1000;;

let epsN_ = aK_ - a0_ + zero(* *);;

let _ = int 2 * kappa_ * kappa_;;

let c172_ = sqrt_I (int 4 * kappa_ * kappa_ + sigma_ * sigma_);;

let lemma_21 = area_I (m 2.1) (two*kappa) (two*kappa) - acrit;;

let lemma_right = kappa * sqrt_I (int 8) - m 2.1;;

let lemma_right' = kappa * sqrt_I (int 8);;

(* 1.72 is nearly optimal *)

let optimal172 = 
  let  pi115 = ratpi 1 15 in
  let (d1,d2,d3) = pinwheeledge pi115 pi115 (m 0.18) in
  (d1,d2,d3,area_I d1 d2 d3 - acrit);;

let calc_pseudo3 = 
  area_I (m 1.72) (m 1.8) (m 1.8) - (acrit + epsN_I);;

let pseudo_dimer_area_table = 
  area_I (m 1.8) (m 1.8) (m 1.8) - (acrit + m 0.112),
  area_I (m 1.8) (m 1.8) (m 1.72) - (acrit + m 0.069),
  area_I (m 1.8) (m 1.72) (m 1.72) - (acrit + int 3 * epsM_I),
  area_I (m 1.8) (m 1.8) (two*kappa) - (acrit + epsM_I),
  area_I (kappa*sqrt_I(int 8)) (two*kappa) (m 1.72) - (acrit + epsN_I);;

let t2b_nonobtuse = 
  let ks = kappa * sqrt_I (int 8) in
  area_I ks (m 1.72) (two*kappa) - (acrit+epsN_I),
  area_I ks (m 1.72) (m 1.72) - (acrit + two*epsN_I),
  area_I ks (m 1.72) (two*kappa) - (acrit+two*epsM_I);;

let lemma_m2b = 
  area_I (m 1.8) (m 1.8) (m 1.72) - (acrit + int 3 * epsM_I);;

let lemma_3m2 = 
  area_I (m 1.8) (m 1.8) (m 1.8) - (acrit + int 3 * epsM_I + epsN_I);;

let lemma_Nb = 
  area_I (two*kappa) (m 1.72) (kappa*sqrt_I (int 8)) - (acrit+epsN_I);;

let areta_I d1 d2 h = 
  let _ = not (d2 << d1) or failwith "areta_I:reorder d1 d2" in
  let _ = not (d1 << two*kappa) or failwith "areta_I:small d1" in
  let theta1 = iarc h h d1 in
  let theta2 = iarc h h d2 in
  let (thetaA,thetaB)= (theta1+theta2,theta1-theta2) in
  let d3A = (iloc h h thetaA) in
  let d3B = (iloc h h thetaB) in
  let _ = disjoint_I d3A d3B or failwith "areta_I:disjoint" in
  let d3 = if d3A >> d3B then d3A else d3B in
  let testh = iarc h h d1 + iarc h h (two*kappa) in
  let test_lemma_areta = testh >> pi or d2 << two*h*sin_I(testh / two) or
    failwith "areta_I:disjont" in
  area_I d1 d2 d3;;
  
let lemma_t2b = 
  areta_I (two*kappa) (kappa*sqrt_I (int 8)) (two) - (acrit + two*epsN_I);;
  
let lemma_0605 = 
  two*sigma*(one/(sin_I(pi25))-one);;

let lemma_calc = 
  amin + area_I (m 1.8) (m 1.8) (m 1.7) > two*acrit;;
