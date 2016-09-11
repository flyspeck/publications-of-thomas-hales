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

let m1 = m 1.72;;

let m18 = m 1.8;;

let tk = two*kappa;;


let _ = int 2 * kappa_ * kappa_;;

let c172_ = sqrt_I (int 4 * kappa_ * kappa_ + sigma_ * sigma_);;

let lemma_21 = area_I (m 2.1) (tk) (tk) - acrit;;

let lemma_right = kappa * sqrt_I (int 8) - m 2.1;;

let lemma_right' = kappa * sqrt_I (int 8);;

(* 1.72 is nearly optimal *)

let optimal172 = 
  let  pi115 = ratpi 1 15 in
  let (d1,d2,d3) = pinwheeledge pi115 pi115 (m 0.18) in
  (d1,d2,d3,area_I d1 d2 d3 - acrit);;

let calc_pseudo3 = 
  area_I m1 m18 m18 - (acrit + epsN_I);;

let pseudo_dimer_area_table = 
  area_I m18 m18 m18 - (acrit + m 0.112),
  area_I m18 m18 m1 - (acrit + m 0.069),
  area_I m18 m1 m1 - (acrit + int 3 * epsM_I),
  area_I m18 m18 (tk) - (acrit + epsM_I),
  area_I (kappa*sqrt_I(int 8)) (tk) m1 - (acrit + epsN_I);;

let t2b_nonobtuse = 
  let ks = kappa * sqrt_I (int 8) in
  area_I ks m1 (tk) - (acrit+epsN_I),
  area_I ks m1 m1 - (acrit + two*epsN_I),
  area_I ks m1 (tk) - (acrit+two*epsM_I);;

let lemma_m2b = 
  area_I m18 m18 m1 - (acrit + int 3 * epsM_I);;

let lemma_3m2 = 
  area_I m18 m18 m18 - (acrit + int 3 * epsM_I + epsN_I);;

let lemma_Nb = 
  area_I (tk) m1 (kappa*sqrt_I (int 8)) - (acrit+epsN_I);;

let areta_I d1 d2 h = 
  let _ = not (d2 << d1) or failwith "areta_I:reorder d1 d2" in
  let _ = not (d1 << tk) or failwith "areta_I:small d1" in
  let theta1 = iarc h h d1 in
  let theta2 = iarc h h d2 in
  let (thetaA,thetaB)= (theta1+theta2,theta1-theta2) in
  let d3A = (iloc h h thetaA) in
  let d3B = (iloc h h thetaB) in
  let _ = disjoint_I d3A d3B or failwith "areta_I:disjoint" in
  let d3 = if d3A >> d3B then d3A else d3B in
  let testh = iarc h h d1 + iarc h h (tk) in
  let test_lemma_areta = testh >> pi or d2 << two*h*sin_I(testh / two) or
    failwith "areta_I:disjont" in
  area_I d1 d2 d3;;
  
let lemma_t2b = 
  areta_I (tk) (kappa*sqrt_I (int 8)) (two) - (acrit + two*epsN_I);;
  

(* obtuse calculations *)

let obtuse_case1 = 
  (kappa * sqrt_I (int 12),
   iarc two two m1 + iarc two two m1
  );;


let obtuse_case1_cocircular = 
  let theta2 = two*iarc two two (tk) in
  let x2 = four*sin_I (theta2/two) in
  let theta3 = (int 3)*iarc two two (tk) in
  let x3 = four*sin_I (theta3/two) in
  let outeta2 = area_I tk tk x2 + area_I tk x2 x3 > (two*acrit + four*epsN_I) in
  let ctheta = (m1 - (tk))/(four*kappa) in
  let theta = acos_I ctheta in
  let arean'1 = tk*sin_I theta * (m1 + tk)/two in
  let outn'1 = arean'1 > two*acrit + epsN_I in
  let outn'23 = tk*m1 > two*acrit + int 3*epsN_I in
  let outn'4 = m1*m1 > two*acrit + four*epsN_I in
  (outeta2,outn'1,outn'23,outn'4);;

let ts = kappa*sqrt_I (int 8) ;;


let obtuse_case1_d4 = 
  let h = sqrt_I (m1*m1+tk*tk) in
  let c i = two*acrit + (int i)*epsN_I in
  let outn'1 = area_I tk tk ts + area_I ts m1 tk > c 1 in
  let outn'2 = area_I tk tk ts + area_I ts m1 m1 > c 2 in
  let outn'2a= area_I tk tk h + area_I h tk m1 > c 2 in
  let outn'3 = area_I tk m1 h + area_I h m1 m1 > c 3 in
  outn'1,outn'2,outn'2a,outn'3;;

let obtuse_case2 = 
  let o1 = area_I tk ts ts > m 1.73 in
  let o2 = area_I m1 ts ts > m 1.73 + epsN_I in
  let o3 = areta_I tk tk (m 1.7) > m 1.08 in
  let o4 = areta_I tk m1 (m 1.7) > m 1.08 + two* epsN_I in
  let o5 = m 1.73 + two*m 1.08 > (int 3)*acrit in
  let o6 = areta_I tk tk two > m 0.968 in
  let m17 = m 1.7 in
  let o7 = iarc m17 m17 tk + iarc m17 m17 ts < pi in
  let o8 = iarc m17 m17 ts * two < pi in
  let o9 = tk*sqrt_I(m17*m17-kappa*kappa) > m 2.41 in
  let o10= two*(m 0.968) + m 2.41 > (int 3)*acrit + (int  5)*epsN_I in
  (o1,o2,o3,o4,o5,o6,o7,o8,o9,o10);;

let obtuse_case3 = 
  let o1 = area_I ts ts ts > m 2.2668 in
  let o2 = areta_I ts ts (m 1.7) > m 2.6 in
  let crit = four*acrit + (int 6)*epsN_I in
  let o3 = m 2.2668 + (int 3)*m 1.08 > crit in
  let o4 = m 2.6 + int 3 * m 0.968 > crit in
  (o1,o2,o3,o4);;

let obtuse_case5 = 
  let o1 = areta_I ts ts two > m 2.45 in
  let o2 = m 2.45 + two*m 0.968 > ((int 3)*acrit + (int 5)*epsN_I) in
  o1,o2;;

(* obtuse_case4 *)

let one_ff x = 
  area_I tk tk x + areta_I tk x two > (two*acrit + four*epsN_I);;

let _ = 
  area_I tk tk  (m 2.96) + areta_I tk (m 2.6) two - (two*acrit+four*epsN_I);;

setify (map (fun i -> ff (mk (ts + i//100).low (ts + succ i //100).high))
(0--64));;

(* end obtuse_case4 *)

let lemma_163 = 
  let o1 = pi15 + acos_I (m 1.63 - kappa) > pi25 - m 0.021 in
  let o2 = pi15 - acos_I (m 1.63 - kappa) < m 0.021 in
  o1,o2;;

let lemma_nonobtuse_2 = 
  let o1 = amin + area_I (m 1.8) (m 1.8) (m 1.72) - two*epsM_I > two*acrit in
  o1;;

let lemma_pseudo_area3_prep = 
  two*amin + m 1.8 * kappa > (int 3)*acrit +epsM_I;;

let lemma_0605 = 
  two*sigma*(one/(sin_I(pi25))-one);;

let lemma_pseudo_area1_prep = 
  amin + area_I m18 m18 (m 1.72) > two*acrit;;

let lemma_calc_large_prep =
  amin + m 1.8 * kappa > two*acrit + epsM_I;;

