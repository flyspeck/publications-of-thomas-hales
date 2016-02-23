(* 
This code is in the public domain.
Thomas Hales April 12, 2015. Nov 2015. 
*)

(*
load through init.ml.
*)


module Pent = struct


let sqrt_I x = 
  try
    Interval.sqrt_I x 
  with Failure _ -> raise Unstable;;

let mk_interval(a,b) = {low=a;high=b};;

let m r = mk_interval(r,r);;

let mk x y = mk_interval(x,y);;

let zero = m 0.0;;

let one = m 1.0;;

let two = m 2.0;;

let four = m 4.0;;

let i16 = m 16.0;;

let min_I y = {low = y.low;high = y.low};;

let max_I y = {low = y.high;high = y.high};;

let mem_I r i = (i.low <= r && r <= i.high);;

let merge_I x y = {low = min x.low y.low;high = max x.high y.high};;

(* let eps = (1.0e-10);; *)

let ( >> ) x y = x.low > y.high;;
let ( >>= ) x y = x.low >= y.high;;
let ( << ) x y = x.high < y.low;;
let ( <<= ) x y = x.high <= y.low;;


(* ******************************************************************************** *)
(* trig functions *)
(* ******************************************************************************** *)

let pi2 = pi_I /$. 2.0;;
let pi =  pi_I;;
let twopi = 2.0 *.$ pi_I;;

let ratpi i j =  
  (pi *$. float_of_int i) /$. float_of_int j;;

let pi15 = ratpi 1 5;;
let pi25 = ratpi 2 5;;
let pi35 = ratpi 3 5;;
let pi45 = ratpi 4 5;;

let rat i j =   (one *$. float_of_int i) /$. float_of_int j;;

(* let mpi i j = (ratpi i j);; *)

let kappa = cos_I (pi /$. 5.0);;
let sigma = sin_I (pi /$. 5.0);;

let ee = sigma;;
let iee = ee;;
let ff = ee /$ (2.0 *.$ kappa);;

(* critical area: *)
let aK = (1.0 +.$ kappa)*$ (3.0 *.$ (kappa *$ sigma)) /$. 2.0;;

let ups_I x1 x2 x3 = 
  two * (x1 * x2 + x2 * x3 + x3 * x1) - x1*x1 - x2*x2 - x3*x3;;

let area_I y1 y2 y3 = 
  let x1 = y1 * y1 in
  let x2 = y2 * y2 in
  let x3 = y3 * y3 in
    sqrt_I (ups_I x1 x2 x3 ) / four;;

let areamin_acute y1 y2 y3 = 
  area_I (min_I y1) (min_I y2) (min_I y3);;

acos_I (m 0.22);;

asin_I (m 0.22);;

(* angle as a function of edge lengths. *)

let iarc =
  let mn = min_I in
  let mx = max_I in
  let iarc1 a b cop = 
    acos_I (((a * a) + (b*b) - (cop*cop)) / (two * a * b)) in
  let iarc2 a b cop a' b' cop' =
    merge_I (iarc1 a b cop) (iarc1 a' b' cop') in
  fun a b cop ->
    let (a,b) = if a << b then (a,b) else (b,a) in
    let b_obtuse =  b*b >> a*a+cop*cop in
    if b_obtuse 
    then iarc2 (mn a) (mx b) (mn cop) (mx a) (mn b) (mx cop) 
    else 
      let ab_acute = b*b << a*a+cop*cop && a*a << b*b+cop*cop in
      if ab_acute 
      then iarc2 (mx a) (mx b) (mn cop) (mn a) (mn b) (mx cop)
      else iarc1 a b cop;;

iarc (m 0.1) (m 0.2) (m 0.1085659);;

let lawsines a alpha beta gamma = 
  let aa = a / sin_I alpha in
    (aa * sin_I beta, aa * sin_I gamma);;

let ilawbeta alpha a b = 
  asin_I (b * sin_I alpha / a);;

(* law of cosines, with special cases for monotonicity *)

let iloc =
  let mx = max_I in
  let mn = min_I in
  let ilocc a b costh = 
    sqrt_I(a * a + b * b - two * a * b * costh) in
  let ilocc2 a b cth a' b' cth' = merge_I (ilocc a b cth) (ilocc a' b' cth') in
    fun a b theta -> 
        let costh = cos_I theta in
	let (a,b) = if a << b then (a,b) else (b,a) in
	let b_obtuse = b*costh >> a in
	if b_obtuse 
	then ilocc2 (mn a) (mx b)  (mn costh) (mx a) (mn b)  (mx costh)
	else 
	  let ab_acute = b*costh << a && a*costh << b in
	  if ab_acute
	  then ilocc2 (mx a) (mx b) (mn costh) (mn a) (mn b) (mx costh)
	  else ilocc a b costh;;

iloc (mk_interval(1.0,1.1)) (mk_interval(1.1,1.2)) (mk_interval(1.2,1.3));;

ilawbeta (m 0.4) (m 1.1) (m 1.2);;



(* ******************************************************************************** *)

(* ell, ellx, thetax, fillout. *)
(* ******************************************************************************** *)

(*
let ell_deprecated h psi =
  let r = sqrt_I (h * h + kappa* kappa) in
  let theta = acos_I (h / r) in
    sqrt_I (one + r * r - two * r * cos_I (psi + theta));;
*)

let ell_aux h psi =
  let r = sqrt_I (h * h + kappa* kappa) in
  let theta = acos_I (h / r) in
    iloc one r (psi+theta);;

ell_aux (mk 1.1 1.2) (mk 1.3 1.4);;

let ellx  = 
  let pi310 = ratpi 3 10 in 
  fun x alpha ->
    ell_aux (iee - x) (alpha + pi310);;

(* N.B.  theta has a jump discontinuity near pm pi/5, which is an inconvenience
   for the interval calculation. We try to deal with this gracefully
   by allowing theta to exceed pi/5.
    
   
   NB. May 2, 2015: pet now puts angles in range. 
   So we now always allow theta to exceed pi/5.

   Recall that pentagon associated with thetap is the pointer, 
   and pentagon theta is the receptor.

   We assume the pentagons are in contact.
*)

let thetax =
  let pi710 = ratpi 7 10 in
  let pi1710 = ratpi 17 10 in
  fun xalpha alpha ->
    let h = xalpha - iee in
    let r = sqrt_I (h*h + kappa*kappa) in
    let phi = acos_I (h / r) in
    let psi = pi710 - alpha in
    let psi' = psi + phi in
    let elx = iloc r one psi' in
    let ely = iloc r (two * iee) (pi1710 - psi') in
    let theta' = (iarc one elx ely) - pi25 in
    let theta = alpha - theta' in
    (elx,theta,theta');;

thetax (m 0.1) (m 0.2);;
thetax (m 0.2) (m 0.19);;
thetax (mk 0.1 0.11) (mk 0.2 0.22);;
thetax (ee+ mk 0.0 0.01) (pi15 + mk 0.0 0.01);;

let ellthetax xalpha alpha sgn =  (* swap if false *)
  let (el,th,th') = thetax xalpha alpha in
  let (th,th') = if sgn then (th,th') else (th',th) in
    (el,th,th');;

(* ******************************************************************************** *)
(* pinwheel *)
(* ******************************************************************************** *)
let pinwheeledge =
  fun alpha beta xgamma ->
    let gamma = pi15 - (alpha + beta) in
    let (xalpha,xbeta) = 
      lawsines xgamma (pi25 - alpha) (pi25 - beta) (pi25 - gamma) in
    ((ellx xalpha alpha), (ellx xbeta beta), (ellx xgamma gamma));;

pinwheeledge (m 0.1) (m 0.2)  (m 0.3);;

let pintedge = 
  fun alpha beta xalpha ->
    let gamma = pi - (alpha+beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let eps' = pi35 - alpha' in
    let eps = pi - eps' in
    let delta = pi - (beta' + eps) in
    let delta' = pi - delta in
    let (w1,w2) = lawsines xalpha eps' pi25 alpha' in
    let (w3,w4) = lawsines (two * iee + w2) delta beta' eps in
    let (w5,w6) = lawsines (two * iee) delta' pi25 gamma' in
    ((ellx xalpha alpha),
     (ellx (w4 - w6) beta),
     (ellx (w1 + w3 + w5) gamma));;

(* Delta junction *)

let deltajedge =
  fun alpha beta xalpha ->
    let gamma = pi15 - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let (yalpha,ygamma) = lawsines (two * iee) (beta') (alpha') (gamma') in
    let xbeta = two * iee - (ygamma + xalpha) in
    let xgamma = two * iee - yalpha in
    ((ellx xalpha alpha'), (ellx xbeta beta'), (ellx xgamma gamma'));;

deltajedge (m 0.05) (m 0.06)  (m 0.1);;
area_I (m 1.94) (m 1.88) (m 1.93);;
deltajedge (m 0.0) (m 0.0) (m 0.0);;
pinwheeledge (m 0.0) (pi15) (two * iee);; (* same as deltajedge, up rto symmetry *)
ellx (m 0.0) (m 0.0);;
ellx (m 0.0) (pi25);;

(* L-junction Delaunay triangle edge lengths *)

let ljedge_full =
  fun alpha beta xalpha ->
  let gamma = pi35 - (alpha+beta) in
  let alphap = pi25 - alpha in
  let betap = pi25 - beta in
  let gammap = pi25 - gamma in
  let delta1 = pi - (gammap + pi25) in
  let delta2 = pi - delta1 in
  let (x3,x5) = lawsines xalpha delta2 betap alphap in
  let x1 = two*iee - x3 in
  let (xgamma,x2) = lawsines x1 pi25 delta1 gammap in
  let x6 = x5 - x2 in
    ((alpha,beta,gamma,alphap,betap,gammap,x1,x2,x3,xalpha,x5,x6),
    ((ellx xalpha alpha),(ellx x6 beta),(ellx xgamma gamma)));;    

let ljedge alpha beta xalpha =
  let (_,ll) = ljedge_full alpha beta xalpha in
  ll;;

ljedge (m 0.1) (m 0.2) (m 0.753251);;

(* T-junction edge lengths *)

let tjedge =
    fun alpha beta xgamma ->
  let gamma = pi - (alpha + beta) in
  let alphap = pi25 - alpha in
  let betap = pi25 - beta in
  let gammap = pi25 - gamma in
  let delta1 = pi - (gammap + pi25) in
  let delta2 = pi - delta1 in
  let delta3 = pi - (alphap + delta2) in
  let delta4 = pi - (betap + pi25) in
  let (x1,x2) = lawsines xgamma delta1 pi25 gammap in
  let x3 = two * iee - x1 in
  let (x4, x5) = lawsines x3 delta3 delta2 alphap in
  let x6 = two * iee - (x5 - x2) in
  let (x7,x8) = lawsines x6 pi25 betap delta4 in
  let x9 = x4 - x7 in
    ((ellx x9 alpha),(ellx x6 beta),(ellx xgamma gamma));;

tjedge (m 0.1) (m 0.2) (m 0.3);;

(* ******************************************************************************** *)
(* split domain along largest dimension *)
(* ******************************************************************************** *)

let rec maxwidth c (i,w) = function 
  | [] -> (i,w)
  | x::xs -> 
      let t = x.high -. x.low in (* floating point error ok here *)
      let c' = Pervasives.(+) c 1 in
      if t >= w then maxwidth c' (c,t) xs else maxwidth c' (i,w) xs;;
   
let testi = [mk_interval (1.0,2.0);mk_interval(2.0,3.5);mk_interval(2.3,3.2)];;
maxwidth 0 (0,0.0) testi;;

let string_of_interval x = 
  "("^string_of_float x.low ^","^string_of_float x.high^")";;
let join_semi = String.concat ";";;
let string_of_list f xs = "["^join_semi (map f xs)^"]";;

let splitlist eps xs = 
  let _ = not(xs=[]) or failwith "empty list" in
  let (i,w) = maxwidth 0 (0,0.0) xs in
  let _ = w > eps or 
    failwith ("splitlist width:" ^ string_of_float w ^ " " ^ 
		 string_of_int i ^",\n"^string_of_list string_of_interval xs) in
  let (us,v::vs) = chop_list i xs in
  let t = (v.low +. v.high) /. 2.0 in
  let v1 = mk_interval(v.low,t) in
  let v2 = mk_interval(t,v.high) in
    (us @ (v1 :: vs)),(us @ (v2 :: vs));;
	  
splitlist 0.2 testi;;

let prepost pre post f x = 
  let ys = pre x in
  let (x1,x2) = f ys in
    (post x1,post x2);;

let split eps pre post = prepost pre post (splitlist eps);;

let rec recurser eps n onef = function
  | [] -> (n,true)
  | abx :: xs -> 
      if onef abx then recurser eps (succ n) onef xs 
	  else
	    let (a1,a2) = 
	      splitlist eps abx in
	      recurser eps (succ n) onef (a1::a2::xs);;

let recursetoeps = recurser (1.0e-8) 0;;

let recursetofinish onef = 
  let wrap3 onef abx = 
    let [a;b;x] = abx in
      onef (a,b,x) in
    recursetoeps (wrap3 onef);;



(* ******************************************************************************** *)
(* Set up computational instances *)
(* ******************************************************************************** *)

(* test that all subcritical pinwheels have an edge > 1.72.
   test returns true if out of domain or ineq holds.

  *)

let area_exceeds l1 l2 l3 a = (area_I l1 l2 l3 >> a);;

let longest_exceeds l1 l2 l3 r = max l1.low (max l2.low l3.low) > r.high;;

let longgt172 =
  let i172 = rat 172 100 in
  fun l1 l2 l3 -> longest_exceeds l1 l2 l3 i172;;

let one172 disjoint_from_domain edges abx = 
  try
    let (alpha,beta,xgamma) = abx in
    disjoint_from_domain alpha beta or
      let (l1,l2,l3) = edges alpha beta xgamma in
      (longgt172 l1 l2 l3) or area_exceeds l1 l2 l3 aK
  with | Unstable -> false;;

let disjoint_from_pinwheel alpha beta =
  (beta >> alpha) or
    pi15 >> alpha + two * beta or
    alpha+beta  >> pi15 ;;

let disjoint_from_lj alpha beta =
  let ab = alpha+beta in
  pi15 >> ab or ab >> pi35;;

let disjoint_from_tj alpha beta = 
  let ab = alpha+beta in
  pi35 >> ab or ab >> pi45;;

let disjoint_from_pint alpha beta = 
  let ab = alpha+beta in
  pi35 >> ab;;

let tester suffix oner (name, disjoint_from, edges, domain) = 
  mktest ((name^suffix),fun() ->
    let once = oner disjoint_from edges in
    time (recursetofinish once) domain);;

let zero2 = merge_I zero;;
let pinwheeldomain = [[zero2 pi15;zero2 pi15;zero2 (two*sigma)]];;
let ljdomain =  [[zero2 pi25;zero2 pi25;zero2 (two*sigma)]];;
let tjdomain = [[merge_I pi15 pi25;merge_I pi15 pi25;zero2 (two*sigma)]];;
let pintdomain = [[merge_I pi15 pi25;merge_I pi15 pi25;zero2 (m 0.0605)]];;

let types3C = 
  [("pinwheel",disjoint_from_pinwheel,pinwheeledge,pinwheeldomain);
   ("lj",disjoint_from_lj,ljedge,ljdomain);
   ("tj",disjoint_from_tj,tjedge,tjdomain);
   ("pint",disjoint_from_pint,pintedge,pintdomain)];;

(* returns true, so that all subcritical pinwheels have an edge > 1.72 *)

map (tester "172" one172) types3C;;



(* next: absolute area minimization *)

let amin = rat 1237 1000;;

let one1237 disjoint_from_domain edges abx = 
  try
    let (alpha,beta,xgamma) = abx in
    disjoint_from_domain alpha beta or
    let (l1,l2,l3) = edges alpha beta xgamma in
      areamin_acute l1 l2 l3 >> amin
    with | Unstable -> false;;


map (tester "1237" one1237) types3C;;


let disjoint_from_delta alpha beta = 
  (beta >> alpha) or alpha+beta >> pi15;;

let onedeltajamin abx = 
  try
    let (alpha,beta,xalpha) = abx in
    disjoint_from_delta alpha beta or
      let (l1,l2,l3) = deltajedge alpha beta xalpha in
      areamin_acute l1 l2 l3 >> rat 15 10
  with | Unstable -> false;;

mktest ("onedeltajmin",fun() ->
	  (recursetofinish onedeltajamin) 
	    [[zero2 pi15;zero2 pi15;zero2 (two * (ee-ff))]]);;

(* non anonaly test JJZ area > 1.345 *)

let oneJJZ = 
  let m1345 = rat 1345 1000 in
  fun abx ->
    try
      let (alpha,beta,xalpha) = abx in
      disjoint_from_lj alpha beta or
	let ((_,_,gamma,alphap,betap,gammap,x1,x2,x3,_,x5,x6),
		 (l1,l2,l3)) = ljedge_full alpha beta xalpha in
	(area_exceeds l1 l2 l3 m1345) or (x6 >> iee) or (iee >> x6) 
    with | Unstable -> false;;

mktest ("oneJJZ",fun() ->
	  recursetofinish oneJJZ 
	    [[zero2 pi25;zero2 pi25;two*sigma]]);;


(* ******************************************************************************** *)
(* timing tests *)
(* ******************************************************************************** *)

(* pinwheel 1.237 benchmarks *)    
(* 1041153 cases, 51 sec. before revision *)
(* 65645 cases, 2.77 secs after revision of area *)
(* 65233 cases, 1.832 secs after installing interval arithmetic *)

(* lj 1.237 benchmarks *)
(* 346263 cases, 18 seconds *)
(* 345877 cases, 10.6 secs with interval package *)

(* tj 1.237 benchmarks *)
(* 3406713 cases old area_I function. Now 167221 cases. *)
(* 166915 cases with intervals installed *)

(* runalltest();; *)

1;;


 end;;
