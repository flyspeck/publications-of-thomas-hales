(* 
This code is in the public domain.
Thomas Hales April 12, 2015. Nov 2015. 
*)

(*
load through init.ml.
*)


module Pent = struct


let try_do f = 
  let rec try_dof = function
    | [] -> []
    | (x::t) ->
      try let y = f x in y :: try_dof t
      with 
      |  Failure s  -> report s; [] 
      | _ -> [] in 
  try_dof;;

let rec selectsome = function
  | [] -> []
  | None::xs -> selectsome xs
  | Some x::xs -> x:: selectsome xs;;

let the x = match x with
  | None -> failwith "the"
  | Some t -> t;;

let issome x = match x with
  | None -> false
  | _ -> true;;

let isnone x = not(issome x);;

(* We rarely use integer arithmetic. *)
let succ n = Pervasives.(+) n 1;;
let pred n = Pervasives.(-) n 1;;

let ( +~ ) = Pervasives.( + );;
let ( *~) = Pervasives.( * );;
let ( -~ ) = Pervasives.( - );;

let ( >. ) (x:float) (y:float) = x > y;;
let ( <. ) (x:float) (y:float) = x < y;;

let sqrt = Pervasives.sqrt;;
let sin = Pervasives.sin;;
let cos = Pervasives.cos;;

(* prioritize interval operations *)
let ( + ) = ( +$ );;
let ( - ) = ( -$ );;
let ( * ) = ( *$ );;
let ( ~- ) = ( ~-$ );;


(*
let rec outer f xs =
  function
  | [] -> []
  | y::ys -> map (fun t -> f t y) xs @ outer f xs ys;;


let rec allpair acc f l1 l2 = 
    match l1 with 
      [] ->  acc
    | (h1::t1) ->  allpair ((List.map (f h1) l2) @ acc) f t1 l2;;
*)

let outer = Lib.allpairs;; 

let pair x y = x,y;;

let outerpair = Lib.allpairs pair;;

let outertriple k1 k2 k3 = 
  let k123 = outer pair k1 (outer pair k2 k3) in
    map (fun (i,(j,k)) -> (i,j,k)) k123;;

outer pair [0;1;2] [3;4];;

let sqrt_I x = 
  try
    Interval.sqrt_I x 
  with Failure _ -> raise Unstable;;

let acos_I x = 
  try
    Interval.acos_I x
  with Failure _ -> raise Unstable;;

let mk_interval(a,b) = {low=a;high=b};;

let m r = mk_interval(r,r);;

let mk x y = mk_interval(x,y);;


let zero = m 0.0;;

let one = m 1.0;;

let two = m 2.0;;

let four = m 4.0;;

let i16 = m 16.0;;

let eps_I = mk (- 1.0e-8) (1.0e-8);;

let merge_I x y = {low = min x.low y.low;high = max x.high y.high};;

let inter_I x y =
  let t = {low = max x.low y.low; high = min x.high y.high} in
  let _ = t.low <= t.high or failwith "inter_I void" in
  t;;

let min_I y = {low = y.low;high = y.low};;

let max_I y = {low = y.high;high = y.high};;

let min2_I x y = min_I (merge_I x y);;

let max2_I x y = max_I (merge_I x y);;

let max3_I x y z = max2_I (max2_I x y) z;;

let mem_I r i = (i.low <= r && r <= i.high);;

let width_I x = max_I x - min_I x;;



width_I eps_I;;

(* let eps = (1.0e-10);; *)

let ( >> ) x y = x.low >. y.high;;
let ( >>= ) x y = x.low >= y.high;;
let ( << ) x y = x.high <. y.low;;
let ( <<= ) x y = x.high <= y.low;;

let ( >>. ) x y = x.low >. y;;
let ( <<. ) x y = x.high <. y;;

let disjoint_I x y = (x >> y) or (y >> x);;

let meet_I x y = not (disjoint_I x y);;

let abs_I x = if (x.low >= 0.0) then x
  else if (x.high <= 0.0) then (- x)
  else mk 0.0 (max x.high (~-. (x.low)));;

abs_I (mk (~-. 0.3) (~-. 0.2));;


let (/) x y = 
  if disjoint_I eps_I y then x /$ y else raise Unstable;;


(*
acos_I (mk 0.5 1.1);;
thetax (m 0.1) (m 0.2);;
sqrt_I (m (- 0.1));;
inter_I (mk 1.0 2.0) (mk 2.1 3.0);;

meet_I (mk 1.0 2.0) (mk 0.0 0.5);;
*)

(* ******************************************************************************** *)
(* trig functions *)
(* ******************************************************************************** *)

let ratpi i j =  
  (pi_I *$. float_of_int i) /$. float_of_int j;;

let pi =  pi_I;;

let pi2 = ratpi 1 2;;
let twopi = ratpi 2 1;;

let pi15 = ratpi 1 5;;
let pi25 = ratpi 2 5;;
let pi35 = ratpi 3 5;;
let pi45 = ratpi 4 5;;
let pi65 = ratpi 6 5;;

let pi110 = ratpi 1 10;;
let pi310 = ratpi 3 10;;
let pi710 = ratpi 7 10;;



let rat i j =   (one *$. float_of_int i) /$. float_of_int j;;

let int i = (one *$. float_of_int i);;

let ( // ) = rat;;

(* let mpi i j = (ratpi i j);; *)

let kappa = cos_I (pi /$. 5.0);;
let sigma = sin_I (pi /$. 5.0);;

(* deprecated *)
(* let ee = sigma;;
let iee = sigma;; *)


(* critical area: *)
let aK = (1.0 +.$ kappa)*$ (3.0 *.$ (kappa *$ sigma)) /$. 2.0;;

(* let a0 =  1237 // 1000;; *)
let amin =  1237 // 1000;;

let epso_I = aK - amin;;

let epso'_I = 7 // 1000;;

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

let ell_aux h psi =
  let r = sqrt_I (h * h + kappa* kappa) in
  let theta = acos_I (h / r) in
    iloc one r (psi+theta);;

ell_aux (mk 1.1 1.2) (mk 1.3 1.4);;

let ellx  = 
  fun x alpha ->
    ell_aux (sigma - x) (alpha + pi310);;

(* N.B.  theta has a jump discontinuity near pm pi/5, which is an inconvenience
   for the interval calculation. We try to deal with this gracefully
   by allowing theta to exceed pi/5.
    
   
   NB. May 2, 2015: pet now puts angles in range. 
   So we now always allow theta to exceed pi/5.

   Recall that pentagon associated with thetap is the pointer, 
   and pentagon theta is the receptor.

   We assume the pentagons are in contact.
*)

(* rewritten 2/28/2016 
let thetax =
  let pi710 = ratpi 7 10 in
  let pi1710 = ratpi 17 10 in
  fun xalpha alpha ->
    let h = xalpha - sigma in
    let r = sqrt_I (h*h + kappa*kappa) in
    let phi = acos_I (h / r) in
    let psi = pi710 - alpha in
    let psi' = psi + phi in
    let elx = iloc r one psi' in
    let ely = iloc r (two * sigma) (pi1710 - psi') in
    let theta' = (iarc one elx ely) - pi25 in
    let theta = alpha - theta' in
    (elx,theta,theta');;
*)

let thetax =
  fun xalpha alpha ->
    let h = xalpha - sigma in
    let r = sqrt_I (h*h + kappa*kappa) in
    let phi' = asin_I (h / r) in
    let delta = pi65 - (alpha + phi') in
    let elx = iloc r one delta in
    let ely = iloc r (two * sigma) (delta  - pi310) in
    let theta' = pi25 - (iarc one elx ely) in
    let theta = alpha - theta' in
    (elx,theta,theta');;

(* merged version on enlarged domain *)

let shifted_thetax xalpha alpha = 
  let (elx,theta,theta') = thetax (two*sigma - xalpha) (alpha - pi25) in
  elx,(theta'+ pi25),theta;;


let mergefn f0 f1 m cutax  = 
  fun x ->
    if x << cutax then f0 x
    else if x >> cutax then f1 x
    else 
      let x0 = merge_I (min_I x) cutax in
      let x1 = merge_I (max_I x) cutax in
      m (f0 x0) (f1 x1);;

let ethetax xalpha alpha = 
  if alpha << pi25 then thetax xalpha alpha
  else if alpha >> pi25 then shifted_thetax xalpha alpha
  else
    mergefn (thetax xalpha) (shifted_thetax xalpha)
    (fun (x1,y1,z1) (x2,y2,z2) -> merge_I x1 x2,merge_I y1 y2, merge_I z1 z2) 
      (pi25) alpha;;

ethetax (m 0.1) pi25;;
ethetax (m 0.5) pi25;;
thetax (m 0.1) (m 0.2);;
thetax (m 0.2) (m 0.19);;
thetax (mk 0.1 0.11) (mk 0.2 0.22);;
thetax (sigma+ mk 0.0 0.01) (pi15 + mk 0.0 0.01);;


(* monotonicity *)

  let theta'mono xa alpha = 
    let (_,_,th1) = ethetax (min_I xa) (min_I alpha) in
    let (_,_,th2) = ethetax (max_I xa) (max_I alpha) in
    merge_I th1 th2;;
  
  let thetamono xa alpha =
    let (_,th1,_) = ethetax (min_I xa) (max_I alpha) in
    let (_,th2,_) = ethetax (max_I xa) (min_I alpha) in
    merge_I th1 th2;;

  let ellxmono_r xa alpha =  (* restricted domain 0 <= alpha <= pi25 *)
    let ellmax x = 
      let h = x - sigma in 
      let r = sqrt_I (kappa*kappa+ h* h) in
      let alpham = pi15 - asin_I (h / r) in
      if (meet_I alpham alpha) 
      then ellx x alpham
      else max2_I (ellx x (min_I alpha)) (ellx x (max_I alpha)) in
    let ellM = max2_I (ellmax (min_I xa)) (ellmax (max_I xa)) in
    let ellmin alp = 
      let xm = sigma + sin_I (alp - pi15) in
      if (meet_I xm xa) 
      then ellx xm alp
      else min2_I (ellx (min_I xa) alp) (ellx (max_I xa) alp) in
    let ellm = min2_I (ellmin (min_I alpha)) (ellmin (max_I alpha)) in
    merge_I ellm ellM;;

(* exploits symmery alpha-> pi25 - alpha, xa -> 2sigma-xa of ellx on
   unextended domain.
    So when alpha > pi25,  
   (xa,alpha)-> (2sigma-xa,alpha-pi25) -> (xa,pi45-alpha) *)

  let ellxmono xa alpha =  (* unrestricted domain alpha <= pi45 *)
    let alpha2 = 
      if alpha << pi25 then alpha
      else if alpha >> pi25 then (pi45-alpha)
      else (merge_I (min2_I alpha (pi45-alpha)) pi25) in
    ellxmono_r xa alpha2;;

  let ellxmono_merge =0;;

  let ellthetax xa alpha = 
    (ellxmono xa alpha,thetamono xa alpha,theta'mono xa alpha);;

ellthetax (m 0.1) pi25;;
ethetax (m 0.1) pi25;;

let ellthetax_sgn xalpha alpha sgn =  (* swap if false *)
  let (el,th,th') = ellthetax xalpha alpha in
  if sgn then (el,th,th') else (el,th',th);;

ellthetax_sgn (mk 0.2 0.25) (mk 0.3 0.35) false;;    
ellxmono (mk 0.2 0.25) (mk 0.3 0.35);;

(* ******************************************************************************** *)
(* 2C coordinates *)
(* ******************************************************************************** *)

(* start of mk_isosceles *)
  let hasint x = 
    let t = x - m (floor x.low) in
    mem_I 0.0 t or mem_I 1.0 t;;

(* gets the integer in x, raises unstable if solution not unique *)

  let getint x = 
    let k = m (floor x.low) in
    let k' = if disjoint_I k x then k+one else k in
    let _ = disjoint_I (k'+one) x or raise Unstable in
    if meet_I k' x then Some k' else None;;


getint (mk 1.1 1.3);;

hasint (mk  (-0.9) (-0.8));;

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

(* Constructs all the key variables on a "2C" P-triangle.
   B is the pentagon that touches both others.
   alpha variables between A and B
   beta variables between B and C.
   when signs are true, then B is the pointer.
   dACrange give a priori bounds on the length of dAC. 

   Can be used on the extended range with alpha beta up to 4pi/5.
   In that case, take both signs to be true.
   Get pointers both ways,
   when alpha up to 2pi/5, then B is the pointer,
   for alpha larger than 2pi/5 A becomes the pointer.
   Similar for beta.

   Extended range is equivalent to taking alpha beta up to 2pi/5 and both signs.
   We should deprecate the signed version.

*)

(* fillout2C takes coordinates on two edges (at pentagon B) and generates
   full coordinate system  
   th... angles are only defined up to a multiple of 2pi/5.

   The output is ordered as follows.
   a= area comes first.
   The next output echoes the input (dAB,thABC,thBAC)
   The next output echoes the input (dBC,thCBA,thBCA)
   The last output is data along the remaining edge.  Its first angle thACB is at the
   vertex of the first input angle thABC.
*)


(* ******************************************************************************** *)
(* pinwheel *)
(* ******************************************************************************** *)
let pinwheeledge =
  fun alpha beta xgamma ->
    let gamma = pi15 - (alpha + beta) in
    let (xalpha,xbeta) = 
      lawsines xgamma (pi25 - alpha) (pi25 - beta) (pi25 - gamma) in
    ((ellxmono xalpha alpha), 
     (ellxmono xbeta beta), 
     (ellxmono xgamma gamma));;

pinwheeledge (m 0.1) (m 0.2)  (m 0.3);;

let pintedge_extended = 
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
    let (w3,w4) = lawsines (two * sigma + w2) delta beta' eps in
    let (w5,w6) = lawsines (two * sigma) delta' pi25 gamma' in
    ((ellxmono xalpha alpha),
     (ellxmono (w4 - w6) beta),
     (ellxmono (w1 + w3 + w5) gamma),w1+w3+w5,w4-w6);;

let pintedge alpha beta xalpha = 
  let (d1,d2,d3,_,_) = pintedge_extended alpha beta xalpha in
  (d1,d2,d3);;


(* Delta junction *)

let deltajedge =
  fun alpha beta xalpha ->
    let gamma = pi15 - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let (yalpha,ygamma) = lawsines (two * sigma) (beta') (alpha') (gamma') in
    let xbeta = two * sigma - (ygamma + xalpha) in
    let xgamma = two * sigma - yalpha in
    ((ellxmono xalpha alpha'), (ellxmono xbeta beta'), (ellxmono xgamma gamma'));;


deltajedge (m 0.05) (m 0.06)  (m 0.1);;
area_I (m 1.94) (m 1.88) (m 1.93);;
deltajedge (m 0.0) (m 0.0) (m 0.0);;
pinwheeledge (m 0.0) (pi15) (two * sigma);; (* same as deltajedge, up rto symmetry *)
ellxmono (m 0.0) (m 0.0);;
ellxmono (m 0.0) (pi25);;

(* L-junction Delaunay triangle edge lengths. Rewritten 3/10/2016. *)

let ljedge_extended =
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
    ((xbeta,xgamma),
    ((ellxmono xalpha alpha),(ellxmono xbeta beta),(ellxmono xgamma gamma)));;

let ljedge alpha beta xalpha =
  let (_,ll) = ljedge_extended alpha beta xalpha in
  ll;;

ljedge (m 0.1) (m 0.2) (m 0.753251);;

(* T-junction edge lengths *)

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

let tjedge_extended =
  fun alpha beta xgamma ->
    let gamma = pi - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (pi25 + gamma') in
    let eps' = pi - (pi25 + beta') in
    let (t1,s1) = lawsines xgamma delta' gamma' pi25 in
    let s2 = two*sigma - s1 in
    let (a2,t2) = lawsines s2 eps' delta' alpha' in
    let t3 = two*sigma - (t2-t1) in
    let (a3,xbeta) = lawsines t3 pi25 beta' eps' in 
    let xalpha = a2-a3 in
    let t = (xbeta,t1,s1,s2,a2,t2,t3,a3,xalpha) in
    let t = xbeta in
    ((ellxmono xalpha alpha),(ellxmono xbeta beta),(ellxmono xgamma gamma),xbeta);;

let tjedge alpha beta xgamma =
  let (l1,l2,l3,_) = tjedge_extended alpha beta xgamma in
  (l1,l2,l3);;

tjedge (m 0.9) (m 1.0) (m 0.5);;

(* uniform coordinate systems for 3C dimers, 3/2016 *)
let dimer_pintedge alpha beta xbeta = 
  let dAC,dBC,dAB = pintedge beta alpha xbeta in
  dBC,dAC,dAB;;

let dimer_pinwheeledge alpha beta xbeta = 
  let dAB,dBC,dAC = pinwheeledge ((pi15) - (alpha+beta)) alpha xbeta in
  dBC,dAC,dAB;;

let dimer_lj1edge_extended =
  fun alpha' beta xbeta ->
    let alpha = pi25 - alpha' in
    let gamma = pi35 - (alpha + beta) in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (alpha'+gamma') in
    let (c1,xaa) = lawsines (two*sigma) delta' alpha' gamma' in
    let (a,c2) = lawsines xbeta delta' beta' pi25 in
    let xa = xaa - a in
    let xc = c1 + c2 in
    (ellx xa alpha,ellx xbeta beta,ellx xc gamma,xa,xc);;

let dimer_lj1edge alpha' beta xbeta = 
  let l1,l2,l3,_,_ = dimer_lj1edge_extended alpha' beta xbeta in
  l1,l2,l3;;

let dimer_lj2edge alpha beta xbeta =
  let (dAC,dBC,dAB) = ljedge beta alpha xbeta in
  dBC,dAC,dAB;;

let dimer_lj2edge_extended alpha beta xbeta = 
  let t,(dAC,dBC,dAB) = ljedge_extended beta alpha xbeta in
  dBC,dAC,dAB,t;;

let dimer_lj3edge_extended =
  fun alpha beta xbeta ->
    let gamma = pi35 - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (alpha'+gamma') in
    let (s1,a1) = lawsines xbeta delta' pi25 beta' in
    let s2 = two*sigma - s1 in
    let (xgamma,aa) = lawsines s2 alpha' delta' gamma' in
    (ellx (aa-a1) alpha,ellx xbeta beta,ellx xgamma gamma,aa-a1);;

let dimer_lj3edge alpha beta xbeta = 
  let (d1,d2,d3,_) = dimer_lj3edge_extended alpha beta xbeta in
  (d1,d2,d3);;

let dimer_tj1edge = 
    fun alpha beta xbeta ->
    let gamma = pi - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (alpha'+gamma') in
    let eps' = pi - (pi25  + beta') in
    let (s1,a2) = lawsines xbeta eps' pi25 beta' in
    let (a1,cc) = lawsines (two*sigma) delta' gamma' alpha' in
    let s2 = two*sigma - s1 in
    let (c2,a3) = lawsines s2 delta' eps' pi25 in
    (ellx ((a1+a3)-a2) alpha,ellx xbeta beta,ellx (cc-c2) gamma);;

let dimer_tj2edge alpha beta xbeta = 
  let (dAB,dBC,dAC) = tjedge (pi - (alpha+beta)) alpha xbeta in
  dBC,dAC,dAB;;

let dimer_tj2edge_extended alpha beta xbeta = 
  let (dAB,dBC,dAC,t) = tjedge_extended (pi - (alpha+beta)) alpha xbeta in
  dBC,dAC,dAB,t;;

let dimer_tj3edge alpha' beta xbeta = 
    let alpha = pi25 - alpha' in
    let gamma = pi - (alpha + beta) in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let eps' = pi - (alpha' + pi25) in
    let delta' = pi - (beta'+ pi25) in
    let (c2,a2) = lawsines (two*sigma) eps' alpha' pi25 in
    let (a1,s1) = lawsines xbeta delta' beta' pi25 in
    let s2 = two*sigma - s1 in
    let (a3,cc) = lawsines s2 eps' gamma' delta' in
    let xalpha = (a2+a3)-a1 in
    (ellx xalpha alpha,ellx xbeta beta,ellx (cc-c2) gamma);;

let disjoint_from_dimer_pint alpha beta xbeta = 
  let ab = alpha+beta in
  if pi35 >> ab or xbeta >> m 0.0605 then true
  else
    let (_,_,_,xgamma,_) = pintedge_extended beta alpha xbeta in
    xgamma >> two*sigma;;

let disjoint_from_dimer_pinwheel alpha beta xbeta =
   alpha+beta  >> pi15 or xbeta >> m 0.8;; (* 0.8 from one_pinwheelx *)

let disjoint_from_15_35 alpha beta = 
  let ab = alpha+beta in
  pi15 >> ab or ab >> pi35;;
  
let disjoint_from_dimer_lj1 alpha' beta xbeta =
  let alpha = pi25 - alpha' in
  if disjoint_from_15_35 alpha beta then true
  else 
    let (_,_,_,xa,xc) = dimer_lj1edge_extended alpha' beta xbeta in
    (xa << zero) or (xc >> two*sigma);;

let disjoint_from_dimer_lj2 alpha beta xbeta = 
  disjoint_from_15_35 alpha beta;;

let disjoint_from_dimer_lj3 alpha beta xbeta  = 
  if disjoint_from_15_35 alpha beta or alpha >> m 0.9 then true
  else 
    let (_,_,_,xalpha) = dimer_lj3edge_extended alpha beta xbeta in
    xalpha << zero;;

let disjoint_from_35_45 alpha beta =
  let ab = alpha+beta in
  pi35 >> ab or ab >> pi45;;

let disjoint_from_dimer_tj3 alpha' beta xbeta = 
  let alpha = pi25 - alpha' in
  disjoint_from_35_45 alpha beta;;

let disjoint_from_dimer_tj2 alpha beta xbeta = 
  if disjoint_from_35_45 alpha beta then true
  else 
    let (_,_,_,x) = dimer_tj2edge_extended alpha beta xbeta in
    (x >> two * sigma);;

let disjoint_from_dimer_tj1 alpha beta xbeta = 
  disjoint_from_35_45 alpha beta or (beta << one);;
  
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

let print_stats n xs = 
  if (n mod 100000 = 0) then 
    let ws = map (map width_I) (map fst xs) in
    let vol = end_itlist ( + ) (map (end_itlist ( * )) ws) in
    report (Printf.sprintf "count=%d, length=%d, vol=%4.4f" n (List.length ws) vol.high)
  else ();;

let rec recurserpair eps n onef = function
  | [] -> (n,true)
  | abx :: xs as xss -> 
    let _ = print_stats n xss in
    if onef abx then recurserpair eps (succ n) onef xs 
    else
      let (a1,a2) = splitlist eps (fst abx) in
      recurserpair eps (succ n) onef 
	((a1,snd abx)::(a2,snd abx)::xs);;

let recursetoeps = recurser (1.0e-8) 0;;

let recursepairtoeps = recurserpair (1.0e-8) 0;;

(* version for no extra args *)
let recurserpair_x eps n onef xs  = 
  recurserpair eps n (fun (t,_) -> onef t) (map (fun x -> x,()) xs);;

let recurs_xeps = recurserpair_x (1.0e-8) 0;;

let recursetofinish onef = 
  let wrap3 onef abx = 
    let [a;b;x] = abx in
      onef (a,b,x) in
    recursetoeps (wrap3 onef);;



(* ******************************************************************************** *)
(* Set up computational instances *)
(* ******************************************************************************** *)

(* test that all subcritical pinwheels have an edge > 1.7215.
   test returns true if out of domain or ineq holds.

  *)

let area_exceeds l1 l2 l3 a = (area_I l1 l2 l3 >> a);;

let longest_exceeds l1 l2 l3 r = max l1.low (max l2.low l3.low) > r.high;;

let longgt172 =
  let i172 =  17215 // 10000 in
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

map (tester "17215" one172) types3C;;



(* next: absolute area minimization *)

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
      areamin_acute l1 l2 l3 >>  15 // 10
  with | Unstable -> false;;

mktest ("onedeltajmin",fun() ->
  let ff = sigma / (two * kappa) in
	  (recursetofinish onedeltajamin) 
	    [[zero2 pi15;zero2 pi15;zero2 (two * (sigma-ff))]]);;

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
