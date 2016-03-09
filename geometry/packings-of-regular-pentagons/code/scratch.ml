reneeds "/home/hasty/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/pent.ml";;
reneeds "/home/hasty/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/work-in-progress/pet.ml";;



open Pent;;
open Pet;;


acos_I (mk 0.5 1.1);;
thetax (m 0.1) (m 0.2);;
sqrt_I (m (- 0.1));;
inter_I (mk 1.0 2.0) (mk 2.1 3.0);;

meet_I (mk 1.0 2.0) (mk 0.0 0.5);;
  let range = mk 172.0 178.0 / m 100.0;;


  let inf = one / mk_interval (-1.0,1.0);;
disjoint_I eps_I inf;;

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
  let pi25 = ratpi 2 5 in
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

(* B is the pentagon that touches both others.
   alpha variables between A and B
   beta variables between B and C.
   when signs are true, then B is the pointer *)

let mk2C dACrange (xs,(sgnalpha,sgnbeta)) = 
  let [xalpha; alpha;  xbeta; beta] = xs in
  let pi25 = ratpi 2 5 in
    try
      let (dAB,thABC,thBAC) = ellthetax_sgn xalpha alpha sgnalpha in
      let (dBC,thCBA,thBCA) = ellthetax_sgn xbeta beta sgnbeta in
      let arcBrange = iarc dAB dBC dACrange in
      let prearc = pi25 - (thBAC+thBCA) in
      let k = getint ((arcBrange - prearc)/pi25) in
      if (k=None) then None
      else
	let arcB = prearc + the k*pi25 in
	let dAC = iloc dAB dBC arcB in
	let arcC = iarc dAC dBC dAB in
	let arcA = iarc dAC dAB dBC in
	let a = areamin_acute dAC dAB dBC in
	let thACB = pi25 - (arcA + thABC) in
	let thCAB = pi25 - (arcC + thCBA) in
	if not(pet dAC thACB thCAB)
	then None
	else
	  Some (a,dAB,dAC,dBC,arcA,arcB,arcC,thABC,thBAC,thCBA,thBCA,thACB,thCAB)
    with e -> raise e;;

let one_iso2C xs = 
  let dACrange = mk 1.72 1.79 in
  try
    let v = mk2C dACrange xs in
    if (v = None) then true
    else 
      let (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in
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
      let (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in
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
	let (a,dAB,dAC,dBC,arcA,arcB,arcC,
	     thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in
	(a >> aK) or (dAC >> m 1.79) 
    with Unstable -> false;;

let one_pintx xs = 
  let ([alpha;beta;xa],_) = xs in
  if disjoint_from_pint alpha beta then true
      else 
      let (d1,d2,d3,w,xb)= pintedge_extended alpha beta xa in
      let a = areamin_acute d1 d2 d3 in
      w >> two*sigma or
      (a >> aK+epso_I) or ((d2 << m 1.72) && (xb >> sigma));;

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

recursepairtoeps one_iso2C domain_iso2C;;
recursepairtoeps one_iso2C' domain_iso2C';;
recursepairtoeps one_scaleneto3C domain_scaleneto3C;;
recursepairtoeps one_pintx (map (fun t->(t,(true,true))) pintdomain);;

let ce = map mk_interval [(0.854120493332,0.854120502695);(1.21644675543,1.21644676479);(0.000468112587929,0.000468119800091)];;
let [alpha1;beta1;xa1] = ce;;
pintedge_extended alpha1 beta1 xa1;;
two*sigma;;
areamin_acute (m 1.95) (m 1.73) (m 1.635);;
aK + epso_I;;





let one127 (sgnalpha,sgnbeta) xs  = 
  try
  let dACrange = mk 1.72 1.79 in
  let v = mk2C dACrange (xs,( sgnalpha, sgnbeta)) in
  if (v = None) then true
  else 
    let (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in
       (a >> rat 127 100) or disjoint_I dAB dAC or
	 dAC >> dAB
  with Unstable -> false;;

let domain2C =   [map zero2 [two*sigma;ratpi 2 5;two*sigma;ratpi 2 5]];;

let recursesgn f dom = 
  map (fun t -> recursetoeps (f t) dom)
    [(true,true);(true,false);(false,true);(false,false)];;

recursesgn one127 domain2C;;

let onedACfail (sgnalpha,sgnbeta) xs  = 
  try
  let v = mk_isosceles sgnalpha sgnbeta xs in
  if (v = None) then true
  else 
    let (a,dAB,dAC,dBC,arcA,arcB,arcC,
	 thABC,thBAC,thCBA,thBCA,thACB,thCAB) = the v in
       (dAC >> rat 173 100)
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
       (dAC << rat 178 100) (* 179, 178 fails *)
  with Unstable -> false;;
[(0.,8.75868279178e-09);(0.313545663681,0.313545673044);(0.,8.75868279178e-09);(0.00122708164088,0.00122709100355)];;

