(* May 16, 2016 *)

module Banana = struct

(* output provably in range [0,2pi/5] on valid inputs
   even without inter_I *)

let theta_hpos lx theta' = 
  let ly = iloc one lx (pi25 - theta') in
  let r = iloc one lx theta' in
  let h = sqrt_I (r*r - kappa*kappa) in
  let xa = h + sigma in
  let delta = pi310 + iarc r (two*sigma) ly in
  let phi' = asin_I (h / r) in
  let alpha = pi65 - (delta + phi') in
  let theta = alpha - theta' in
  inter_I theta (zero2 pi25);;

let theta_hsign lx theta' hsign = 
  if hsign then theta_hpos lx theta'
  else pi25 - theta_hpos lx (- theta');;

(* boundary curves of banana *)

let curveIt t = acos_I (two*kappa / t) - pi15;;
let curveIIt t = acos_I (t/two);;
let curveIIIt t = - curveIt t;;
let curveIVtpos t = acos_I ((one + t*t-kappa*kappa)/(two*t));;
let curveIVtneg t = -curveIVtpos t;;
let curveVt t = acos_I((one+kappa)/t);;

let curveIth th' = two*kappa/(cos_I (th' + pi15));;
let curveIIth th' = two*cos_I th';;
let curveIIIth th' = curveIth (- th');;
let curveIVth th' = let c = cos_I th' in c + sqrt_I (c*c + kappa*kappa - one);;
let curveVth th' = (one+kappa)/cos_I th';;

curveIt (curveIth (m (- 0.1)));;
curveIIt (curveIIth (m 0.1));;
curveIIIt (curveIIIth (m 0.3));;
curveIVtpos (curveIVth (m 0.1));;
curveIVtneg (curveIVth (m (- 0.1)));;
curveVt (curveVth (m 0.1));;

let square_I t = t * t;;

let someinter_I x y = 
  try Some (inter_I x y) with _ -> None;;

(* coordinates to describe banana *)
let ks = sqrt_I (square_I (two*kappa) + square_I sigma);;
let theta'ks = acos_I (two*kappa/ks);;
let k1s = (sqrt_I (square_I (one+kappa)+square_I sigma));;

(* Partition of banana into boxes. box0 has ridge. The "ridge" is the local max. *)
let box0 = (merge_I zero (pi110), merge_I (one+kappa) (k1s));;
let box1 = (merge_I (theta'ks - pi15) zero, merge_I ks two);;
let box2 = (merge_I zero (pi110), merge_I  k1s two);;

let box3 = (merge_I zero (pi15 - theta'ks), merge_I ks (one+kappa));;
let box4 = (merge_I (pi15-theta'ks) (pi110),merge_I (two*kappa) (one+kappa));;
let box5 = (merge_I (pi110) (pi15),merge_I (two*kappa) k1s);;

let ridgeless_boxes = [
  (box1,Some(curveIVth,curveIVtneg),Some(curveIth,curveIt));
  (box2,None,Some(curveIIth,curveIIt));
  (box3,Some(curveIVth,curveIVtpos),None);
  (box4,Some(curveIIIth,curveIIIt),None);
  (box5,Some(curveIIIth,curveIIIt),Some(curveIIth,curveIIt))];;

let restrict_to_box (x,y) (bx,by) =
  let x1 = someinter_I x bx in
  let y1 = someinter_I y by in
  match (x1,y1) with
  |None,_ -> None
  |_,None -> None
  |(Some u1),(Some v1) -> Some (u1,v1);;

let max_theta_box0 ridget (x,y) =
  let lx = min_I y in
  let th' = ridget lx in
  if (th' << x) then [min_I x,lx]
  else if (th' >> x) then [max_I x,lx]
  else [th',lx];;

let critical_theta_box0 ridget = function
  | None -> []
  | Some (x,y) ->
    let lx = max_I y in
    [(min_I x,lx);(max_I x,lx)] @ max_theta_box0 ridget (x,y);;

let some_function shift = function
  | None ->
    (fun x -> shift),(fun y -> failwith "invalid function extraction")
  | Some (fx,fy) -> (fx,fy);;

let find_critical_points x y lowerc upperc = 
  let (uppercx,uppercy) = some_function (max_I y + one) upperc in
  let (lowercx,lowercy) = some_function (min_I y - one) lowerc in
  let (xmin,xmax,ymin,ymax) = (min_I x,max_I x,min_I y,max_I y) in
  let (lowerLHS,upperLHS) = lowercx xmin, uppercx xmin in
  let (lowerRHS,upperRHS) = lowercx xmax, uppercx xmax in

  let left_corner_filter = filter (fun (x0,y0)->meet_I y0 (merge_I lowerLHS upperLHS)) in
  let right_corner_filter = filter (fun (x0,y0)->meet_I y0 (merge_I lowerRHS upperRHS)) in
  let corners = (left_corner_filter [(xmin,ymin);(xmin,ymax)] @
		   right_corner_filter [(xmax,ymin);(xmax,ymax)]) in
  let curve_filter = filter (fun (x0,y0) -> meet_I y0 y) in
  let curve_points = curve_filter 
    [(xmin,lowerLHS);(xmin,upperLHS);(xmax,lowerRHS);(xmax,upperRHS)] in
  (* now add points on horizontal edges *)
  let add_horiz (lhs,rhs, y, cy) = 
    if meet_I y (merge_I lhs rhs) 
    then Some (cy y,y) else None in
  let horiz_point = selectsome (map add_horiz
    [(lowerLHS,lowerRHS,ymin,lowercy);(lowerLHS,lowerRHS,ymax,lowercy);
     (upperLHS,upperRHS,ymin,uppercy);(upperLHS,upperRHS,ymax,uppercy)]) in
  corners @ curve_points @ horiz_point;;

find_critical_points (zero2 one) (zero2 two) None None;;

let rec compress f = function
  | [] -> []
  | [x] -> [x]
  | a::b::xs ->
    try 
      let t = f a b in
      compress f (t::xs)
    with Failure _ ->
      a::(compress f (b::xs));;

let critical_points_box (x,y) boxdata = 
  let (bx,by),lowerc,upperc = boxdata in
  match restrict_to_box (x,y) (bx,by) with
  | None -> []
  | Some (x,y) -> find_critical_points x y lowerc upperc;;

let critical_points_banana (x,y) = 
  let v1 = List.flatten (List.map (critical_points_box (x,y)) ridgeless_boxes) in
  let x_gmax,y_gmax = (pi15 - theta'ks,ks) in
  let x_gmin,y_gmin = (zero,two) in
  let meets_global_max = meet_I x_gmax x && meet_I y_gmax y in
  let meets_global_min = meet_I x_gmin x && meet_I y_gmin y in
  let v = v1 @ (critical_theta_box0 curveVt (restrict_to_box (x,y) box0)) in
  let (xmin,xmax,ymin,ymax) = (min_I x,max_I x,min_I y,max_I y) in
  let rectangle_boundary_filter = filter (fun (x0,y0) -> 
     meet_I x0 xmin or meet_I x0 xmax or meet_I y0 ymin or meet_I y0 ymax) in
  let global_points = if meets_global_max then [(x_gmax,y_gmax)] else [] @
      if meets_global_min then [x_gmin,y_gmin] else [] in
  let vv = global_points @ rectangle_boundary_filter v in 
  vv;;

(*
  List.fold_right (fun (x,y) = function | [] -> [(x,y)] | (x',y')::bs as bbs -> if meet_I x x' && meet_I y y' then (merge_I x x',merge_I y y')::bs else (x,y)::bbs) [] vsort;;

  let vsort = sort (fun (x0,y0) (x1,y1) -> (x0 << x1 or (meet_I x0 x1 && y0 << y1))) vv in
  let compressor (x0,y0) (x1,y1) = 
    if meet_I x0 x1 && meet_I y0 y1 then (merge_I x0 x1,merge_I y0 y1) 
    else failwith "compressor" in

NB: the variable order is lx theta', but in
the "graphical" procedures is is (theta',lx), following our graphing conventions.
*)

let theta_banana lx theta' = 
  let v = critical_points_banana (theta',lx) in
  let theta_values = map (fun (theta',lx) -> theta_hpos lx theta') v in
  if theta_values = [] then None
  else 
    Some (end_itlist merge_I theta_values);;

let theta_banana_neg lx theta' = 
  match theta_banana lx (- theta') with
  | None -> None
  | Some theta -> Some (pi25 - theta);;

(* tests *)
(*
let ttheta  (theta',lx) = theta_hpos lx theta';;
let bx = 0;;
let by = 0;;
let lowerc = 0;;
let upperc = 0;;
let p1 = (mk (- 0.281) (-0.279), (mk 1.72 1.722));;
let bd1 = hd ridgeless_boxes;;
let  (bx,by),lowerc,upperc = bd1;;
let (x1,y1) =  the( restrict_to_box p1 (bx,by));;
find_critical_points x1 y1 lowerc upperc;;
critical_points_banana p1;;
theta_banana (mk (- 0.281) (-0.279), (mk 1.72 1.722));;
let p2 = ((pi15 - theta'ks), mk 1.72 1.722);;
theta_banana p2;;
map (fun (theta',lx) -> theta_hpos lx theta') cp2;;
let cp2 = critical_points_banana p2;;
ttheta(List.nth cp2 1);;
List.nth cp2 1;;
ttheta(m 0.2798,m 1.722);;
ttheta(m 0.2798,m 1.73);;
ttheta(m 0.2798,m 1.8);; 
end_itlist (merge_I) (map fst cp2);;
 end_itlist (merge_I) (map snd cp2);;
let p3 = (mk 0.628 0.629),(mk 1.618 1.619);;
theta_banana p3;;
pi15;;
let p4 = (mk (-0.1) (0.1)),(mk 1.9 2.1);;
theta_banana p4;;
let cp4 = critical_points_banana p4;;
curveIIth (m 0.1);;
curveIt (m 1.9);;
k1s;;
*)

let theta'_acute lx theta = 
  let s = sin_I (pi310 + theta) in
  let x = sin_I (pi310) / s in
  let phi = asin_I (( lx - x) * s) in
  let alpha' = phi - pi310 in
  let theta' = pi25 - (alpha' + theta) in
  theta';;

theta'_acute ks (theta'ks  + pi15);;
(* boundary durves of danana,
   curve->durve banana->danana, box->dox in this section *)

let durveIt t = acos_I (t/two);;
let durveIIt t = pi15 + acos_I (two*kappa / t);;
let durveIIIt t = pi25 - acos_I (t/two);;
let durveIVtpos t = pi15 + acos_I ((one+kappa) /t);;
let durveIVtneg t = pi15 - acos_I ((one+kappa) /t);;
let durveVt t = pi15 + acos_I ((kappa*kappa + t*t - one)/(two*t*kappa));;

let durveIth th = two*cos_I(th);;
let durveIIth th = two*kappa/(cos_I (th - pi15));;
let durveIIIth th = two*cos_I (th - pi25);;
let durveIVth th = (one+kappa)/cos_I (pi15 - th);;
let durveVth th = let c = cos_I(th-pi15) in kappa*c + sqrt_I (square_I (kappa*c) + one - kappa*kappa);;

(*
durveIt (durveIth (m (0.35)));;
durveIIt (durveIIth (m (0.7)));;
durveIIIt (durveIIIth (m 1.0));;
durveIVtpos (durveIVth (m 0.7));;
durveIVtneg (durveIVth (m (0.4)));;
durveVt (durveVth (m 0.7));;
pi110;;
durveIth  (pi110);;
durveIth (pi15);;
durveIIth (pi15);;
durveIIth (pi25);;
durveIIIth(pi25);;
durveIIIth(pi310);;
durveIVth (pi310);;
durveIVth (pi15);;
one+kappa;;
durveIVth (pi110);;
*)

(* dox0 has ridge *)
let dox0 = (merge_I pi15 (theta'ks + pi15), merge_I ks (one+kappa));;
let dox1 = (merge_I (pi110) pi15, merge_I (two*kappa) (sqrt_I (two*(one+kappa))));;
let dox2 = (merge_I pi15 (pi310),merge_I (one+kappa) (sqrt_I (two*(one+kappa))));;

let dox3 = (merge_I pi15 (theta'ks+pi15), merge_I (two*kappa) ks);;
let dox4 = (merge_I (pi310) (theta'ks+pi15),merge_I (one+kappa) two);;
let dox5 = (merge_I (theta'ks+pi15) pi25,merge_I ks two);;

let ridgeless_doxes = [
  (dox1,Some(durveIth,durveIt),Some(durveIVth,durveIVtneg));
  (dox2,None,Some(durveIVth,durveIVtpos));
  (dox3,Some(durveIIth,durveIIt),None);
  (dox4,None,Some(durveIIIth,durveIIIt));
  (dox5,Some(durveIIth,durveIIt),Some(durveIIIth,durveIIIt))];;

let min_critical_theta_dox_ridge ridget (x,y) =
  let lx = max_I y in
  let th' = ridget lx in
  if (th' << x) then [min_I x,lx]
  else if (th' >> x) then [max_I x,lx]
  else [th',lx];;

let critical_theta_dox_ridge ridget = function
  | None -> []
  | Some (x,y) ->
    let lx = min_I y in
    [(min_I x,lx);(max_I x,lx)] @ min_critical_theta_dox_ridge ridget (x,y);;

(* critical_points_box, restrict_to_box unchanged *)

let critical_points_danana (x,y) = 
  let v1 = List.flatten (List.map (critical_points_box (x,y)) ridgeless_doxes) in
  let x_gmax,y_gmax = (pi15,two*kappa) in
  let x_gmin,y_gmin = (pi310,sqrt_I (two*(one+kappa))) in
  let meets_global_max = meet_I x_gmax x && meet_I y_gmax y in
  let meets_global_min = meet_I x_gmin x && meet_I y_gmin y in
  let v = v1 @ (critical_theta_dox_ridge durveVt (restrict_to_box (x,y) dox0)) in
  let (xmin,xmax,ymin,ymax) = (min_I x,max_I x,min_I y,max_I y) in
  let rectangle_boundary_filter = filter (fun (x0,y0) -> 
    meet_I x0 xmin or meet_I x0 xmax or meet_I y0 ymin or meet_I y0 ymax) in
  let global_points = if meets_global_max then [(x_gmax,y_gmax)] else [] @
      if meets_global_min then [x_gmin,y_gmin] else [] in
  let vv = global_points @ rectangle_boundary_filter v in 
  vv;;

let theta'_danana (theta,lx) = 
  let v = critical_points_danana (theta,lx) in
  let theta'_values = map (fun (theta,lx) -> theta'_acute lx theta) v in
 end_itlist merge_I theta'_values;;


(* tests *)

(*
let ttheta'  (theta',lx) = theta'_acute lx theta';;
let p2 = ((pi15 - theta'ks), mk 1.72 1.722);;
let cp2 = critical_points_banana p2;;
theta_banana p3;;
pi15;;
let p4 = (mk (-0.1) (0.1)),(mk 1.9 2.1);;
theta_banana p4;;
let cp4 = critical_points_banana p4;;
curveIIth (m 0.1);;
curveIt (m 1.9);;
k1s;;
*)

(* first version is flawed. We don't know which it theta, which is theta'.
let pent_contact_deprecated lx theta theta' = 
  let theta's = Pet.periodize_pent theta' in
  let thetas = Pet.periodize_pent theta in
  let mx x = max_I (
  let sort (th,th') = 
  let thetas2 = selectsome (map (theta_banana lx) theta's @
		   map (theta_banana_neg lx) theta's) in
  exists (fun (a,b) -> meet_I a b) (outer pair thetas thetas2);;
*)

(* ordering makes theta' positive and smaller in absolute value than theta *)

let pent_contact lx itheta itheta' =
  let split i = List.flatten (map Pet.splitat0  (Pet.periodize_pent i)) in
  let ithetas = split itheta in
  let ithetas' = split itheta' in
  let cases = List.flatten (Lib.allpairs Pet.reorder ithetas ithetas') in
  let up0 (th',th,samesign) = if samesign then (th',th) else (th',pi25 - th) in
  let cases0 = map up0 cases in
  let p = List.flatten (
    map (fun (th',th) -> [(theta_banana lx th',th);(theta_banana_neg lx th',th)]) cases0) in
  exists (fun (s,th) ->
    match s with
    | None -> false
    | Some th2 -> meet_I th2 th) p;;

(* theta must be between 0 2pi/5, theta' in [-pi/5,pi/5] .
   Must have th' <= th, th' <= 2pi/5 - th *)

let ell_ofth theta theta' = 
  let alpha = theta + theta' in
  let x = sin_I (pi310) / sin_I (theta+ pi310) in
  let y = sin_I (pi710 - alpha) / sin_I (pi710 - theta) in
  x + y;;

(* essentially the same as pent_contact, but more concise and a bit faster. *)

let pent_contact2 lx itheta itheta' =
  let split i = List.flatten (map Pet.splitat0  (Pet.periodize_pent i)) in
  let ithetas = split itheta in
  let ithetas' = split itheta' in
  let cases = List.flatten (Lib.allpairs Pet.reorder ithetas ithetas') in
  let up0 (th',th,samesign) = if samesign then (th',th) else (th',pi25 - th) in
  let cases0 = map up0 cases in
  exists (fun (th',th) -> meet_I lx (ell_ofth th th')) cases0;;

(* test  

let ffx a b = 
  let  (ell,th,th') = ellthetax (m a) (m b) in
  (ell,th,th',pent_contact (ell + mk ( 0.001) 0.00001) th th');;

let fg _ =
  let w = Random.float  0.0011 in
  let xa = random (zero2 (two*sigma)) w in
  let alpha = random (zero2 pi45) w in
  let (ell,th,th') = ellthetax xa alpha in
  pent_contact2 (ell +  m 0.1) th' th;;

setify (time (map fg) (0--10000));;
ffx 0.1 0.1;;
ffx 0.2 0.2;;
ffx 0.3 0.3;;
ffx 0.9 0.9;;
time (ffx 0.3) 0.4;;

1;;

*)

(* ************************************************** *)
(* fillout P-triangles  *)
(* ************************************************** *)
  

let fillout2C dACrange (dAB,thABC,thBAC) (dBC,thCBA,thBCA) =
  try
    let arcBrange = iarc dAB dBC dACrange in
    let prearc = pi25 - (thBAC+thBCA) in
    let k = getint ((arcBrange - prearc)/pi25) in
    if (k=None) then None
    else
      let arcB = prearc + the k*pi25 in
      let dAC = iloc dAB dBC arcB in
      if (dAC << two*kappa) then None
      else
	let dAC = merge_I (max2_I (two*kappa) (min_I dAC)) (max_I dAC) in
	let arcC = iarc dAC dBC dAB in
	let arcA = iarc dAC dAB dBC in
	let a = areamin_acute dAC dAB dBC in
	let thACB = pi25 - (arcA + thABC) in
	let thCAB = pi25 - (arcC + thCBA) in
	if arcA >> pi2 or arcB >> pi2 or arcC >> pi2 or not(Pet.pet dAC thACB thCAB)
	then None
	else
	  Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB))
  with e -> raise e;;


let mk2C dACrange (xs,(sgnalpha,sgnbeta)) = 
  let [xalpha; alpha;  xbeta; beta] = xs in
  let dAB_triple  = ellthetax_sgn xalpha alpha sgnalpha in
  let dBC_triple  = ellthetax_sgn xbeta beta sgnbeta in
  fillout2C dACrange dAB_triple dBC_triple;;

let mk2Ce dACrange xs = mk2C dACrange (xs,(true,true));;

(* fillout 5D.  Acute triangle.
   One pent contact between A and C. A points to C. 
   Full input coordinates (dAB,thABC,thBAC) given along edge AB. *)

let fillout5D ((dAB,thABC,thBAC),dBC,dAC) = 
  if not(Pet.pet dAB thABC thBAC) then None 
  else
    let arcC = iarc dAC dBC dAB in
    let arcA = iarc dAC dAB dBC in
    let arcB = iarc dAB dBC dAC in
    let a = areamin_acute dAC dAB dBC in
    let thACB = - (arcA + thABC) in
    let thBCA = - (arcB + thBAC) in
    let thACB0 = Pet.periodize_pent thACB in
    let thACB_CAB_pos = map (fun t -> t,theta_banana dAC t) thACB0 in
    let thACB_CAB_neg = map (fun t -> t,theta_banana_neg dAC t) thACB0 in
    let thACB_CAB= mapfilter (fun (t,s) -> (t, the s)) (thACB_CAB_pos @ thACB_CAB_neg) in
    let thACB_CAB_CBA = map (fun (t1,t) -> (t1,t,-(arcC + t))) thACB_CAB in
    let thACB_CAB_CBA = filter (fun (_,_,th') -> Pet.pet dBC thBCA th') thACB_CAB_CBA in 
    if (thACB_CAB_CBA = []) then None 
    else
	(Some (a,(map (fun (thACB,thCAB,thCBA) -> 
	  (dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	  (dAC,thACB,thCAB,arcB) ) thACB_CAB_CBA)));;

let fillout6D ((dAB,thABC,thBAC),(dBC,thCBA),dAC) = 
  if not(Pet.pet dAB thABC thBAC) then None 
  else
    let arcC = iarc dAC dBC dAB in
    let arcA = iarc dAC dAB dBC in
    let arcB = iarc dAB dBC dAC in
    let a = areamin_acute dAC dAB dBC in
    let thACB = - (arcA + thABC) in
    let thBCA = - (arcB + thBAC) in
    let thCAB = - (arcC + thCBA) in
    if Pet.pet dAC thACB thCAB && Pet.pet dBC thBCA thCBA then
      Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
      (dAC,thACB,thCAB,arcB))
    else None;;



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

end;; 


