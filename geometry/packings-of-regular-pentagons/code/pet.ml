module Pet = struct

let rec allpair acc f l1 l2 = 
    match l1 with 
      [] ->  acc
    | (h1::t1) ->  allpair ((List.map (f h1) l2) @ acc) f t1 l2;;


(* reduces interval modulo 1 so that interval is in [0,1] *)

let periodize1 ix = 
  if (ix.high  >= 1.0 +. ix.low) then [mk_interval(0.0,1.0)]
  else
    let iy = ix - m (floor ix.low) in
      if iy.high <= 1.0 then [iy] else
	[mk_interval (iy.low,1.0);mk_interval(0.0,iy.high -. 1.0)];;

periodize1 (mk_interval(3.3 ,4.4 ));;
periodize1 (mk_interval(3.3 ,3.8 ));;
periodize1 (mk_interval(3.7 ,4.2 ));;
periodize1 (mk_interval(-3.7 ,-2.8 ));;

(* arbitrary period r. Reduce between [0,r]. *)

let periodize ix r = 
  let eps = m (1.0e-8) in 
  let _ = r >> eps or failwith "underflow periodize" in
    map (( * ) r) (periodize1 (ix / r));;

periodize (mk_interval(3.3 ,4.4 )) (m 0.2);;
periodize (mk_interval(3.3 ,3.35 )) (m 0.2);;
periodize (mk_interval(3.37 ,3.42 )) (m 0.2);;

(* arbitrary period, arbitrary lower endpoint
   All values are put between a and a+r. *)

let periodize_min ix r a = 
  let iy = ix -  a in
    map (( + ) ( a)) (periodize iy r);;

let xi2 = m 0.2;;
let xi1 = m 0.1;;
periodize_min (mk_interval(3.3 ,4.4 )) xi2 xi1;;
periodize_min (mk_interval(3.37 ,3.43 )) xi2 xi1;;
periodize_min (mk_interval(3.45 ,3.54 )) xi2 xi1;;

(* this puts the angle in the range (-pi/5,pi/5), splitting the
angle if necessary *)
(* let periodize_angle = 0;; *)

let periodize_pent ix = 
  periodize_min ix (ratpi 2 5) (- ratpi 1 5);;

let periodize_pent0 ix =
  periodize_min ix pi25 zero;;

(* now run the pent existence tests for same sign and mixed sign cases *)
      
let case_pet_pos l (itheta',iabstheta) =
  let pi5 = ratpi 1 5 in
  let abstheta = max_I iabstheta in 
  let locx th = iloc l one th in
  let beta th = ilawbeta th (locx th) one in
  let r th = kappa / cos_I (beta th + pi5 - abstheta) in 
  let f th = (locx th).high >= (r th).low in
(*  (beta th).low <= abstheta.high in *)
    f (min_I itheta') or f (max_I itheta');;

let case_pet_neg l (itheta',iabstheta) =
  let pi5 = ratpi 1 5 in
  let theta' = max_I itheta' in
  let iabstheta = inter_I iabstheta (mk (theta'.high) (iabstheta.high)) in
  let locx = iloc l one theta' in
  let beta = ilawbeta theta' locx one in
  let target = pi5 - beta in
  let abstheta = 
    if iabstheta >> target then min_I iabstheta
    else if iabstheta << target then max_I iabstheta
    else target in
  let r = kappa / cos_I (pi5 - (beta + abstheta)) in
    locx.high >= r.low;;

let pet0 l (itheta', iabstheta,samesign) = 
  let locx = iloc one l (max_I itheta') in
    if locx.high >= one.low then true
    else if locx <<  kappa then false
    else if not(samesign) then case_pet_neg l (itheta',iabstheta) 
    else case_pet_pos l (itheta',iabstheta);;

let splitat0 itheta = 
  if (itheta >>= zero) then [(itheta,true)]
  else if (itheta <<= zero) then [(-itheta,false)]
  else [mk_interval(0.0,itheta.high),true;
	mk_interval(0.0, -. itheta.low),false];;

(* break into cases with first < second *)

let resize(t1,t2,samesign) =
  let t = mk (t1.low) (t2.high) in
  let t1 = inter_I t1 t in
  let t2 = inter_I t2 t in
  (t1,t2,samesign);;

let reorder (th1,b1) (th2,b2) = 
  let samesign = (b1=b2) in
  if (th1 << th2) then [(th1,th2,samesign)]
  else if (th2 << th1) then [(th2,th1,samesign)]
  else [resize(th1,th2,samesign);resize(th2,th1,samesign)];;

(* symmetrical in itheta itheta' *)

let pet il itheta itheta' = 
  let split i = List.flatten (map splitat0  (periodize_pent i)) in
  let ithetas = split itheta in
  let ithetas' = split itheta' in
  let cases = List.flatten (allpair [] reorder ithetas ithetas') in
  exists (pet0 (max_I il)) cases;;

end;;
