(* automatic differentiation *)
module Autodiff = struct


let ( +^ ) (a0,a1) (b0,b1) = 
  (a0+b0,a1+b1);;

let ( -^ ) (a0,a1) (b0,b1) =
  (a0-b0,a1-b1);;

let near eps r x = 
  (x.high <= r +. eps) && (x.low >= r -. eps);;

let neare2 (r1,r2) (x1,x2) = 
  (near (1.0e-14) r1 x1 && near (1.0e-14) r2 x2);;

let test_addD = 
  let x = (m 3.0,m 4.0) in
  let y = (m 4.1,m 5.1) in
  neare2 (0.0,0.0) (((x +^ y) -^ y) -^ x);;

let ( *^ ) (a0,a1) (b0,b1) = 
  (a0 * b0,a0 *b1 + a1*b0);;

let ( /^ ) (a0,a1) (b0,b1) = 
  (a0/ b0, (a1*b0 - a0*b1) / (b0 * b0));;

let test_multD = 
  let x = (m 3.0,m 4.0) in
  let y = (m 4.1,m 5.1) in
  neare2 (1.0,0.0) (((x *^ y) /^ y) /^ x);;

let sqrtD (a0,a1) = 
  (sqrt_I a0, a1 / (two * sqrt_I a0));;

let test_sqrtD = 
  let x = (m 3.0,m 4.0) in
  let y = sqrtD x in
  neare2 (1.0,0.0) ((y *^ y) /^ x);;
  
let sinD (a0,a1) = 
  (sin_I a0,cos_I a0 * a1);;

let cosD (a0,a1) = 
  (cos_I a0, - sin_I a0 * a1);;

let acosD (a0,a1) = 
  (acos_I a0, - a1 / sqrt_I (one - a0*a0));;

let asinD (a0,a1) = 
  (asin_I a0, a1/ sqrt_I (one - a0*a0));;

let test_sinD = 
  let x = (m 1.1,m 1.2) in
  let y = sinD x in
  neare2 (1.0,0.0) (asinD y /^ x);;

let test_cosD = 
  let x = (m 1.1,m 1.2) in
  let y = cosD x in
  neare2 (1.0,0.0)  (acosD y /^ x);;

let iD s = (s,zero);;

let mk_intervalD s = iD (mk_interval s);;

let mD r = mk_intervalD(r,r);;

let mkD x y = mk_intervalD(x,y);;

let zeroD = mD 0.0;;

let oneD = mD 1.0;;

let twoD = mD 2.0;;

let fourD = mD 4.0;;

let i16D = mD 16.0;;

(* deprecated let eps_D = iD eps_I;; *)

let piD = iD  pi_I;;

let pi2D = iD pi2;;

let twopiD = iD twopi;;

let ratpiD i j = iD(ratpi i j);;

let pi15D = ratpiD 1 5;;
let pi25D = ratpiD 2 5;;
let pi35D = ratpiD 3 5;;
let pi45D = ratpiD 4 5;;

let ratD i j = iD (rat i j);;

let kappaD = cosD pi15D;;
let sigmaD = sinD pi15D;;

let aKD = iD aK;;

let epso_D = aKD -^ ratD 1237 1000;;

let test_epso_D = 
  neare2 (0.0,0.0) (epso_D -^ iD epso_I);;

let ups_D x1 x2 x3 = 
  twoD *^ 
  (x1 *^ x2 +^ x2 *^ x3 +^ x3 *^ x1) -^ x1*^ x1 -^ x2*^ x2 -^ x3 *^ x3;;

let nearfst f0 g = near (1.0e-14) f0 (fst g);;

let test_ups_D = 
  let (x1,x2,x3) = (m 1.1,m 1.2,m 1.3) in
  nearfst (ups_I x1 x2 x3).high (ups_D (iD x1) (iD x2) (iD x3));;

let area_D y1 y2 y3 = 
  let x1 = y1 *^ y1 in
  let x2 = y2 *^ y2 in
  let x3 = y3 *^ y3 in
    sqrtD (ups_D x1 x2 x3 ) /^ fourD;;

let test_area_D = 
  let (x1,x2,x3) = (m 1.1,m 1.2,m 1.3) in
  nearfst (area_I x1 x2 x3).high (area_D (iD x1) (iD x2) (iD x3));;

let arcD a b cop =
  acosD (((a *^ a) +^ (b *^ b) -^ (cop *^ cop)) /^ (twoD *^ a *^ b));;

let test_arcD =
  let (x1,x2,x3) = (m 1.1,m 1.2,m 1.3) in
  nearfst (iarc x1 x2 x3).high (arcD (iD x1) (iD x2) (iD x3));;

let lawsinesD a alpha beta gamma = 
  let aa = a /^ sinD alpha in
  (aa *^ sinD beta, aa *^ cosD gamma);;

let lawbetaD alpha a b = 
  asinD (b *^ sinD alpha /^ a);;

let locD a b theta = 
  let costh = cosD theta in
  sqrtD (a *^ a +^ b *^ b -^ twoD *^ a *^ b *^ costh);;

let ell_auxD h psi = 
  let r = sqrtD (h *^ h +^ kappaD *^ kappaD) in
  let theta = acosD (h /^ r) in
  locD oneD r (psi +^ theta);;

let ellD = 
  let pi310D = ratpiD 3 10 in
  fun x alpha ->
    ell_auxD (sigmaD -^ x) (alpha +^ pi310D);;

let pinwheeledgeD alpha beta xgamma = 
  let gamma = pi15D -^ (alpha +^ beta) in
  let (xalpha,xbeta) = 
    lawsinesD xgamma (pi25D -^ alpha) (pi25D -^ beta) (pi25D -^ gamma) in
  (ellD xalpha alpha,ellD xbeta beta,ellD xgamma gamma);;

let ljedge_extendedD alpha beta xalpha = 
  let gamma = pi35D -^ (alpha +^ beta) in
  let alpha' = pi25D -^ alpha in
  let beta' = pi25D -^ beta in
  let gamma' = pi25D -^ gamma in
  let delta' = piD -^ (alpha' +^ beta') in
  let (s1,b1) = lawsinesD xalpha delta' beta' alpha' in
  let s2 = twoD*^ sigmaD -^ s1 in
  let (b2,xgamma) = lawsinesD s2 pi25D gamma' delta' in
  let xbeta = b1 -^ b2 in
    ((xbeta,xgamma),
    ((ellD xalpha alpha),(ellD xbeta beta),(ellD xgamma gamma)));;

let ljedgeD alpha beta xalpha =
  let (_,ll) = ljedge_extendedD alpha beta xalpha in
  ll;;

let dimer_pinwheeledgeD alpha beta xbeta = 
  let dAB,dBC,dAC = pinwheeledgeD (pi15D -^ (alpha+^beta)) alpha xbeta in
  dBC,dAC,dAB;;

let dimer_lj1edge_extendedD =
  let pi25 = ratpiD 2 5 in
  let pi35 = ratpiD 3 5 in
  fun alpha' beta xbeta ->
    let alpha = pi25 -^ alpha' in
    let gamma = pi35 -^ (alpha +^ beta) in
    let beta' = pi25 -^ beta in
    let gamma' = pi25 -^ gamma in
    let delta' = piD -^ (alpha'+^ gamma') in
    let (c1,xaa) = lawsinesD (twoD*^ sigmaD) delta' alpha' gamma' in
    let (a,c2) = lawsinesD xbeta delta' beta' pi25 in
    let xa = xaa -^ a in
    let xc = c1 +^ c2 in
    (ellD xa alpha,ellD xbeta beta,ellD xc gamma,xa,xc);;

let dimer_lj1edgeD alpha' beta xbeta = 
  let l1,l2,l3,_,_ = dimer_lj1edge_extendedD alpha' beta xbeta in
  l1,l2,l3;;

let dimer_lj2edgeD alpha beta xbeta =
  let (dAC,dBC,dAB) = ljedgeD beta alpha xbeta in
  dBC,dAC,dAB;;

let dimer_lj2edge_extendedD alpha beta xbeta = 
  let t,(dAC,dBC,dAB) = ljedge_extendedD beta alpha xbeta in
  dBC,dAC,dAB,t;;

let dimer_tj3edgeD alpha' beta xbeta = 
    let alpha = pi25D -^ alpha' in
    let gamma = piD -^ (alpha +^ beta) in
    let beta' = pi25D -^ beta in
    let gamma' = pi25D -^ gamma in
    let eps' = piD -^ (alpha' +^ pi25D) in
    let delta' = piD -^ (beta'+^ pi25D) in
    let (c2,a2) = lawsinesD (twoD*^ sigmaD) eps' alpha' pi25D in
    let (a1,s1) = lawsinesD xbeta delta' beta' pi25D in
    let s2 = twoD*^ sigmaD -^ s1 in
    let (a3,cc) = lawsinesD s2 eps' gamma' delta' in
    let xalpha = (a2+^ a3)-^ a1 in
    (ellD xalpha alpha,ellD xbeta beta,ellD (cc-^ c2) gamma);;

(* linear motion from given values to Kuperberg critical values *)

(* junk:
let expandD (alphaB,beta,xbeta,alphaD) = 
  let (a1,b1,x1,d1) = (zero,pi15,sigma,zero) in
  ((alphaB,a1-alphaB),(beta,b1-beta),(xbeta,x1-xbeta),(alphaD,d1-alphaD));;
*)

let one_twist_claim_lj1 xs =
  let ([alpha';beta;xbeta],_) = xs in
  if disjoint_from_dimer_lj1 alpha' beta xbeta then true
  else 
    try
        let (_,_,_,xa,_) = dimer_lj1edge_extended alpha' beta xbeta in
        (xa >> sigma)
    with Unstable -> false;;

let dummybool = Dimer.dummybool;;

let twist_claim_lj1 =
  let ee = mk (-0.01) (0.01) in
  let eps_domain =[[zero2 (m 0.01);pi15 + ee;sigma+ee]] in
  recursepairtoeps one_twist_claim_lj1 (dummybool eps_domain);;

let one_twist_claim_lj2 xs = 
  try
    let ([alpha;xbeta],_) = xs in
    let beta_t = (pi15,zero) in
    let alpha_t = (alpha,- one) in
    let xbeta_t = (xbeta,zero) in
    let (l1,l2,l3) = dimer_lj2edgeD alpha_t beta_t xbeta_t in
    let (_,a') = area_D l1 l2 l3 in
      (a' << zero)
    with Unstable -> false;;

let twist_claim_lj2 =
  let ee = mk (-0.01) (0.01) in
  let eps_domain =[[zero2 (m 0.01);sigma+ee]] in
  recursepairtoeps one_twist_claim_lj2 (dummybool eps_domain);;

let one_dimerD xs = 
  let ([alphaB;betaB;xbetaB;alphaD],
       ((sB,edgeB,curveB,disjointB),(sD,edgeD,curveD,disjointD))) = xs in
  try
    (* subcritical triangle ABC: *)
    if disjointB alphaB betaB xbetaB then true 
    else
      let alphaB_t = curveB alphaB in
      let betaB_t = (betaB,one) in
      let (dBC,dAC,dAB) = edgeB alphaB_t betaB_t (iD xbetaB) in
      let aABC = area_D dBC dAC dAB in
      (* second triangle ADC of dimer: *)
      let betaD = pi25 - betaB in
      let xbetaD = two * sigma - xbetaB in
      if disjointD alphaD betaD xbetaD then true
      else 
	let alphaD_t = curveD alphaD in
	let betaD_t = (betaD,-one) in
	let (dCD,dAC',dAD) = edgeD alphaD_t betaD_t (iD xbetaD) in
	let aADC = area_D dCD dAC' dAD in
	let (_,area_derivative) = aABC +^ aADC in
	area_derivative << zero  
  with | Unstable -> false;;

let i_m1 alpha = (alpha,-one);;

let dimerD_toptypes = [
  ("pinw_apos",dimer_pinwheeledgeD,i_m1,disjoint_from_dimer_pinwheel)  ;
  ("pinw_a0",dimer_pinwheeledgeD,iD,disjoint_from_dimer_pinwheel);
  ("lj1top",dimer_lj1edgeD,i_m1,disjoint_from_dimer_lj1);
  ("lj2top",dimer_lj2edgeD,i_m1,disjoint_from_dimer_lj1);];;

let dimerD_bottypes = [
  ("lj1bot",dimer_lj1edgeD,i_m1,disjoint_from_dimer_lj1);
  ("lj2bot_apos",dimer_lj1edgeD,i_m1,disjoint_from_dimer_lj1);
  ("lj2bot_a0",dimer_lj2edgeD,iD,disjoint_from_dimer_lj2);
  ("tj3bot",dimer_tj3edgeD,i_m1,disjoint_from_dimer_tj3);];;

let dimerD_domain (i,j) = 
  let eps = zero2 (m 0.01) in
  ([eps;pi25-eps;two*sigma+eps-eps;eps]),
  (List.nth dimerD_toptypes i,List.nth dimerD_bottypes j);;

let dtypeD_labels xs = 
  let (_,((sB,_,_,_),(sD,_,_,_))) = xs in
  (sB,sD);;

let recurse_dimerD d =
    try 
      let _ = report "..." in
      recurserpair (1.0e-8) 0 (one_dimerD) [d]
    with Failure s ->
      let (sB,sD) = dtypeD_labels d in
      failwith ("one_dimerD("^sB^","^sD^") "^s);;

let recurseD i j = recurse_dimerD (dimerD_domain (i,j));;
map (recurseD 0) (0--3);;
map (recurseD 1) (0--3);;
map (recurseD 2) (0--3);;
map (recurseD 3) (0--3);;


(* end of first derivatives *)


(* start second derivatives *)
let neare3 (r1,r2,r3) (x1,x2,x3) = 
  let e = 1.0e-12 in
  (near e r1 x1 && near e r2 x2) && near e r3 x3;;

let ( +^^ ) (a0,a1,a2) (b0,b1,b2) = 
  (a0+b0,a1+b1,a2+b2);;

let ( -^^ ) (a0,a1,a2) (b0,b1,b2) =
  (a0-b0,a1-b1,a2-b2);;

let test_addD2 = 
  let x = (m 3.0,m 4.0,m 4.3) in
  let y = (m 4.1,m 5.1,m 5.3) in
  neare3 (0.0,0.0,0.0) (((x +^^ y) -^^ y) -^^ x);;

let ( *^^ ) (a0,a1,a2) (b0,b1,b2) = 
  (a0 * b0,a0 *b1 + a1*b0,a2*b0 + two*a1*b1 + a0*b2);;

let ( /^^ ) (a0,a1,a2) (b0,b1,b2) = 
  let d1 = (a1*b0 - a0*b1) / (b0 * b0) in
  (a0/ b0, d1,
   (a2*b0-a0*b2)/(b0*b0) - two*b1*d1/ b0);;

let test_multD = 
  let x = (m 3.0,m 4.0,m 4.3) in
  let y = (m 4.1,m 5.1,m 5.3) in
  neare3 (1.0,0.0,0.0) (((x *^^ y) /^^ y) /^^ x);;

let sqrtD2 (a0,a1,a2) = 
  let s = sqrt_I a0 in
  (s,a1 /(two*s), - a1*a1/(four*s*s*s) + a2/(two* s));;

let test_sqrtD2 = 
  let x = (m 3.0,m 4.0,m 4.2) in
  let y = sqrtD2 x in
  neare3 (1.0,0.0,0.0) ((y *^^ y) /^^ x);;

let sinD2 (a0,a1,a2) = 
  let s = sin_I a0 in
  let c = cos_I a0 in
  (s,c * a1, - s* a1*a1 + c * a2);;

let cosD2 (a0,a1,a2) = 
  let s = sin_I a0 in
  let c = cos_I a0 in
  (c, - s * a1, - c * a1 * a1 - s * a2);;

let acosD2 (a0,a1,a2) = 
  let r = one - a0*a0 in
  let s = sqrt_I r in
  (acos_I a0, - a1 / s, - a0*a1*a1/(s*r) - a2/s);;

let asinD2 (a0,a1,a2) = 
  let r = one - a0*a0 in
  let s = sqrt_I r in
  (asin_I a0, a1/ s, a0*a1*a1/(s * r) + a2/s);;

let test_sinD2 = 
  let x = (m 1.1,m 1.2,m 1.3) in
  let y = sinD2 x in
  neare3(1.0,0.0,0.0)  (asinD2 y /^^ x);;

let test_cosD2 = 
  let x = (m 1.1,m 1.2,m 1.3) in
  let y = cosD2 x in
  neare3 (1.0,0.0,0.0)  (acosD2 y /^^ x);;

let iD2 x = (x,zero,zero);;

let mk_intervalD2 s = iD2 (mk_interval s);;

let mD2 r = mk_intervalD2(r,r);;

let mkD2 x y = mk_intervalD2(x,y);;

let zeroD2 = mD2 0.0;;

let oneD2 = mD2 1.0;;

let twoD2 = mD2 2.0;;

let fourD2 = mD2 4.0;;

let i16D2 = mD2 16.0;;

(* deprecated let eps_D2 = iD2 eps_I;; *)

let piD2 = iD2 pi_I;;

let pi2D2 = iD2 pi2;;

let twopiD2 = iD2 twopi;;

let ratpiD2 i j = iD2 (ratpi i j);;

let pi15D2 = ratpiD2 1 5;;
let pi25D2 = ratpiD2 2 5;;
let pi35D2 = ratpiD2 3 5;;
let pi45D2 = ratpiD2 4 5;;

let ratD2 i j = iD2(rat i j);;

(* let mpi i j = (ratpi i j);; *)

let kappaD2 = cosD2 pi15D2;;
let sigmaD2 = sinD2 pi15D2;;

let aKD2 = iD2 aK;;

let epso_D2 = aKD2 -^^ ratD2 1237 1000;;

let ups_D2 x1 x2 x3 = 
  twoD2 *^^ 
  (x1 *^^ x2 +^^ x2 *^^ x3 +^^ x3 *^^ x1) -^^ x1*^^ x1 -^^ x2*^^ x2 -^^ x3 *^^ x3;;

let area_D2 y1 y2 y3 = 
  let x1 = y1 *^^ y1 in
  let x2 = y2 *^^ y2 in
  let x3 = y3 *^^ y3 in
    sqrtD2 (ups_D2 x1 x2 x3 ) /^^ fourD2;;

let arcD2 a b cop =
  acosD2 (((a *^^ a) +^^ (b *^^ b) -^^ (cop *^^ cop)) /^^ (twoD2 *^^ a *^^ b));;

let lawsinesD2 a alpha beta gamma = 
  let aa = a /^^ sinD2 alpha in
  (aa *^^ sinD2 beta, aa *^^ cosD2 gamma);;

let lawbetaD2 alpha a b = 
  asinD2 (b *^^ sinD2 alpha /^^ a);;

let locD2 a b theta = 
  let costh = cosD2 theta in
  sqrtD2 (a *^^ a +^^ b *^^ b -^^ twoD2 *^^ a *^^ b *^^ costh);;

let ell_auxD2 h psi = 
  let r = sqrtD2 (h *^^ h +^^ kappaD2 *^^ kappaD2) in
  let theta = acosD2 (h /^^ r) in
  locD2 oneD2 r (psi +^^ theta);;

let ellD2 = 
  let pi310D2 = ratpiD2 3 10 in
  fun x alpha ->
    ell_auxD2 (sigmaD2 -^^ x) (alpha +^^ pi310D2);;

let pinwheeledgeD2 alpha beta xgamma = 
  let gamma = pi15D2 -^^ (alpha +^^ beta) in
  let (xalpha,xbeta) = 
    lawsinesD2 xgamma (pi25D2 -^^ alpha) (pi25D2 -^^ beta) (pi25D2 -^^ gamma) in
  (ellD2 xalpha alpha,ellD2 xbeta beta,ellD2 xgamma gamma);;

let dimer_pinwheeledgeD2 alpha beta xbeta = 
  let dAB,dBC,dAC = pinwheeledgeD2 (pi15D2 -^^ (alpha+^^beta)) alpha xbeta in
  dBC,dAC,dAB;;

(*
let alpha = zeroD2 in
let beta = pi15D2 in
let xbeta = sigmaD2 +^^ (zero,one,zero) in
let (l1,l2,l3) = dimer_pinwheeledgeD2 alpha beta xbeta in
area_D2 l1 l2 l3;;
*)

(* check the convexity of the dimer along the 1param family *)

let one_dimer2 xs = 
  let alphaB = zeroD2 in
  let betaB = pi15D2 in
  let xbetaB = xs in
  let xbetaB = iD2 xbetaB +^^ (zero,one,zero) in
  let alphaD = zeroD2 in
  let edge = dimer_pinwheeledgeD2 in
  try
    let (dBC,dAC,dAB) = edge alphaB betaB xbetaB in
    let aABC = area_D2 dBC dAC dAB in
    let betaD = pi25D2 -^^ betaB in
    let xbetaD = twoD2 *^^ sigmaD2 -^^ xbetaB in
    let (dCD,dAC',dAD) = edge alphaD betaD xbetaD in
    let aADC = area_D2 dCD dAC' dAD in
    let (_,_,deriv2) =     aABC +^^ aADC in
    deriv2 >> zero
  with | Unstable -> false;;

recursetoeps (fun t -> one_dimer2 (hd t)) [[mk (-0.1) (0.1)]];;

(* end of convexity proof *)

end;;
