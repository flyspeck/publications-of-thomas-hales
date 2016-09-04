(* automatic differentiation *)

module Autodiff = struct


let ( +^ ) (a0,a1) (b0,b1) = 
  (a0+b0,a1+b1);;

let ( -^ ) (a0,a1) (b0,b1) =
  (a0-b0,a1-b1);;

let test_near eps r x = 
  (x.high <= r +. eps) && (x.low >= r -. eps);;

let test_neare2 (r1,r2) (x1,x2) = 
  (test_near (1.0e-14) r1 x1 && test_near (1.0e-14) r2 x2);;

let test_nearfst f0 g = test_near (1.0e-14) f0.high (fst g);;

let test_nearff f0 g = 
  let (g0,_,_) = g in
  test_near (1.0e-14) f0.high (g0);;

let test_addD = 
  let x = (m 3.0,m 4.0) in
  let y = (m 4.1,m 5.1) in
  test_neare2 (0.0,0.0) (((x +^ y) -^ y) -^ x);;

let ( *^ ) (a0,a1) (b0,b1) = 
  (a0 * b0,a0 *b1 + a1*b0);;

let ( /^ ) (a0,a1) (b0,b1) = 
  (a0/ b0, (a1*b0 - a0*b1) / (b0 * b0));;

let test_multD = 
  let x = (m 3.0,m 4.0) in
  let y = (m 4.1,m 5.1) in
  test_neare2 (1.0,0.0) (((x *^ y) /^ y) /^ x);;

let sqrtD (a0,a1) = 
  (sqrt_I a0, a1 / (two * sqrt_I a0));;

let test_sqrtD = 
  let x = (m 3.0,m 4.0) in
  let y = sqrtD x in
  test_neare2 (1.0,0.0) ((y *^ y) /^ x);;
  
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
  test_neare2 (1.0,0.0) (asinD y /^ x);;

let test_cosD = 
  let x = (m 1.1,m 1.2) in
  let y = cosD x in
  test_neare2 (1.0,0.0)  (acosD y /^ x);;

let iD s = (s,zero);;

let mk_intervalD s = iD (mk_interval s);;

let mD r = mk_intervalD(r,r);;

let mkD x y = mk_intervalD(x,y);;

let zeroD = mD 0.0;;

let oneD = mD 1.0;;

let twoD = mD 2.0;;

let fourD = mD 4.0;;

let i16D = mD 16.0;;

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

let ice_ray_nbd = 1 // 100;;

let epsN_D = aKD -^ ratD 1237 1000;;

let test_epsN_D = 
  test_neare2 (0.0,0.0) (epsN_D -^ iD epsN_I);;

let ups_D x1 x2 x3 = 
  twoD *^ 
  (x1 *^ x2 +^ x2 *^ x3 +^ x3 *^ x1) -^ x1*^ x1 -^ x2*^ x2 -^ x3 *^ x3;;

let test_ups_D = 
  let (x1,x2,x3) = (m 1.1,m 1.2,m 1.3) in
  test_nearfst (ups_I x1 x2 x3) (ups_D (iD x1) (iD x2) (iD x3));;

let area_D y1 y2 y3 = 
  let x1 = y1 *^ y1 in
  let x2 = y2 *^ y2 in
  let x3 = y3 *^ y3 in
    sqrtD (ups_D x1 x2 x3 ) /^ fourD;;

let test_area_D = 
  let (x1,x2,x3) = (m 1.1,m 1.2,m 1.3) in
  test_nearfst (area_I x1 x2 x3) (area_D (iD x1) (iD x2) (iD x3));;

let arcD a b cop =
  acosD (((a *^ a) +^ (b *^ b) -^ (cop *^ cop)) /^ (twoD *^ a *^ b));;

let test_arcD = 
  let (a,b,c) = (m 1.1,m 1.2,m 1.3) in
  test_nearfst (iarc a b c) (arcD (iD a) (iD b) (iD c));;

let lawsinesD a alpha beta gamma = 
  let aa = a /^ sinD alpha in
  (aa *^ sinD beta, aa *^ sinD gamma);;

let test_lawsinesD =
  let (a,alpha,beta,gamma) = (m 1.05,m 1.1,m 1.2,m 1.3) in
  let (aD,alphaD,betaD,gammaD) = (iD a,iD alpha,iD beta,iD gamma) in
  test_nearfst (fst(lawsines a alpha beta gamma)) 
    (fst(lawsinesD aD alphaD betaD gammaD)) &&
  test_nearfst (snd(lawsines a alpha beta gamma)) 
    (snd(lawsinesD aD alphaD betaD gammaD));;

let locD a b theta = 
  let costh = cosD theta in
  sqrtD (a *^ a +^ b *^ b -^ twoD *^ a *^ b *^ costh);;

let test_locD = 
  let (a,b,theta) = (m 1.1,m 1.2,m 1.3) in
  let (aD,bD,thetaD) = (iD a,iD b,iD theta) in
  test_nearfst (iloc a b theta) (locD aD bD thetaD);;

let ell_auxD h psi = 
  let r = sqrtD (h *^ h +^ kappaD *^ kappaD) in
  let theta = acosD (h /^ r) in
  locD oneD r (psi +^ theta);;

let ellD = 
  let pi310D = ratpiD 3 10 in
  fun x alpha ->
    ell_auxD (sigmaD -^ x) (alpha +^ pi310D);;

let test_ellD =
  let (x,alpha) = (m 0.5,m 0.6) in
  let (xD,alphaD) = (iD x,iD alpha) in
  test_nearfst (ellx x alpha) (ellD xD alphaD);;

let pinwheeledgeD alpha beta xgamma = 
  let gamma = pi15D -^ (alpha +^ beta) in
  let (xalpha,xbeta) = 
    lawsinesD xgamma (pi25D -^ alpha) (pi25D -^ beta) (pi25D -^ gamma) in
  (ellD xalpha alpha,ellD xbeta beta,ellD xgamma gamma);;

let test_nearedge a b = 
  let (a1,a2,a3) = a in
  let (b1,b2,b3) = b in
  test_nearfst a1 b1 &&
    test_nearfst a2 b2 &&
    test_nearfst a3 b3;;

let test_pinwheeledgeD =
  let (alpha,beta,xgamma) = (m 0.1,m 0.2, m 0.3) in
  let (alphaD,betaD,xgammaD)= (iD alpha,iD beta,iD xgamma) in
   test_nearedge (pinwheeledge alpha beta xgamma)
    (pinwheeledgeD alphaD betaD xgammaD);;

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

let test_ljedgeD = 
  let (alpha,beta,xalpha) = (m 0.4,m 0.25, m 0.3) in
  let (alphaD,betaD,xalphaD)= (iD alpha,iD beta,iD xalpha) in
  test_nearedge    (ljedge alpha beta xalpha)
    (ljedgeD alphaD betaD xalphaD);;

let shared_pinwheeledgeD alpha beta xbeta = 
  let gamma = (pi15D -^ (alpha+^beta)) in
  let dAB,dBC,dAC = pinwheeledgeD gamma alpha xbeta in
  dBC,dAC,dAB;;

let test_shared_pinwheeledgeD = 
  let (alpha,beta,xbeta) = (m 0.1,m 0.2,m 0.3) in
  let (alphaD,betaD,xbetaD) = (iD alpha,iD beta,iD xbeta) in
  test_nearedge (shared_pinwheeledge alpha beta xbeta)
    (shared_pinwheeledgeD alphaD betaD xbetaD);;

let shared_lj1edge_extendedD =
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

let shared_lj1edgeD alpha' beta xbeta = 
  let l1,l2,l3,_,_ = shared_lj1edge_extendedD alpha' beta xbeta in
  l1,l2,l3;;

let test_shared_lj1edgeD = 
  let (alpha',beta,xbeta) = (m 0.1,m 0.2,m 0.3) in
  let (alphaD',betaD,xbetaD) = (iD alpha',iD beta,iD xbeta) in
  test_nearedge (shared_lj1edge alpha' beta xbeta)
    (shared_lj1edgeD alphaD' betaD xbetaD);;

let shared_lj2edgeD alpha beta xbeta =
  let (dAC,dBC,dAB) = ljedgeD beta alpha xbeta in
  dBC,dAC,dAB;;

let shared_lj2edge_extendedD alpha beta xbeta = 
  let t,(dAC,dBC,dAB) = ljedge_extendedD beta alpha xbeta in
  dBC,dAC,dAB,t;;

let test_shared_lj2edgeD = 
  let (alpha,beta,xbeta) = (m 0.45,m 0.2,m 0.3) in
  let (alphaD,betaD,xbetaD) = (iD alpha,iD beta,iD xbeta) in
  test_nearedge (shared_lj2edge alpha beta xbeta)
    (shared_lj2edgeD alphaD betaD xbetaD);;

let shared_tj3edgeD alpha' beta xbeta = 
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

let test_shared_tj3edgeD = 
  let (alpha',beta,xbeta) = (m 0.1,m 0.2,m 0.3) in
  let (alphaD',betaD,xbetaD) = (iD alpha',iD beta,iD xbeta) in
  test_nearedge (shared_tj3edge alpha' beta xbeta)
    (shared_tj3edgeD alphaD' betaD xbetaD);;


(* linear motion from given values to pentagonal ice-ray critical values *)


let one_twist_claim_lj1 xs =
  let ([alpha';beta;xbeta],_) = xs in
  if outdomfn_shared_lj1 alpha' beta xbeta then true
  else 
    try
        let (_,_,_,xa,_) = shared_lj1edge_extended alpha' beta xbeta in
        (xa >> sigma)
    with Unstable -> false;;

let dummybool = Dimer.dummybool;;

let twist_claim_lj1 =
  let ee = merge_I (- ice_ray_nbd) (ice_ray_nbd) in
  (* mk (-0.01) (0.01) *)
  let eps_domain =[[zero2 (m 0.01);pi15 + ee;sigma+ee]] in
  recursepairtoeps one_twist_claim_lj1 (dummybool eps_domain);;

let one_twist_claim_lj2 xs = 
  try
    let ([alpha;xbeta],_) = xs in
    let beta_t = (pi15,zero) in
    let alpha_t = (alpha,- one) in
    let xbeta_t = (xbeta,zero) in
    let (l1,l2,l3) = shared_lj2edgeD alpha_t beta_t xbeta_t in
    let (_,a') = area_D l1 l2 l3 in
      (a' << zero)
    with Unstable -> false;;

let twist_claim_lj2 =
  let ee = merge_I (- ice_ray_nbd) (ice_ray_nbd) in
(*  let ee = mk (-0.01) (0.01) in *)
  let eps_domain =[[zero2 ice_ray_nbd;sigma+ee]] in
  recursepairtoeps one_twist_claim_lj2 (dummybool eps_domain);;

(* coordinates should be such that
   the pentagonal ice-ray always has
   alphaB=0, betaB=pi15, xbetaB=sigma, alphaD=0.

   Shared variables are (xbetaB,betaB), (xbetaD,betaD).

   In particular, betaB is the angle along shared edge AC.

   The letter D is used to indicate 1-jet variables (f,f').
   The pentagons are also labeled A,B,C,D, which causes some
   ambiguity in notation.  For example, in alphaD, the D stands
   for pentagon D, rather than a 1-jet variable.

   B should have betaB < pi15 and increasing.
   D should have betaD > pi15 and decreasing.

*)

let one_dimerD xs = 
  let ([alphaB;betaB;xbetaB;alphaD],
       ((sB,edgeB,curveB,_),(sD,edgeD,curveD,_))) = xs in
  try
    (* subcritical triangle ABC: *)
    let alphaB_s = curveB alphaB in
    let betaB_s = (betaB,one) in
    let (dBC,dAC,dAB) = edgeB alphaB_s betaB_s (iD xbetaB) in
    let aABC = area_D dBC dAC dAB in
      (* second triangle ADC of dimer: *)
    let betaD = pi25 - betaB in
    let xbetaD = two * sigma - xbetaB in
    let alphaD_s = curveD alphaD in
    let betaD_s = (betaD,-one) in
    let (dCD,dAC',dAD) = edgeD alphaD_s betaD_s (iD xbetaD) in
    let aADC = area_D dCD dAC' dAD in
    let (_,area_derivative) = aABC +^ aADC in
    area_derivative << zero  
  with | Unstable -> false;;

let i_m1 alpha = (alpha,-one);;

(* true if i_m1, false if iD *)

let dimerD_toptypes = [
  ("pinw_apos",shared_pinwheeledgeD,i_m1,true);
  ("pinw_a0",shared_pinwheeledgeD,iD,false);
  ("lj1top_apos",shared_lj1edgeD,i_m1,true);
  ("lj1top_a0",shared_lj1edgeD,iD,false);
  ("lj2top",shared_lj2edgeD,i_m1,true);];;

let dimerD_bottypes = [
  ("lj1bot",shared_lj1edgeD,i_m1,true);
  ("lj2bot_apos",shared_lj2edgeD,i_m1,true);
  ("lj2bot_a0",shared_lj2edgeD,iD,false);
  ("tj3bot_apos",shared_tj3edgeD,i_m1,true);
  ("tj3bot_a0",shared_tj3edgeD,iD,false);
];;

let dimerD_domain (i,j) = 
  let top = List.nth dimerD_toptypes i in
  let (_,_,_,topw) = top in
  let bottom  =  List.nth dimerD_bottypes j in
  let (_,_,_,bottomw) = bottom in
  let eps = zero2 (ice_ray_nbd) in
  let epstop = if topw then eps else zero in
  let epsbottom = if bottomw then eps else zero in
  let alphaBdomain = merge_I (pi15 - eps) pi15 in
  ([epstop;alphaBdomain;sigma+eps-eps;epsbottom]),
  (top,bottom);;

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
map (recurseD 0) (0--4);;
map (recurseD 1) (0--4);;
map (recurseD 2) (0--4);;
map (recurseD 3) (0--4);;
map (recurseD 4) (0--4);;


(* end of first derivatives *)


(* ********************************************************************** *)
(* start second derivatives *)
(* ********************************************************************** *)


let test_neare3 (r1,r2,r3) (x1,x2,x3) = 
  let e = 1.0e-12 in
  (test_near e r1 x1 && test_near e r2 x2) && test_near e r3 x3;;

let ( +^^ ) (a0,a1,a2) (b0,b1,b2) = 
  (a0+b0,a1+b1,a2+b2);;

let ( -^^ ) (a0,a1,a2) (b0,b1,b2) =
  (a0-b0,a1-b1,a2-b2);;

let test_addD2 = 
  let x = (m 3.0,m 4.0,m 4.3) in
  let y = (m 4.1,m 5.1,m 5.3) in
  test_neare3 (0.0,0.0,0.0) (((x +^^ y) -^^ y) -^^ x);;

let ( *^^ ) (a0,a1,a2) (b0,b1,b2) = 
  (a0 * b0,a0 *b1 + a1*b0,a2*b0 + two*a1*b1 + a0*b2);;

let ( /^^ ) (a0,a1,a2) (b0,b1,b2) = 
  let d1 = (a1*b0 - a0*b1) / (b0 * b0) in
  (a0/ b0, d1,
   (a2*b0-a0*b2)/(b0*b0) - two*b1*d1/ b0);;

let test_multD = 
  let x = (m 3.0,m 4.0,m 4.3) in
  let y = (m 4.1,m 5.1,m 5.3) in
  test_neare3 (1.0,0.0,0.0) (((x *^^ y) /^^ y) /^^ x);;

let sqrtD2 (a0,a1,a2) = 
  let s = sqrt_I a0 in
  (s,a1 /(two*s), - a1*a1/(four*s*s*s) + a2/(two* s));;

let test_sqrtD2 = 
  let x = (m 3.0,m 4.0,m 4.2) in
  let y = sqrtD2 x in
  test_neare3 (1.0,0.0,0.0) ((y *^^ y) /^^ x);;

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
  test_neare3(1.0,0.0,0.0)  (asinD2 y /^^ x);;

let test_cosD2 = 
  let x = (m 1.1,m 1.2,m 1.3) in
  let y = cosD2 x in
  test_neare3 (1.0,0.0,0.0)  (acosD2 y /^^ x);;

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

let epsN_D2 = aKD2 -^^ ratD2 1237 1000;;

let ups_D2 x1 x2 x3 = 
  twoD2 *^^ 
  (x1 *^^ x2 +^^ x2 *^^ x3 +^^ x3 *^^ x1) -^^ x1*^^ x1 -^^ x2*^^ x2 -^^ x3 *^^ x3;;

let test_ups_D2 = 
  let (x1,x2,x3) = (m 1.0,m 1.1,m 1.2) in
  let (x1D,x2D,x3D) = (iD2 x1,iD2 x2,iD2 x3) in
  test_nearff (ups_I x1 x2 x3) (ups_D2 x1D x2D x3D);;

let area_D2 y1 y2 y3 = 
  let x1 = y1 *^^ y1 in
  let x2 = y2 *^^ y2 in
  let x3 = y3 *^^ y3 in
    sqrtD2 (ups_D2 x1 x2 x3 ) /^^ fourD2;;

let test_area_D2 = 
  let (x1,x2,x3) = (m 1.0,m 1.1,m 1.2) in
  let (x1D,x2D,x3D) = (iD2 x1,iD2 x2,iD2 x3) in
  test_nearff (area_I x1 x2 x3) (area_D2 x1D x2D x3D);;

let arcD2 a b cop =
  acosD2 (((a *^^ a) +^^ (b *^^ b) -^^ (cop *^^ cop)) 
	  /^^ (twoD2 *^^ a *^^ b));;

let test_arcD2 = 
  let (x1,x2,x3) = (m 1.0,m 1.1,m 1.2) in
  let (x1D,x2D,x3D) = (iD2 x1,iD2 x2,iD2 x3) in
  test_nearff (iarc x1 x2 x3) (arcD2 x1D x2D x3D);;

let lawsinesD2 a alpha beta gamma = 
  let aa = a /^^ sinD2 alpha in
  (aa *^^ sinD2 beta, aa *^^ sinD2 gamma);;

let test_lawsinesD2 = 
  let (x1,x2,x3,x4) = (m 1.0,m 1.1,m 1.2,m 1.3) in
  let (x1D,x2D,x3D,x4D) = (iD2 x1,iD2 x2,iD2 x3,iD2 x4) in
  let (s1,s2),(s1D,s2D)= ((lawsines x1 x2 x3 x4), 
			  (lawsinesD2 x1D x2D x3D x4D)) in
  test_nearff s1 s1D && test_nearff s2 s2D;;

let locD2 a b theta = 
  let costh = cosD2 theta in
  sqrtD2 (a *^^ a +^^ b *^^ b -^^ twoD2 *^^ a *^^ b *^^ costh);;

let test_locD2 = 
  let (x1,x2,x3) = (m 1.0,m 1.1,m 1.2) in
  let (x1D,x2D,x3D) = (iD2 x1,iD2 x2,iD2 x3) in
  test_nearff (iloc x1 x2 x3) (locD2 x1D x2D x3D);;

let ell_auxD2 h psi = 
  let r = sqrtD2 (h *^^ h +^^ kappaD2 *^^ kappaD2) in
  let theta = acosD2 (h /^^ r) in
  locD2 oneD2 r (psi +^^ theta);;

let ellD2 = 
  let pi310D2 = ratpiD2 3 10 in
  fun x alpha ->
    ell_auxD2 (sigmaD2 -^^ x) (alpha +^^ pi310D2);;

let test_ellD2 = 
  let (x1,x2) = (m 0.3,m 0.4) in 
  let (x1D,x2D) = (iD2 x1,iD2 x2) in
  test_nearff (ellx x1 x2) (ellD2 x1D x2D);;

let pinwheeledgeD2 alpha beta xgamma = 
  let gamma = pi15D2 -^^ (alpha +^^ beta) in
  let (xalpha,xbeta) = 
    lawsinesD2 xgamma (pi25D2 -^^ alpha) 
      (pi25D2 -^^ beta) (pi25D2 -^^ gamma) in
  (ellD2 xalpha alpha,ellD2 xbeta beta,ellD2 xgamma gamma);;

let test_nearedgeD2 a b = 
  let (a1,a2,a3) = a in
  let (b1,b2,b3) = b in
  test_nearff a1 b1 &&
    test_nearff a2 b2 &&
    test_nearff a3 b3;;

let test_pinwheeledgeD2 = 
  let (x1,x2,x3) = (m 0.3,m 0.4,m 0.5) in
  let (x1D,x2D,x3D) = (iD2 x1,iD2 x2,iD2 x3) in
  test_nearedgeD2 (pinwheeledge x1 x2 x3) (pinwheeledgeD2 x1D x2D x3D);;


let shared_pinwheeledgeD2 alpha beta xbeta = 
  let dAB,dBC,dAC = pinwheeledgeD2 (pi15D2 -^^ (alpha+^^beta)) alpha xbeta in
  dBC,dAC,dAB;;

let test_shared_pinwheeledgeD2 = 
  let (x1,x2,x3) = (m 0.3,m 0.4,m 0.5) in
  let (x1D,x2D,x3D) = (iD2 x1,iD2 x2,iD2 x3) in
  test_nearedgeD2 (shared_pinwheeledge x1 x2 x3) 
    (shared_pinwheeledgeD2 x1D x2D x3D);;


(* check the convexity of the dimer along the 1param family *)

let one_dimer2 xs = 
  let alphaB = zeroD2 in
  let betaB = pi15D2 in
  let xbetaB = xs in
  let xbetaB = iD2 xbetaB +^^ (zero,one,zero) in
  let alphaD = zeroD2 in
  let edge = shared_pinwheeledgeD2 in
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

(* we only need 0.01.  We go much further than needed here *)

recursetoeps (fun t -> one_dimer2 (hd t)) [[mk (-0.1) (0.1)]];;

(* end of convexity proof *)

end;;
