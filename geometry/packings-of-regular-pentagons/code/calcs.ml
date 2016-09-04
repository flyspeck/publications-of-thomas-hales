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
