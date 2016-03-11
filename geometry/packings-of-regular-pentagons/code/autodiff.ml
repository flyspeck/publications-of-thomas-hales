(* automatic differentiation *)

let ( *^ ) (a0,a1) (b0,b1) = 
  (a0 * b0,a0 *b1 + a1*b0);;

let ( +^ ) (a0,a1) (b0,b1) = 
  (a0+b0,a1+b1);;

let ( -^ ) (a0,a1) (b0,b1) =
  (a0-b0,a1-b1);;

let ( /^ ) (a0,a1) (b0,b1) = 
  (a1*b0 - a0*b1, b1*b1);;

let sinD (a0,a1) = 
  (sin_I a0,cos_I a0 * a1);;

let cosD (a0,a1) = 
  (cos_I a0, - sin_I a0 * a1);;

let 
