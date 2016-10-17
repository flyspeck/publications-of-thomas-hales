
(* 
   XX Warning XX: This is a non-working version of interval.
   Nothing is correctly rounded.  
   This should not be used for any serious purposes.
   This is for recreational purposes only.

*)

module Interval = struct

type interval = {low: float; high: float}

let zero_I = {low=0.;high=0.}
let one_I = {low=1.;high=1.}

let print_I x = Printf.printf "[%f, %f] " x.low x.high

let sprintf_I format i = 
  Printf.sprintf "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

let fprintf_I fp format i = 
  Printf.fprintf fp "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

let printf_I format i = 
  Printf.fprintf stdout "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

let is_NaN (x : float) = x <> x

let compare_I_f {low = a; high = b} x =
  if b < x then 1 else if a <= x then 0 else -1

let (<$.) = compare_I_f

let size_I x = x.high -. x.low

let abs_I ({low = a; high = b} as x) =
  if 0. <= a then x
  else if b <= 0. then {low = -.b; high = -.a}
  else {low = 0.; high = max (-.a) b}

let sgn_I {low = a; high = b} =
  {low = float (compare a 0.); high = float (compare b 0.)}

let truncate_I x =
  {low = floor x.low; high = ceil x.high}

let union_I_I x y = {low = min x.low y.low; high = max x.high y.high}

let max_I_I x y = {low = max x.low y.low; high = max x.high y.high}

let min_I_I x y = {low = min x.low y.low; high = min x.high y.high}

let (+$) x y = {low = x.low +. y.low; high = x.high+. y.high}

let (-$) x y = {low = x.low -. y.low; high = x.high-. y.high}

let (+$.) x y = {low = x.low +. y;high = x.high +. y}

let (+.$) x a = a +$. x
  
let (-$.) x a = {low = x.low -. a;high = x.high -. a}

let (-.$) a x = {low = a -. x.high; high = a -. x.low}

let (~-$) {low = a; high = b} = {low = -.b; high = -.a}

let fmul_high x y = x *. y

let fmul_low x y = x *. y

let ( *$) {low = a; high = b} {low = c; high = d} =
  let sa = compare a 0. and sb = compare b 0. in
  let sc = compare c 0. and sd = compare d 0. in
  if (sa = 0 && sb = 0) || (sc = 0 && sd = 0) then {low = 0.; high = 0.}
  else if sb <= 0 then
    if sd <= 0 then {low = fmul_low b d; high = fmul_high a c}
    else if 0 <= sc then {low = fmul_low a d; high = fmul_high b c}
    else {low = fmul_low a d; high = fmul_high a c}
  else if 0 <= sa then
    if sd <= 0 then {low = fmul_low b c; high = fmul_high a d}
    else if 0 <= sc then {low = fmul_low a c; high = fmul_high b d}
    else {low = fmul_low b c; high = fmul_high b d}
  else if 0 <= sc then {low = fmul_low a d; high = fmul_high b d}
  else if sd <= 0 then {low = fmul_low b c; high = fmul_high a c}
  else
    { low = min (fmul_low a d) (fmul_low b c);
      high = max (fmul_high a c) (fmul_high b d) }

let ( *$.) {low = a; high = b} y =
  let sy = compare y 0. in
  if sy = 0 then {low = 0.; high = 0.}
  else if sy < 0 then {low = fmul_low b y; high = fmul_high a y}
  else {low = fmul_low a y; high = fmul_high b y}

let ( *.$) y a = a *$. y

let fdiv_low x y = x /. y

let fdiv_high x y = x /. y

let (/$) {low = a; high = b} {low = c; high = d} =
  let sc = compare c 0. and sd = compare d 0. in
  if sd = 0 then
    if sc = 0 then failwith "/$"
    else if b <= 0. then
      {low = fdiv_low b c; high = if a = 0. then 0. else infinity}
    else if 0. <= a then {low = neg_infinity; high = fdiv_high a c}
    else {low = neg_infinity; high = infinity}
  else if sd < 0 then
    { low = if b <= 0. then fdiv_low b c else fdiv_low b d;
      high = if 0. <= a then fdiv_high a c else fdiv_high a d }
  else if sc = 0 then
    if b <= 0. then
      {low = if a = 0. then 0. else neg_infinity; high = fdiv_high b d}
    else if 0. <= a then {low = fdiv_low a d; high = infinity}
    else {low = neg_infinity; high = infinity}
  else if 0 < sc then
    { low = if a <= 0. then fdiv_low a c else fdiv_low a d;
      high = if b <= 0. then fdiv_high b d else fdiv_high b c }
  else if a = 0. && b = 0. then {low = 0.; high = 0.}
  else {low = neg_infinity; high = infinity}

let (/$.) {low = a; high = b} y =
  let sy = compare y 0. in
  if sy = 0 then failwith "/$."
  else if 0 < sy then {low = fdiv_low a y; high = fdiv_high b y}
  else {low = fdiv_low b y; high = fdiv_high a y}

let (/.$) x {low = a; high = b} =
  let sx = compare x 0. and sa = compare a 0. and sb = compare b 0. in
  if sx = 0 then
    if sa = 0 && sb = 0 then failwith "/.$" else {low = 0.; high = 0.}
  else if 0 < sa || sb < 0 then
    if 0 < sx then {low = fdiv_low x b; high = fdiv_high x a}
    else {low = fdiv_low x a; high = fdiv_high x b}
  else if sa = 0 then
    if sb = 0 then failwith "/.$"
    else if 0 <= sx then {low = fdiv_low x b; high = infinity}
    else {low = neg_infinity; high = fdiv_high x b}
  else if sb = 0 then
    if sx = 0 then {low = 0.; high = 0.}
    else if 0 <= sx then {low = neg_infinity; high = fdiv_high x a}
    else {low = fdiv_low x a; high = infinity}
  else {low = neg_infinity; high = infinity}

let fsub_high x y = x -. y


let inv_I {low = a; high = b} =
  let sa = compare a 0. and sb = compare b 0. in
  if sa = 0 then
    if sb = 0 then failwith "inv_I"
    else {low = fdiv_low 1. b; high = infinity}
  else if 0 < sa || sb < 0 then {low = fdiv_low 1. b; high = fdiv_high 1. a}
  else if sb = 0 then {low = neg_infinity; high = fdiv_high 1. a}
  else {low =  neg_infinity; high = infinity}

let fsqrt_low x = sqrt x

let fsqrt_high x = sqrt x

let sqrt_I {low = a; high = b} =
  if b < 0. then failwith "sqrt_I"
  else {low = if a < 0. then 0. else fsqrt_low a; high = fsqrt_high b}

let (ffloat_low,ffloat_high) = (float_of_int,float_of_int)

let float_i n = {low = ffloat_low n; high = ffloat_high n}

(* to here *)

let pi_I = {low = atan 1.0 *. 4.0; high = atan 1.0 *. 4.0}
let pi2_I = pi_I *$. 2.0
let pio2_I = zero_I


let sgn x =
  let sgn_low = compare x.low 0. and sgn_high = compare x.high 0. in
  if sgn_low <> sgn_high then 0 else sgn_low

let max_63 = ldexp 1. 63

let pr x = {low = x; high = x}

let cos_I x = pr (cos x.low)

let sin_I x = pr (sin x.low)

let (ftan_low,ftan_high) = (tan,tan)

let tan_I {low = a; high = b} =
  if -.max_63 <= a && b <= max_63 && fsub_high b a < pi_I.high then (
    let ta = ftan_low a in
    let tb = ftan_high b in
    if ta <= tb then {low = ta; high = tb}
    else {low = neg_infinity; high = infinity})
  else {low = neg_infinity; high = infinity}

let (facos_low,facos_high) = (acos,acos)

let acos_I {low = a; high = b} =
  if a <= 1. && -1. <= b then
    {low = if b < 1. then facos_low b else 0.;
     high = if -1. < a then facos_high a else pi_I.high}
  else failwith "acos_I"

let (fasin_low,fasin_high) = (asin,asin)

let asin_I {low = a; high = b} =
  if a <= 1. && -1. <= b then
    { low = if -1. < a then fasin_low a else -.pio2_I.high;
      high = if b < 1. then fasin_high b else pio2_I.high }
  else failwith "asin_I"

let (fatan_low,fatan_high) = (atan,atan)

let atan_I x = pr (atan x.low)

end ;;
