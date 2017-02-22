(* Generalities *)

(* summary *)
Id[x_] := x;
I2 = {{1, 0}, {0, 1}};
J = {{0, -1}, {1, 0}};
A2 = {{a, b}, {c, -a}}; (* X *)

frac[{{a_, b_}, {c_, d_}}, z_] := (a z + b) / (c z + d);
Cx[{x_, y_}] := x + I y;

Ctimes[{x1_, y1_}, {x2_, y2_}] :=
  {(x1 x2 - y1 y2), (x1 y2 + y1 x2)};
todisk[z_] := (z - I)/(z + I);

Tx = Transpose;
Lie[X_, Y_] := X.Y - Y.X;
R1  = {{1/2, Sqrt[3]/2}, {-Sqrt[3]/2, 1/2}};
R = Tx[R1];
powR[i_] := {{Cos[i Pi/3], -Sin[i Pi/3]}, {Sin[i Pi/3], 
    Cos[i Pi/3]}};
ExpJt = {{Cos[t], -Sin[t]}, {Sin[t], Cos[t]}};

v0 = {1, 0}; v1 = R.v0; v2 = R.v1; v3 = R.v2; v4 = R.v3; v5 = 
 R.v4; R.v5;

Clear[conj, real, imag, Reps];
test =  Module[{z, conj, real, imag, u},
   conj[u_] := u /; Head[u] == Symbol;
   conj[u_] := u /; Head[u] == Integer;
   conj[Rational[a_, b_]] := Rational[a, b];
   conj[a_Real] := a;
   conj[Power[a_, b_]] := Power[conj[a], b];
   conj[Plus[a_, b_]] := Plus[conj[a], conj[b]];
   conj[Times[a_, b_]] := Times[conj[a], conj[b]];
   conj[Complex[a_, b_]] := Complex[a, -b];
   z = frac[{{a, b}, {c, d}}, Cx[{x, y}]];
   real = (conj[z] + z)/2;
   imag = (z - conj[z])/(2 I);
    {real, imag} // Simplify // InputForm
   ];

(*Reps[frac[{{a,b},{c,d}},Cx[{x,y}]]]//InputForm;*)

Repfrac[{{a_, b_}, {c_, d_}}, {x_, 
    y_}] := {(b*(d + c*x) + a*(d*x + c*(x^2 + y^2)))/(d^2 + 2*c*d*x + 
      c^2*(x^2 + y^2)), (-(b*c*y) + a*d*y)/(d^2 + 2*c*d*x + 
      c^2*(x^2 + y^2))};

polyapprox[f_, n_] := 
  Apply[Plus, Table[t^i SeriesCoefficient[f, {t, 0, i}], {i, 0, n}]];

adjoint[h_] := -{D[h, x], D[h, y]} // Simplify;

(* hyperbolic plane, state eqn. *)

Xupper = {{x/y, -x^2/y - y}, {1/y, -x/y}};
(* upper half-plane *)
zofX[X_] := Module[{x, y},
   y = 1/X[[2, 1]] // Simplify;
   x = y *X[[1, 1]] // Simplify;
   {x, y}];

(* get a basis of sl2 from Xupper and its derivatives *)

Module[{stdbasis},
  stdbasis[X_] := 
   {(X[[1, 1]] - X[[2, 2]])/2, X[[1, 2]], X[[2, 1]]};
  Det[{stdbasis[Xupper], stdbasis[D[Xupper, x]], 
    stdbasis[D[Xupper, y]]}]];

{Det[Xupper], Tr[Xupper.Xupper]} // Simplify;
UpperHalfODE = Module[{Yhh, Dhh, rhh, xh, yh, t, Dx, Dy, xsub, Dxsub}, 
  Yhh = Xupper /. {x -> xh[t], y -> yh[t]};
  xsub = {xh[t] -> x, yh[t] -> y};
  Dxsub = {xh'[t] -> Dx, yh'[t] -> Dy};
  Dhh = (D[Yhh, t] /. Dxsub) /. xsub;
  rhh = -2/Tr[A2.Xupper];
  {Dx, Dy} /. 
     Solve[Dhh == (Xupper .(rhh (A2) - Xupper)), {Dx, Dy}][[1]] /. 
    xsub // Factor]

(* general payoff function *)
Clear[Hpayoff];
Hampayoff = lambda0 (3/2) (x^2 + y^2 + 1)/y;
adjoint[Hampayoff];

(* general upper-half function *)

Hupper = {lambda1, lambda2}.UpperHalfODE ;
HamLie = Tr[{{aL, bL}, {cL, -aL}}.Xupper];
Hamiltonian = Hupper + Hampayoff + HamLie // Simplify;

(* switching set, bang-bang *)

z001sub = {a -> -1/Sqrt[3], b -> -2/3, c -> 0};
z010sub = {a -> 1/Sqrt[3], b -> -2/3, c -> 0};
z100sub = {a -> 0, b -> 1/3, c -> 1};
z011sub = {a -> -m, b -> -2/3, c -> 0};
Zsub = {a -> (u1 - u2)/Sqrt[3], b -> u0/3 - 2 u1/3 - 2 u2/3, c -> u0};

u001sub = {u0 -> 0, u1 -> 0, u2 -> 1};
u010sub = {u0 -> 0, u1 -> 1, u2 -> 0};
u100sub = {u0 -> 1, u1 -> 0, u2 -> 0};

m001sub = {m -> 1/Sqrt[3]};
m010sub = {m -> -1/Sqrt[3]};

Rm001 = 1/2 {{1, -1/m}, {1/m, 1}};
test = (Rm001 /. m001sub) - R;

(*
switch32=(Hupper/.z001sub)-(Hupper/.z010sub)//Simplify;
switch12 = (Hupper/.z100sub)-(Hupper/.z010sub)//Simplify;
switch13 = (Hupper/.z100sub)-(Hupper/.z001sub)//Simplify;
*)
switch[i_, j_] := Module[{zsub},
   zsub = {z100sub, z010sub, 
     z001sub}; (Hupper /. zsub[[i]]) - (Hupper /. zsub[[j]]) // 
    Simplify];

switch32 = switch[3, 2];
switch12 = switch[1, 2];
switch13 = switch[1, 3];

(* Bang - Bang 001,010 *)

(* 001,010 bang-bang sol of state eqn *)

Clear[alpha, u, c0, msub, hamc];
xy011sub = {x -> -m + c0 u, y -> c0 alpha u};
(* x0y0sub= *)

c0alpha011sub = 
  Solve[({x, y} /. (xy011sub /. u -> 1)) == {x0, y0}, {c0, alpha}][[
   1]];
usub = {u -> E^(alpha t)};

(* state eqn, hyperbolic term
 has an obvious solution,
x = -m + c u, y = c alpha u, where
u = E^(alpha t) ;
  m= b/(2a)  *)

(* state eqn, Lie part *)

StateSolG = Module[{G2, XXh, eqnn, eqn, gsol, a, b, d, c, i, j},
   G2 = {{a[u], b[u]}, {c[u], d[u]}};
   XXh = (Xupper/(alpha u)) /. xy011sub // Factor;
   eqnn = {D[G2, u], G2.XXh} // Simplify;
   eqn[i_, j_] := eqnn[[1, i, j]] == eqnn[[2, i, j]];
   {{a[u], b[u]}, {c[u], d[u]}} /. 
    DSolve[{eqn[1, 1], eqn[1, 2], eqn[2, 1], eqn[2, 2], a[1] == 1, 
       b[1] == 0, c[1] == 0, d[1] == 1}, {a, b, c, d}, u][[1]]];
(StateSolG - I2) alpha^2 c0 u/(u - 1) // Factor;
Det[StateSolG] // Simplify

(* cost *)
cost011 = (3/2) Integrate[(x^2 + y^2 + 1)/y /. xy011sub /. 
     usub, {t, 0, t1}];

costTransform = 
 Module[{Rt, x1, y1},
  Rt = {{a, b}, {-b, a}};
  {x1, y1} = Repfrac[Rt, {x, y}];
  (x1^2 + y1^2 + 1)/y1 // Simplify]
 
 (* adjoint solution: Lie term 001,010 *)

AdjointSolLie011 = Module[{Ytt, Rs, Cs, eqns, a1, a2, a3},
   Ytt = Xupper /. xy011sub;
   Rs = {{a1[u], a2[u]}, {a3[u], -a1[u]}};
   Cs = (Rs.Ytt - Ytt .Rs)/(alpha u) // Simplify;
   eqns[i_, j_] := D[Rs, u][[i, j]] == Cs[[i, j]];
   (* Rs/. *)
   Rs /. DSolve[{eqns[1, 1], eqns[1, 2], eqns[2, 1]}, {a1, a2, a3}, 
      u][[1]]];

(* How C[1],C[2],C[3] 
relate to initial {{aL,bL},{cL,-aL}} *)

AdjointSolLie011Init = AdjointSolLie011 /. {u -> 1};

(* solve ODE 001, 010, main term *)


HamLie011 = Tr[AdjointSolLie011.Xupper] // Simplify;

UpperHalfODE /. {c -> 0} // Simplify;
Hupper011 = lambda1 y + lambda2 y^2/(m + x);
Hamiltonian011 = 
  Hupper011 + Hampayoff + HamLie011 /. xy011sub // Simplify;

AdjointODE011 = 
  adjoint[HamLie011] + adjoint[Hampayoff] + adjoint[Hupper011] /. 
    xy011sub // Simplify;


 
AdjointSol011 = Module[{adj},
   adj = AdjointODE011 /. {lambda1 -> lambda1[t], 
       lambda2 -> lambda2[t]} /. usub; {lambda1[t], lambda2[t]} /. 
     DSolve[{lambda1'[t] == adj[[1]], 
        lambda2'[t] == adj[[2]]}, {lambda1, lambda2}, t][[1]] // 
    Simplify];


ham011c = 
  Hamiltonian011 /. {lambda1 -> AdjointSol011[[1]], 
       lambda2 -> AdjointSol011[[2]]} /. usub // Simplify // Factor;

  
(* Rotate solution by arbitrary rotation matrix *)

(* Rt is an arbitary rotation matrix.  We compute rotated {lambda1, lambda2} viewed in the cotangent space at Rt.z.  N.B. not at z.  We check it satisfies the appropriate rotated ODE. *)

Clear[Rt, aLbar, bLbar, cLbar, junk, a, b, c, aL, bL, cL, zbar, fbar, 
  blam, Dblam, DblamODE];

(* general rotation *)
Rt = {{aR, bR}, {-bR, aR}};
(* Lambda transform *)
{{aLbar, bLbar}, {cLbar, junk}} = 
  Rt.{{aL, bL}, {cL, -aL}}.Inverse[Rt];
(* Z0 transform *)
{{aZ0bar, bZ0bar}, {cZ0bar, junk}} =
  Rt.{{a, b}, {c, -a}}.Inverse[Rt];

(* z={x,y}, f={f1,f2} transform *)
{zbar, fbar} = 
  Module[{z, zb, fb, sub},
   sub = {x'[0] -> f1, y'[0] -> f2, x[0] -> x, y[0] -> y};
   z = {x[t], y[t]};
   fb = D[Repfrac[Rt, z], t];
   zb = Repfrac[Rt, z];
   {zb, fb} /. t -> 0 /. sub // Simplify
   ];
(* {lambda1,lambda2} transform *)
blam = Module[{blam1, blam2},
    {blam1, blam2} /. 
     Solve[({blam1, blam2}.fbar == {lam1, lam2}.{f1, 
           f2}) /. {f1 -> {1, 0}, f2 -> {0, 1}}, {blam1, blam2}]][[
   1]] // Simplify

test = blam.fbar // Simplify

Dblam = Module[{vv},
   vv = D[(blam /. {lam1 -> lam1[t], lam2 -> lam2[t], x -> x[t], 
        y -> y[t]}), t]; 
   vv /. {x'[t] -> UpperHalfODE[[1]], y'[t] -> UpperHalfODE[[2]], 
      x[t] -> x, y[t] -> y, lam1'[t] -> -D[Hamiltonian, x], 
      lam2'[t] -> -D[Hamiltonian, y],
      lam1[t] -> lambda1,
      lam2[t] -> lambda2} // Simplify
   ];

DblamODE = 
  Module[{Hambar, vv, xB, yB, aB, bB, cB, laB1, laB2, aLB, bLB, cLB},
   Hambar = 
    Hamiltonian /. {x -> xB, y -> yB, lambda1 -> laB1, 
      lambda2 -> laB2, aL -> aLB, bL -> bLB, cL -> cLB, a -> aB, 
      b -> bB, c -> cB};
   vv = -{D[Hambar, xB], D[Hambar, yB]} // Simplify;
   vv /. {xB -> zbar[[1]], yB -> zbar[[2]], laB1 -> blam[[1]], 
       laB2 -> blam[[2]], aB -> aZ0bar, bB -> bZ0bar, cB -> cZ0bar, 
       aLB -> aLbar, bLB -> bLbar, cLB -> cLbar} /. {lam1 -> lambda1, 
      lam2 -> lambda2} // Simplify
   ];
Dblam - DblamODE // Simplify

(* Fillipov *)

(* Filippov *)
(* vertices distinct *)

test = (UpperHalfODE /. z001sub) - (UpperHalfODE /. z010sub) // 
    Together // Simplify;
(* fixed sign *)
test = Module[{p1, p2, rssub},
  p1 = (UpperHalfODE /. z001sub) // Simplify;
  p2 = (UpperHalfODE /. z010sub) // Simplify;
  rssub = 
   Solve[{{r, s}.  p1 == 1, {r, s}.p2 == 1}, {r, s}][[1]] // 
    Simplify;
  UpperHalfODE.{r, s} - 1 /. Zsub /. rssub /. {u0 -> 1 - u1 - u2} // 
   Simplify 
  ]

(* Smoothed Octagon 001 Parameters *)

(* smoothed octagon state eqns *)



Clear[a, b, c, d, tc, sc, cx, fj, s, ggt, t1, Ts];

(* This entire section is summarized by the constants: cmoctsub, \
alphaoctsub, tmaxoct *)

cmoctsub = {c0 -> 1/Sqrt[3], m -> 1/Sqrt[3]};
alphaoctsub = {alpha -> Sqrt[(2 Sqrt[2] - 1)]};
tmaxoct = (1/(2 alpha)) Log[2] /. alphaoctsub;
umaxoct = {u -> Sqrt[2]};

(* curve in SL2, unnormalized t1 *)

goct1 = Module[{G2, u0, u2, a, b, c, d, gt, gamma0, gamma2, strel, dd,
     ssub, s0},
   s0 = 1 - 1/Sqrt[2];
   G2 = {{a, b}, {c, d}};
   u0 = {1, 0}; u2 = {-1/2, Sqrt[3]/2};
   gamma0 :=  {1, 0} + {0, t1};
   gamma2 := {-1/Sqrt[2], 
      1/Sqrt[2]} +  {-1/Sqrt[2], -1/Sqrt[2]} (s - s0);
   dd = Det[{gamma0, gamma2}];
   strel = (dd - (dd /. {s -> 0, t1 -> 0}));
   ssub = Solve[strel == 0, s][[1]];
   G2 /. Solve[
       G2.Tx[{u0, u2}] == Tx[({gamma0, gamma2}) /. ssub], {a, b, c, 
        d}][[1]] // Factor
   ];

smoothedoctdensity = 
  8 Sqrt[3] (8 - 8 Sqrt[2] + Sqrt[2] Log[2])/(4 (-4 + Sqrt[2]))/
    Sqrt[12];

test = Module[{Yt1, IYt1},
   Yt1 = Inverse[goct1].D[goct1, t1] // Simplify;
   {"Yt1", Tr[Yt1], Det[Yt1]} // Simplify;
   (* payoff *)
   
   IYt1 = (-3/2) Integrate[Yt1[[1, 2]] - Yt1[[2, 1]], {t1, 0, s0}];
   (* from paper *)
   
   {4 IYt1/Sqrt[12], smoothedoctdensity} // N
   ];


(*"Xoct" unit speed *)
goct = Module[{t1sub},
   t1sub = {t1 -> 1 - E^(-alpha t)};
   goct1 /. t1sub // Simplify];



Xoct = Inverse[goct].D[goct, t] // Simplify;

(* tests *)
Xoct + Inverse[Xoct].D[Xoct, t] // Simplify;
({"Xoct", Tr[Xoct], Det[Xoct]} // Simplify) /. alphaoctsub;
{"X terminal", Module[{Xoct0, XoctfN},
     Xoct0 = Xoct /. {t -> 0} /. alphaoctsub;
     XoctfN = (Xoct /. {t -> tmaxoct}) /. alphaoctsub;
     R1.Xoct0.Tx[R1] - XoctfN] // Simplify} // N;

Module[{IXoct},
   IXoct = (-3/2) Integrate[(Xoct[[1, 2]] - Xoct[[2, 1]]) /. 
       alphaoctsub, {t, 0, tmaxoct}];
   {4 IXoct/Sqrt[12], smoothedoctdensity} // Simplify] // N;


zoctupper = zofX[Xoct];
(* zoctupper1= Module[{xxt,yyt},
yyt = 1/Xoct[[2,1]]//Simplify;
xxt = yyt Xoct[[1,1]]//Simplify;
{xxt,yyt}];

test = zoctupper1-zoctupper//Simplify; *)

{"{x,y}", zoctupper};
4 Module[{Iz, xxt, yyt},
   {xxt, yyt} = zoctupper;
   Iz =  (3/2) NIntegrate[(xxt^2 + yyt^2 + 1)/yyt /. alphaoctsub, {t, 
       0, tmaxoct}]];

(* compare with ODE solution. *)


test = zoctupper - {x, y} /. xy011sub /. cmoctsub /. usub /. 
    alphaoctsub /. {t -> Random[]} // N
test = Sqrt[2] - E^(alpha tmaxoct) /. alphaoctsub;

(* Smoothed Octagon Transversality *)

(* We show that transversality holds on a shorter period : 1/4 the time it takes to complete the hexameral domain. *)

(* Transversality reprise *)
R1sub  = {aR -> 1/2, bR -> Sqrt[3]/2};

{"det constant-extra degree of freedom", 
  Det[AdjointSolLie011] // Simplify};

(* terminal condition upper half plane state *)

checkTransverseState001 = Module[{},
   (frac[R1, Cx[zoctupper]] /. {t -> 0}) - (Cx[
         zoctupper] /. {t -> tmaxoct}) /. alphaoctsub // Simplify];

(* solve for initial conditions. Lie sector transversality. *)

c23sub = Module[{zca},
   zca = R.(AdjointSolLie011 /. umaxoct).Inverse[
        R] - (AdjointSolLie011 /. u -> 1) // Simplify; 
   Solve[{zca == 0}, {C[2], C[3]}][[1]] /. cmoctsub /. alphaoctsub // 
    Simplify];

(* hamiltonian vanishes *)
c123sub = Module[{vv},
   vv = Solve[(ham011c /. c23sub) == 0, C[1]][[1]] /. cmoctsub /. 
      alphaoctsub // Simplify;
   Join[vv, c23sub /. vv] // Simplify];

(* upper half plane transverality *)

octsol = AdjointSol011 /. cmoctsub /. alphaoctsub // Simplify;
octsol0 = octsol /. t -> 0 // Simplify;
(* compare octsolf with blam for transversality.  *)

octsolf = octsol /. {t -> tmaxoct} // Simplify;
c45sub = Module[{blamoct},
   blamoct = 
    blam /. R1sub /. {x -> zoctupper[[1]], y -> zoctupper[[2]], 
         lam1 -> octsol0[[1]], lam2 -> octsol0[[2]]} /. t -> 0 /. 
      alphaoctsub // Simplify;
   Solve[(octsolf - blamoct /. c123sub // Simplify) == 0, {C[4], 
       C[5]}][[1]] // Simplify];

(* check switches occur: *)
Clear[Ln2];
switch13 /. {lambda1 -> octsolf[[1]], lambda2 -> octsolf[[2]], 
        x -> zoctupper[[1]], y -> zoctupper[[2]]} /. {t -> 
        tmaxoct} /. alphaoctsub /. c123sub /. 
   c45sub /. {Log[2] -> Ln2, Log[4] -> 2 Ln2, Log[8] -> 3 Ln2, 
   Log[16] -> 4 Ln2, Log[4096] -> 12 Ln2} // Simplify

switch32 /. {lambda1 -> octsol0[[1]], lambda2 -> octsol0[[2]], 
       x -> zoctupper[[1]], y -> zoctupper[[2]]} /. {t -> 0} /. 
    alphaoctsub /. c123sub /. c45sub // Simplify

(* Transversality for smoothed 3k+1 - gon and 3k-1-gon *)
    
(* We take 3k+1 or 3k-1 sides. *)
(* Inverse[goct0].goct//Simplify; *)

Clear[zpoly0, cospolysub, tracepoly, yc, zoct0, tmaxpoly, tmaxpolyR1];

test = {{"option1", 3 k + 1, m001sub},
   {"option2", 3 k - 1, m010sub}};

y0oct = (zoctupper /. alphaoctsub /. {t -> 0})[[2]];

gpoly = StateSolG /. xy011sub /. usub /. c0alpha011sub /. x0 -> 0 // 
   Simplify;

Xpoly = Inverse[gpoly].D[gpoly, t] // Simplify;

c0alphapolysub = Join[ (c0alpha011sub /. x0 -> 0)];

tmaxpoly = 
 t /. Solve[
     Xpoly[[1, 1]] == (Inverse[Rm001].(Xpoly /. t -> 0).Rm001)[[1, 
       1]], t][[1]] // Simplify


test = tmaxoct - (tmaxpoly /. {y0 -> y0oct}) /. m001sub // Simplify;

test = Xpoly - (Inverse[Rm001].(Xpoly /. t -> 0).Rm001) /. 
    t -> tmaxpoly // Simplify;

upolymaxsub = usub /. c0alphapolysub /. t -> tmaxpoly

test = (u /. upolymaxsub /. y0 -> y0oct) - u /. umaxoct // Simplify;


(* 6k+2-gon k=1 is 8-gon *)

(* Transversality of regular smoothed polygons *)

c23polysub = Module[{zca},
   zca = Rm001.(AdjointSolLie011 /. upolymaxsub).Inverse[
         Rm001] - (AdjointSolLie011 /. u -> 1) /. c0alphapolysub // 
     Simplify;
    Solve[{zca == 0}, {C[2], C[3]}][[1]] /. c0alphapolysub // 
    Simplify];

test = c23sub - (c23polysub /. y0 -> y0oct) /. m001sub // Simplify;

(* hamiltonian vanishes *)
c123polysub = Module[{vv},
   vv = Solve[(ham011c /. c23polysub) == 0, C[1]][[1]] /. 
      c0alphapolysub // Simplify;
   Join[vv, c23polysub /. vv] // Simplify];

test = (c123polysub /. y0 -> y0oct /. m001sub) - c123sub // Simplify;

test = Sort[Join[cmoctsub,
       alphaoctsub]] -
     Sort[Join[m001sub, (c0alphapolysub /. m001sub)]] /. y0 -> y0oct //
    Simplify;

(* upper half plane transverality *)

polysol = AdjointSol011 /. c0alphapolysub // Simplify;

test = octsol - polysol /. y0 -> y0oct /. m001sub // Simplify;

polysol0 = polysol /. t -> 0 // Simplify;

polysolf = polysol /. {t -> tmaxpoly} // Simplify;

test = octsol0 - polysol0 /. y0 -> y0oct /. m001sub // Simplify;
test = octsolf - polysolf /. y0 -> y0oct /. m001sub // Simplify;

zpolyupper = {x, y} /. xy011sub /. usub /. c0alphapolysub // Simplify;

test = zpolyupper - zoctupper /. c0alphapolysub /. y0 -> y0oct /. 
    m001sub // Simplify;

(* compare octsolf with blam for transversality.  *)

c45polysub = Module[{blampoly, Rm001sub},
   Rm001sub = {aR -> 1/2, bR -> 1/(2 m)};
   blampoly = 
    blam /. Rm001sub (* 
        R1sub/. *) /. {x -> zpolyupper[[1]], y -> zpolyupper[[2]], 
         lam1 -> polysol0[[1]], lam2 -> polysol0[[2]]} /. t -> 0 /. 
      c0alphapolysub // Simplify;
   Solve[(polysolf - blampoly /. c123polysub // Simplify) == 0, {C[4],
        C[5]}][[1]] // Simplify];

(* check switches occur: *)
switch13poly = Module[{switch},
   switch = (Hupper /. z100sub) - (Hupper /. 
       z011sub); (switch /. {lambda1 -> polysolf[[1]], 
             lambda2 -> polysolf[[2]], x -> zpolyupper[[1]], 
             y -> zpolyupper[[2]]} /. {t -> tmaxpoly} /. 
          c0alphapolysub /. c123polysub /. c45polysub // Simplify) // 
     Simplify // Factor] /. {m^2 -> 1/3}

switch32poly = 
 lambda2 /. {lambda1 -> polysol0[[1]], lambda2 -> polysol0[[2]], 
         x -> zpolyupper[[1]], y -> zpolyupper[[2]]} /. {t -> 0} /. 
      c0alphapolysub /. c123polysub /. c45polysub // Simplify // 
  Factor

  (* calculate y0 and tmax. Specialize to 3k+1 and u=001.  *)

Clear[zpoly0, zpoly001, cospoly001sub, costpoly, plotpoly];
Clear[kT, switch13polyT, switch32polyT, plotpoly, tmaxT];

(*
zpoly001 = {0,Module[{yc,tracepoly},
tracepoly=Tr[R1.gpoly/.t\[Rule]tmaxpoly/.m001sub//Simplify]//Simplify;\

(* pick the unique positive real root *)
yc=y0/.Solve[tracepoly\
\[Equal]2 cos,y0][[2]]//Simplify]};
*)

(* cospoly001sub = {cos\[Rule]Cos[Pi k/(3*k+1)]}; *)

typoly001[k1_] := Module[{y, cossub, yk, trace},
   cossub = {cos -> Cos[Pi (k)/(3*k + 1)]};
   trace = Tr[R1.gpoly /. t -> tmaxpoly /. m001sub] // Simplify;
   yk = y0 /. Solve[trace == 2 cos, y0][[2]] // Simplify;
   {tmaxpoly, y0} /. {y0 -> yk} /. m001sub /. cossub /. k -> k1];

test = Module[{tk, yk},
  {tk, yk} = typoly001[1];
  yk - y0oct // N
  ]

(* increasing cost *)
Module[{cost},
  cost[k_] := Module[{tk, yk},
    {tk, yk} = typoly001[k];
    (3 k + 1)*cost011 /. c0alphapolysub /. t1 -> tk /. y0 -> yk /. 
     m001sub];
  test = cost[1] // Simplify // N;
  test = Table[{6 k + 2, cost[k]}, {k, 1, 3}] // N;
  Plot[cost[k], {k, 1, 4}]
  ];

(* Lambda0poly is a continuous function of y0
of the form {{0,bL},{cL,0}}
tending to init condition of the circle *)

test = Module[{Lambda0poly, test},
   Lambda0poly = 
    AdjointSolLie011Init /. c0alphapolysub /. c123polysub /. 
       c45polysub /. m001sub // Factor;
   Lambda0poly /. y0 -> 1
   ];

test = AdjointSol011 /. c0alphapolysub /. c123polysub /. 
      c45polysub /. t -> 0 /. y0 -> 1 // Factor;

      
(* Jan 27, 2017. rigorous proof that switching function is positive. *)
\

(* Work a numerical example *)

test = Module[{k1 = 1, switch, st, tk, yk},
   {tk, yk} = typoly001[k1];
   switch = {-switch13, switch32};
   st = (switch /. {lambda1 -> polysol[[1]], lambda2 -> polysol[[2]], 
             x -> zpolyupper[[1]], y -> zpolyupper[[2]]} /. 
           c0alphapolysub /. c123polysub /. c45polysub /. 
        lambda0 -> -1 /. y0 -> yk /. m001sub);
   Plot[st, {t, 0, tk}]];

(* Step 1. Show that switch13 and switch32 are equal after a change \
of coordinate *)
test = Module[{t2sub, switch, sw1, sw2},
   t2sub = {t -> (tmaxpoly - t /. m001sub)} // Simplify;
   switch = {(-switch13), switch32};
   sw1 = (switch /. {lambda1 -> polysol[[1]], lambda2 -> polysol[[2]],
               x -> zpolyupper[[1]], y -> zpolyupper[[2]]} /. 
            c0alphapolysub /. c123polysub /. c45polysub /. 
         lambda0 -> -1 /. m001sub) // Simplify // Factor;
   (sw1[[1]] /. t2sub) - sw1[[2]] // Simplify];

(* Step 2 make a change of coordinates. Get new variables and domain \
for the switch function *)
{switchpoly, test, test} = 
  Module[{sw1, sw2, t1sub, y0sub, ybound, vbound},
   t1sub =  {t -> t1/(Sqrt[3] y0)};
   y0sub = {y0^2 -> (y - 1)/3, t1 -> Log[v] - Log[y]};
   sw1 = y0^5 3 Sqrt[3] v^2 polysol[[2]] /. {x -> zpolyupper[[1]], 
              y -> zpolyupper[[2]]} /. c0alphapolysub /. 
           c123polysub /. c45polysub /. lambda0 -> -1 /. m001sub /. 
       t1sub // Simplify // Factor;
   sw2 = sw1 /. y0sub /. {Log[y/4] -> Log[y] - Log[4]} // Simplify;
   ybound = {y0oct^2 3 + 1, 1^2*3 + 1} // Simplify;
   vbound = {y, (1 + 3 y0^2) E^(Sqrt[3] y0 tmaxpoly /. m001sub)} // 
     Simplify;
   {sw2, ybound, vbound}];
switchpoly // Simplify;

(* Step 3. Take derivatives to establish positivity *)
switchpoly
test = switchpoly /. {v -> y} // Simplify;
test = Module[{r},
   r = D[switchpoly, y] /. v -> y // Simplify;
   Print[r // Simplify];
   Plot[r, {y, Sqrt[8], 4}]];
test = Module[{r},
   r = D[switchpoly, {y, 2}] // Simplify;
   Print[r];
   Print[r /. {y -> 4, v -> 4} // Simplify];
   Plot3D[r, {y, Sqrt[8], 4}, {v, y, 4}]];

(* 3k-1 links. Calculation of tk,zk. *)

(* Material for 3k-1, and u=010 *)

Clear[gboly, Xboly, c0alphabolysub, tmaxboly, ubolymaxsub, zpoly0alt, 
  zpoly010, cospolysubalt, cospoly010sub, plotpolyalt, costpolyalt];
Clear[typoly010];

(* CHANGES *)

typoly010[k1_] := Module[{y, cossub, yk, trace},
   cossub = {cos -> Cos[Pi (k)/(3*k - 1)]};
   trace = Tr[R.gpoly /. t -> tmaxpoly /. m010sub] // Simplify;
   yk = y0 /. Solve[trace == 2 cos, y0][[2]] // Simplify;
   {tmaxpoly, y0} /. {y0 -> yk} /. m010sub /. cossub /. k -> k1];

Module[{cost, tk, yk, k},
  cost[k_] := (3 k - 1)*cost011 /. c0alphapolysub /. m010sub /. 
     t1 -> typoly010[k][[1]] /. y0 -> typoly010[k][[2]];
  test = Table[{6 k - 2, cost[k]}, {k, 2, 4}] // N;
  Plot[cost[k], {k, 2, 4}] ];

(* switch appears to be negative on 
010 link. So not Pontryagin extremal. *)

test = Module[{k1 = 2, switch, st, tmaxT, tk, yk},
   switch = { -switch32 , -switch12} ;
   {tk, yk} = typoly010[k1] // N;
   st = (switch /. {lambda1 -> polysol[[1]], lambda2 -> polysol[[2]], 
             x -> zpolyupper[[1]], y -> zpolyupper[[2]]} /. 
           c0alphapolysub /. c123polysub /. c45polysub /. 
        lambda0 -> -1 /. y0 -> yk /. m010sub);
   Plot[st, {t, 0, tk}] ];
            

(* Plot of cost for smoothed polygons, interpolating between data \
points with a bezier curve *)

test = Module[{e, p1, p2, pt1, pt2, pt3, bezier},
   pt1 = {{4, 3.456}, {8, 3.126}, {10, 3.15}, {14, 3.139}, {16, 
      3.14374}, {20, 3.14058}, {22, 3.1424}};
   e = 1.0;
   pt2 = Flatten[
     Map[{{#[[1]] - e, #[[2]]}, #, {#[[1]] + e, #[[2]]}} &, pt1], 1];
   pt3 = Drop[Drop[pt2, 1], -1];
   bezier = BezierCurve[pt3];
   p1 = Graphics[{bezier}];
   p2 = Plot[Pi, {x, 4, 22}, PlotStyle -> {Red}];
   Show[{p2, p1}, PlotRange -> {{7, 22}, {3.1, 3.25}}, Axes -> True, 
    AxesOrigin -> {8, Pi}] ];
Export["~/Desktop/bezier.jpg", test]

(* General Bang - Bang switching state trajectory
and perturbation of the Octagon. 
Graphics of smoothed polygons. *)

(* Work with u=(0,0,1) *)
(* Jan 27, 2017 *)
(* general bang-bang \
switching state trajectory *)

Clear[Gamma0, gamma, gamma0, gammafn0state, gammafn0hold, sstate, 
  gammafn0, gammafnu, gammafn, xyfn, xyfnstate, xysol, foldfn, 
  gammafoldfn, gammafnX, testfn, xyfnhold, xyfnstate, zterm];
Clear[gammafn0, gammafoldfn, gammafnX, gammafn, zterm];

xyfnhold = {x, y} /. xy011sub /. usub /. c0alpha011sub /. m001sub;
xyfn[{x0_, y0_}, t_] := Release[xyfnhold];
(* test=ParametricPlot[xyfn[{0,1},t],{t,0,0.3}] *)

test = xyfn[{0, 1}, t];
test = xyfn[{x0, y0}, 0];

gammafn0hold = Module[{s},
   s = StateSolG /. usub /. c0alpha011sub /. m001sub // Simplify;
   Inverse[(s /. t -> 0)].s // Simplify];

gammafn0[{x0_, y0_}, t_] := Release[gammafn0hold];

test = gammafn0[{0, 1}, 0.1];
test = gammafn0[{x0, y0}, 0];

gammafn0[i_, z0_, t_] := powR[i].gammafn0[z0, t].powR[-i];

gammafn0[i_, z0_, {T1_, T2_}, t_] := 
  Piecewise[{{I2, t <= T1}, {gammafn0[i, z0, t - T1], 
     T1 <= t && t <= T2}},(*default*)gammafn0[i, z0, T2 - T1]];

gammafoldfn[{t_, z0_, t1_, T1_, k1_, gamk1_}, {k2_, t2_}] := 
  Module[{z1, T2},
   z1 = Repfrac[powR[k1 - k2], xyfn[z0, t1]];
   T2 = T1 + t2;
   {t, z1, t2, T2, k2, gammafn0[k2, z1, {T1, T2}, t]}];

gammafnX[kt_, z0_, t_] := Module[{k1, t1, T0, T1, kk},
   {k1, t1} = First[kt];
   kk = Drop[kt, 1];
   {T0, T1} = {0, t1};
   FoldList[
    gammafoldfn, {t, z0, t1, T1, k1, gammafn0[k1, z0, {T0, T1}, t]}, 
    kk]];

gammafn[kt_, z0_, t_] := Module[{gfX, gs},
   gfX = gammafnX[kt, z0, t];
   gs = Map[Last, gfX];
   Apply[Dot, gs]];

zterm[kt_, z0_] := Module[{any, z, kn, tn},
   any = 0;
   z = Last[gammafnX[kt, z0, any]][[2]];
   {kn, tn} = Last[kt];
   Repfrac[powR[kn], xyfn[z, tn]]];

test = Module[{fn},
   fn[t_] := gammafn[{{0, 0.1}, {1, 0.2}}, {0, 1}, t];
   Plot[fn[t], {t, -0.1, 0.4}]] ;

test = (2 == Length[gammafn[{{0, 0.1}, {1, 0.2}}, {0, 1}, 0.1]]);

(* cost along a deformation *)
Clear[cost011hold, cost011r, costkt];
cost011hold = cost011 /. c0alpha011sub /. m001sub /. t1 -> t;
cost011r[{x0_, y0_}, t_] := Release[cost011hold];

costkt[kt_, z0_] := Module[{any, gfX, costs},
   any = 0;
   gfX = gammafnX[kt, z0, any];
   costs = Map[cost011r[#[[2]], #[[3]]] &, gfX];
   Apply[Plus, costs]];

test = cost011r[{0, 1}, 0.1];
test = cost011r[{0, 1.1}, 0.1];
test = costkt[{{0, tmaxoct}, {-1, tmaxoct}, {-2, tmaxoct}, {-3, 
     tmaxoct}}, {0.0, N[y0oct]}]/Sqrt[12]

(* perturbed octagon *)


(* perturb octagon *)
Clear[testGz, testfnG, testG, testz, ze];
Clear[ste, defm, delta, cc, defsub, gzError, gzGrad, ff, ee, testjz, 
  ze, testfnG, epss];

NN[x_] := N[x, 100];
eps = NN[10^-20];
kth[h1_, h2_, h3_, 
   h4_] := {{0, NN[tmaxoct + h1]}, {-1, NN[tmaxoct + h2]}, {-2, 
    NN[tmaxoct + h3]}, {-3, NN[tmaxoct + h4]}};
ze[ex_, ey_] := {ex, y0oct + ey} // NN;

gzGrad[hh_] := 
  Module[{gGrad, gamma, zGrad, kt, z0, T, h1, h2, h3, h4, ex, ey},
   {h1, h2, h3, h4, ex, ey} = hh;
   kt = kth[h1, h2, h3, h4];
   z0 = ze[ex, ey];
   zGrad = (Repfrac[R, zterm[kt, z0]] - z0)/eps // NN;
   T = Apply[Plus, Map[Last, kt]] // NN;
   gamma = gammafn[kt, z0, T] // NN;
   gGrad = Flatten[(R1.gamma - I2)/eps];
   Join[zGrad, gGrad]];
test = gzGrad[{eps, 0, 0, 0, 0, 0}];

defsub = Module[{ste, defm, delta, i, j, hh},
   delta[i_, j_] := If[i == j, 1, 0];
   ste[i_] := Table[delta[i, j], {j, 1, 6}];
   (* sl2 trace zero, so can drop one redundant coefficient *)
   
   defm = Table[Drop[gzGrad[eps*ste[i]], -1], {i, 1, 6}];
   Solve[{{h1, h2, h3, h4, ex, ey}.defm == 0, h1 == ee}, {h1, h2, h3, 
       h4, ex, ey}][[1]] // Chop];

(* ERROR: cost Derivative should be zero at local min *)

costOctPerturb[e_] := Module[{tm, kt, z0},
   kt = kth[h1, h2, h3, h4] /. defsub /. ee -> e // NN;
   z0 = ze[ex, ey] /. defsub /. ee -> e // NN;
   costkt[kt, z0]];
{"cost-deriv", (costOctPerturb[0] - costOctPerturb[eps])/eps, 
 costOctPerturb[0]}
Plot[costOctPerturb[e], {e, -0.01, 0.01}];

test = Module[{hh, errors},
  hh = {h1, h2, h3, h4, ex, ey} /. defsub /. ee -> eps // NN;
  errors = gzGrad[hh] // NN // Abs;
  Apply[Plus, errors]
  ]

(* Plot smoothed octagon, 14 - gon, perturbed octagon *)

(* N speeds up considerably *)
(* plotOct *)

Clear[testfn, cc0, po0, po1, po2, po3, po4, po5];

plotCircle = Graphics[{Red, Circle[{0, 0}, 1]}];

plotOct = Module[{fn, tm, t, v, po0, po1, po2, po3, po4, po5},
   tm = tmaxoct // N;
   fn[t_, v_] := 
    gammafn[{{0, tm}, {-1, tm}, {-2, tm}, {-3, tm}}, {0.0, N[y0oct]}, 
      t].v;
   (* fn[0.1,v0] *)
   
   po0 = ParametricPlot[fn[t, v0], {t, 0, 4.0*tmaxoct}, 
     PlotStyle -> {Red}];
   po1 = ParametricPlot[fn[t, v1], {t, 0, 4.0*tmaxoct}, 
     PlotStyle -> {Red}];
   po2 = ParametricPlot[fn[t, v2], {t, 0, 4.0*tmaxoct}, 
     PlotStyle -> {Red}];
   po3 = ParametricPlot[fn[t, v3], {t, 0, 4.0*tmaxoct}, 
     PlotStyle -> {Red}];
   po4 = ParametricPlot[fn[t, v4], {t, 0, 4.0*tmaxoct}, 
     PlotStyle -> {Red}];
   po5 = ParametricPlot[fn[t, v5], {t, 0, 4.0*tmaxoct}, 
     PlotStyle -> {Red}];
   {po0, po1, po2, po3, po4, po5}
   (* data for preprint graphic: *)
   (* Table[fn[i*4*tmaxoct/5,v5]//
   N//Chop,{i,0,5}] *)];

test = Module[{},
    typoly001[1]] // N;

Show[{plotOct, plotCircle}, PlotRange -> {{-1, 1}, {-1, 1}}]


(* plot solution found, uses defsub. *)

Clear[testf, tmm, pp0, pp1, pp2, pp3, pp4, pp5];
plotDeformOct = 
  Module[{testf, tm4, pp0, pp1, pp2, pp3, pp4, pp5, e, kt, zz, tm},
   tm = tmaxoct // N;
   e = -0.02;
   kt = {{0, tm + h1}, {-1, tm + h2}, {-2, tm + h3}, {-3, 
        tm + h4}} /. defsub /. ee -> e;
   zz = {0 + ex, y0oct + ey} /. defsub /. ee -> e // N;
   testf[t_, v_] := gammafn[kt, zz, t].v;
   testf[0.1, v0];
   tm4 = 4*tmaxoct // N;
   pp0 = ParametricPlot[testf[t, v0], {t, 0, tm4}, 
     PlotStyle -> {Blue, Thin}];
   pp1 = ParametricPlot[testf[t, v1], {t, 0, tm4}, 
     PlotStyle -> {Blue, Thin}];
   pp2 = ParametricPlot[testf[t, v2], {t, 0, tm4}, 
     PlotStyle -> {Blue, Thin}];
   pp3 = ParametricPlot[testf[t, v3], {t, 0, tm4}, 
     PlotStyle -> {Blue, Thin}];
   pp4 = ParametricPlot[testf[t, v4], {t, 0, tm4}, 
     PlotStyle -> {Blue, Thin}];
   pp5 = ParametricPlot[testf[t, v5], {t, 0, tm4}, 
     PlotStyle -> {Blue, Thin}];
   {pp0, pp1, pp2, pp3, pp4, pp5}];

Show[{plotDeformOct, plotOct}, 
  PlotRange -> {{-1.1, 1.1}, {-1.1, 1.1}}];


(* Note starting z0 is R1.{0,yk}. Can vary k.
k = 1.001, n=2 gives an approximate square. *)

plotDec = 
  Module[{k = 1.03, n, kt, yk, tk, fn, t, v, pd0, pd1, pd2, pd3, pd4, 
    pd5},
   n = Floor[3 k - 1];
   {tk, yk} = typoly010[k] // N;
   kt = Table[{i, tk}, {i, 1, n}];
   fn[t_, v_] := gammafn[kt, Repfrac[R1, {0, yk}], t].v;
   test = fn[5*tk, v0] - {0.5, Sqrt[3]/2};
   pd0 = ParametricPlot[fn[t, N[v0]], {t, 0, n*tk}];
   pd1 = ParametricPlot[fn[t, N[v1]], {t, 0, n*tk}];
   pd2 = ParametricPlot[fn[t, N[v2]], {t, 0, n*tk}];
   pd3 = ParametricPlot[fn[t, N[v3]], {t, 0, n*tk}];
   pd4 = ParametricPlot[fn[t, N[v4]], {t, 0, n*tk}];
   pd5 = ParametricPlot[fn[t, N[v5]], {t, 0, n*tk}];
   {pd0, pd1, pd2, pd3, pd4, pd5}
   (* graphics for article: Table[fn[i*n*tk/10,N[v5]],{i,0,10}]*)] ;
test;
Show[{plotDec}, PlotRange -> {{-1.1, 1.1}, {-1.1, 1.1}}]



Clear[y0hept, tmax];
(* Can vary k. *)

test = plotSmoothGon = 
   Module[{k = 2, n, kt, tk, yk, fn, t, v, ph0, ph1, ph2, ph3, ph4, 
     ph5},
    {tk, yk} = typoly001[k] // N;
    n = 3 k + 1;
    kt = Table[{Mod[-i, 3], tk}, {i, 0, n - 1}];
    fn[t_, v_] := gammafn[kt, {0, yk}, t].v;
    fn[n*tk, v0];
    ph0 = ParametricPlot[fn[t, v0], {t, 0, n*tk}];
    ph1 = ParametricPlot[fn[t, v1], {t, 0, n*tk}];
    ph2 = ParametricPlot[fn[t, v2], {t, 0, n*tk}];
    ph3 = ParametricPlot[fn[t, v3], {t, 0, n*tk}];
    ph4 = ParametricPlot[fn[t, v4], {t, 0, n*tk}];
    ph5 = ParametricPlot[fn[t, v5], {t, 0, n*tk}];
    {ph0, ph1, ph2, ph3, ph4, ph5}
    ];
test = Show[{plotSmoothGon, plotCircle}, 
   PlotRange -> {{-1, 1}, {-1, 1}}];
Export["~/Desktop/14gon2.jpg", test];

(* Non-chattering between 010 and 001. *)

(* We analyze behavior near lambda2=0 (and lambda1!=0).  The basic idea of non-chattering is that the function lambda2 is nearly the same for both domains 010 and 001.  To first approximation, we can view lambda2 as a single analytic function that can be put in Weierstrass form.  In a degenerate case (say epsilon=0, x0!=0), we might have a quadratic polynomial (say the Weierstrass approximation) with a double root at 0.  Deforming to epsilon!=0, we get a quadratic polynomial that has been deformed.  We might have different behavior near zero, say where the graph dips below the x-axis, but the general shape has not changed, so that the quadratic function on the mid-scale carries us away from the zeros of lambda2.

Similar comments apply in the cubic case of lambda2 (epsilon=x0=0) with a triple zero at t=0. Deformation might give some short switches, between the zeros of lambda2, but on the mid-scale, the cubic carries us away from zero. *)

Clear[cLsub, newswitch, newswitch001, adj001, x0y0sub, lm1sub, 
  c1223sub, adj011, c45sub, adj2, bLsub, adj3];


(* switch is valid on both 011 and 010 domains *)
(* lambda2 is \
positive, exactly when in 001 domain. Note that we break symmetry by \
removing a factor of m, going from preswitch to switch. *)
Clear[eps]
(* Easy check: not abnormal *)

preswitch32 = Module[{h}, h = Hupper011 /. usub;
    h - (h /. m -> -m)] // Simplify;
{Abnormal, switch32A} = 
  Module[{c0alpha011sub, lm1sub, labsub, c123sub, adj011, c45sub, 
    adj2, bLsub, adj3}, 
   c0alpha011sub = 
    Solve[({x, y} /. (xy011sub /. u -> 1)) == {x0, y0}, {c0, alpha}][[
     1]];
   labsub = {lambda0 -> 0};
   lm1sub = {lambda0 -> -1};
   c123sub = 
    Solve[(AdjointSolLie011 /. u -> 1 // Simplify) == {{aL, 
         bL}, {cL, -aL}}, {C[1], C[2], C[3]}][[1]];
   adj011 = AdjointSol011[[2]] /. c123sub // Simplify;
   c45sub = 
    Solve[{(adj011 /. {t -> 0} // Factor) == 
        0, (ham011c /. c123sub) == 0}, {C[4], C[5]}][[1]];
   adj2 = adj011 /. c45sub /. c0alpha011sub // Simplify // Factor;
   bLsub = Solve[(D[adj2, t] /. {t -> 0}) == eps, bL][[1]];
   adj3 = adj2  /. bLsub /. lm1sub // Simplify;
   {(adj2 /. labsub), adj3}];

(* must be normal: lambda0\[Rule]-1 *)

Abnormal y0^3 /(m + x0) /. {E^(t y0/(m + x0)) -> u} // Simplify;
Clear[switch32B];
(*
switch32A (1+s)^2 y0^3/(m+x0)/.{t\[Rule]Log[1+s] \
(m+x0)/y0}//Simplify//Factor
*)
polyapprox[switch32A, 3]
(*AdjointSol011/.{t\[Rule] Log[u]/alpha}//Simplify;*)


(* Non - chattering away from singular point. Canonical coordinates. Two vanishing switches. *)


(* Canonical coordinates xi1,xi2,mu1,mu2, with mu-i switching \
function *)
xi2sub = {xi2 -> +3 y^2/(1 + Sqrt[3] x) + Sqrt[3] x};
xi1sub = {xi1 -> x};
A1xi = Module[{r1, r2},
   r1 = xi1 /. xi1sub;
   r2 = xi2 /. xi2sub;
   {{D[r1, x], D[r2, x]}, {D[r1, y], D[r2, y]}} // Simplify];
lambdaxisub = Module[{p},
   p = A1xi.{mu1, mu2};
   {lambda1 -> p[[1]], lambda2 -> p[[2]]}];

(* Tests: *)

test = {"switch: mu2", (Hupper /. z001sub) - (Hupper /. z010sub) /. 
     lambdaxisub // Factor};
test = {"switch: mu1", (Hupper /. z001sub) - (Hupper /. z100sub) /. 
     lambdaxisub // Factor};
(* switchMu3=(Hupper/.z010sub)-(Hupper/.z100sub)/.lambdaxisub//Factor;\
  ignore *)

(* independence of Hamiltonian for third switch *)
Clear[mu2test];
test = Module[{h, mu2sub, sw},
   h = testg1g2.{mu1, mu2};
   sw = switch[1, 2] /. lambdaxisub // Simplify;
   mu2sub = Solve[sw == 0, mu2][[1]];
   h /. mu2sub /. Zsub /. {u0 -> t, u1 -> 1 - t, u2 -> 0} // 
     FullSimplify // Factor];
(* independent of t *)
D[test, t] // FullSimplify


(* Both g1,g2 are independent of the control 
along the appropriate edge of U, since mu1 and mu2 are switches. 
We have mu1 g1 + mu2 g2 \[Equal] lambda1 f1 + lambda2 f2 *)

Clear[g1, g2];
test = Module[{g1, g2},
   {g1, g2} = Transpose[A1xi].UpperHalfODE // Simplify;
   {g1 /. {b -> -2/3, c -> 0} // Simplify,
    g2 /. {a -> (u1 - u2)/Sqrt[3], b -> u0/3 - 2 u1/3 - 2 u2/3, 
        c -> u0} /. {u0 -> t, u1 -> 0, u2 -> 1 - t} // FullSimplify}];

(* Same thing computed a different way as a cross check *)
(* \
independent of control along edge *)
Clear[C1xi];
test = Module[{f1, f2, A, Adot, C, C1xi, T1, T2, zerocheck},
  {f1, f2} = UpperHalfODE;
  C = {{D[f1, x], D[f2, x]}, {D[f1, y], D[f2, y]}};
  A = Inverse[A1xi] // Simplify;
  Adot = D[A, x] f1 + D[A, y] f2 // Simplify;
  C1xi = -Adot.A1xi + A.C.A1xi // Simplify;
  T1 = Transpose[C1xi][[1]] /. {a -> t, b -> -2/3, c -> 0} // 
    Simplify ;
  (* It is independent of t! *)
  {zerocheck, T2} =
   {2 Sqrt[3] a - 3 b + c, 
       Transpose[C1xi][[2]]} /. {a -> (u1 - u2)/Sqrt[3], 
       b -> u0/3 - 2 u1/3 - 2 u2/3, c -> u0} /. {u0 -> t, u1 -> 0, 
      u2 -> 1 - t} // FullSimplify;
  {zerocheck, T1, T2}]

(* 100 State Solutions *)

Clear[xy001sub, c0alphaR1sub];

Rm010 = 1/2  {{1, 1/m}, {-1/m, 1}};
test = (Rm010 /. m010sub) - R;

x0y0R1sub = Module[{x1, y1},
   {x1, y1} = Repfrac[Inverse[Rm010], {x0, y0}] // Simplify;
   {x0 -> x1, y0 -> y1}];

(* use m010sub, and c0alpha100sub to evaluate *)
m010sub;

c0alpha100sub = (c0alpha011sub /. x0y0R1sub) // Simplify;

(* here is the xy state solution on 100 sector *)

xy100sub = Module[{vv, x1, y1},
   {x1, y1} = Repfrac[Rm010, {x, y} /. xy011sub] // Simplify;
   {x -> x1, y -> y1}];

(* test alternate derivation *)

test = Module[{vv, x1, y1, xy100subAlt},
   vv = Repfrac[R, {x, y} /. xy011sub /. m010sub] // Simplify;
   {x1, y1} = vv /. c0alpha011sub /. x0y0R1sub // Simplify;
   xy100subAlt = {x -> x1, 
     y -> y1}; ({x, y} /. xy100sub /. c0alpha100sub /. 
       m010sub) - ({x, y} /. xy100subAlt /. m010sub) // Simplify];

(* check it satisfies the ODE *)
UpperHalfODE /. z100sub // Factor;
testODE = Module[{v1, v2, v3, v4, t2},
    {v1, v2} = {x, y} /. xy100sub /. {u -> u[t]};
    v3 = {D[v1, t], D[v2, t]} /. {u'[t] -> alpha u, u[t] -> u};
    v4 = UpperHalfODE /. z100sub /. xy100sub // Simplify;
    t2 = Transpose[{v3, v4}] /. c0alpha100sub /. m010sub;
    {t2[[1, 1]]/t2[[1, 2]], t2[[2, 1]]/t2[[2, 2]]}] // Simplify;

testinitial = (xy100sub /. u -> 1 /. c0alpha100sub // Simplify);

AdjointSolLie100 = Module[{Ytt, Rs, Cs, eqns, a1, a2, a3},
   Ytt = Xupper /. xy100sub;
   Rs = {{a1[u], a2[u]}, {a3[u], -a1[u]}};
   Cs = (Rs.Ytt - Ytt .Rs)/(alpha u) // Simplify;
   eqns[i_, j_] := D[Rs, u][[i, j]] == Cs[[i, j]];
   (* Rs/. *)
   Rs /. DSolve[{eqns[1, 1], eqns[1, 2], eqns[2, 1]}, {a1, a2, a3}, 
      u][[1]]];

AdjointSolLie100c123sub = Module[{},
     Solve[(AdjointSolLie100 /. u -> 1) == {{aL, bL}, {cL, -aL}}, {C[
        1], C[2], C[3]}]][[1]] // Simplify;


AdjointSolLie100abc = (AdjointSolLie100 /. AdjointSolLie100c123sub // 
      Simplify) /. m010sub // Simplify;

AdjointSolLie100abc /. u -> 1 // Simplify

(* Adjoint Solution 100 *)

(*  100 ODE costate solutions by Rotation from 010 control *)
(* \
AdjointSol100 gives adjoint solution on 100 sector,
with c0,alpha given by c0alpha100sub, m by m010sub *)


Clear[c1alpha011sub, c0alphaR1sub];
Clear[hatlambdasol, hatlambdasub, checkUpperODE, blamos, blamos1, 
  blamos2, blamosUpper, hatxysub, z1sub, hatRsub, abRsub];

c0alpha100sub;

(* abRsub = Module[{a,b,c,junk},
{{a,b},{junk,junk}} = R;
{aR\[Rule]a,bR\[Rule]b}//Simplify]; *)

abRmsub = {aR -> 1/2, bR -> 1/(2 m)};

AdjointSol100 = 
  blam /. {lam1 -> AdjointSol011[[1]], lam2 -> AdjointSol011[[2]]} /. 
      xy011sub /. usub /. abRmsub (* /.m010sub *)// Simplify;

(* repeat 
x0y0R1sub = Module[{x1a,y1a},
{x1a,y1a}=Repfrac[R1,{x0,y0}];
{x0\[Rule]x1a,y0\[Rule]y1a}];
*)

(* c0alpha100sub same as alternative derivation *)
test = 
 Module[{c0alpha100subAlt, c0s, as},
  {c0s, as} = {c0, alpha} /. c0alpha011sub /. x0y0R1sub /. m010sub // 
    Simplify;
  c0alpha100subAlt = {c0 -> c0s, alpha -> as};
  ({c0, alpha} /. c0alpha100sub /. m010sub) - ({c0, alpha} /.
      
      c0alpha100subAlt) // Simplify]

(* compare two derivations of AdjointSol100 *)
test = 
 Module[{hatlambdasol, blamos1, hatxysub},
  hatxysub = 
   xy011sub /. usub /. c0alpha011sub /. x0y0R1sub /. m010sub // 
    Simplify;
  hatlambdasol = 
   AdjointSol011 /. c0alpha011sub /. x0y0R1sub /. m010sub // 
    Simplify;
  blamos1 = 
   blam /. hatxysub /. {lam1 -> hatlambdasol[[1]], 
       lam2 -> hatlambdasol[[2]]} /. abRmsub // 
    Simplify; (blamos1 - AdjointSol100) /. c0alpha100sub /. m010sub //
    Simplify]

(* test of homogeneous part of ODE for lambda on 100 sector. I'm not \
testing inhomogenous part, because I haven't yet calculated Lie \
sector solution on 100, but it would be trivial to do. *)
\
testUpperODE = Module[{blamosUpper, adj, lhs, randomsub},
  blamosUpper = 
   AdjointSol100 /. {lambda0 -> 0, C[1] -> 0, C[2] -> 0, C[3] -> 0} //
     Simplify;
  adj = adjoint[Hupper /. z100sub] /. xy100sub /. 
     usub /. {lambda1 -> blamosUpper[[1]], 
     lambda2 -> blamosUpper[[2]]};
  lhs = D[blamosUpper, t];
  randomsub = {t -> 0.2, C[4] -> 2.2, C[5] -> 1.3, x0 -> 0.2, 
    y0 -> 1.86};
  (((adj - lhs) // Simplify // Factor) /. m010sub)]


(* Circle Revisited, PMP singular, 2nd variation *)

(* circle revisited *)
Z333sub = {a -> 0, b -> -1/3, c -> 1/3};
UpperHalfODE /. Z333sub // Simplify // Factor;
xycirclesub = {x -> 0, y -> 1};
(* circle adjoint solution: Lie term *)

AdjointSolCircleLie = Module[{Ytt, Rs, Cs, eqns, a1, a2, a3},
   Ytt = Xupper /. xycirclesub;
   Rs = {{a1[t], a2[t]}, {a3[t], -a1[t]}};
   Cs = (Rs.Ytt - Ytt .Rs) // Simplify;
   eqns[i_, j_] := D[Rs, t][[i, j]] == Cs[[i, j]];
   Rs /. DSolve[{eqns[1, 1], eqns[1, 2], eqns[2, 1]}, {a1, a2, a3}, 
      t][[1]]];

HamCircle = Tr[AdjointSolCircleLie.Xupper] +
     Hampayoff + Hupper /. Z333sub // Simplify;
AdjointODECircle = 
  adjoint[HamCircle] /. xycirclesub // Simplify;


AdjointSolCircle = Module[{adj},
   adj = AdjointODECircle /. {lambda1 -> lambda1[t], 
      lambda2 -> lambda2[t]}; {lambda1[t], lambda2[t]} /. 
     DSolve[{lambda1'[t] == adj[[1]], 
        lambda2'[t] == adj[[2]]}, {lambda1, lambda2}, t][[1]] // 
    Simplify];
costateCirclesub = {lambda1 -> AdjointSolCircle[[1]], 
   lambda2 -> AdjointSolCircle[[2]]};


(* transversality *)

(* Circle costate is unconstrained in Lie sector *)

testCircle = 
  R.(AdjointSolCircleLie /. t -> Pi/3).Inverse[
      R] - (AdjointSolCircleLie /. t -> 0) // Simplify;

(* checks for a singular solution at circle.  Since control is \
interior, PMP requires singular solution. *)

singCircle = Module[{hamcircle, Dh, DD, i, s},
   hamcircle = (Hupper /. costateCirclesub /. 
         xycirclesub /. {a -> (w1 - w2)/Sqrt[3], 
         b -> w0/3 - 2 w1/3 - 2 w2/3, c -> w0} /. {w0 -> 
         1/3 - t1 - t2, w1 -> 1/3 + t1, w2 -> 1/3 + t2} // Simplify);
   Dh = {D[hamcircle, t1], D[hamcircle, t2]} // Simplify;
   DD[i_] := D[Dh, {t, i}] /. {t -> 0} // Simplify;
   s = Solve[Table[DD[i], {i, 0, 3}] == 0, {C[1], C[3], C[4], C[5]}][[
     1]];
   {hamcircle /. s, costateCirclesub /. s, s}];
(* Lambda = - C[2] J constant: *)

(* add vanishing of hamiltonian *)
circlesub = Module[{vv},
   vv = Solve[(HamCircle /. costateCirclesub /. xycirclesub /. 
          Last[singCircle] // Factor) == 0, C[2]][[1]];
   Join[Last[singCircle] /. vv, vv] // Sort];

(* final solutions to costate *)

AdjointSolCircleLie /. circlesub // Simplify;

costateCirclesub /. circlesub // Simplify;


test = adjoint[HamCircle] - AdjointODECircle /. xycirclesub // 
   Simplify;
   
   
(* Reinhardt I, paper second variation circle, calc repeated and \
simplified. *)
Clear[RtI, Rt, eps, t, u, v, w, a, b, c];
Module[{A1, expJt, expJtI, exp, expinv, Ytilde, cost, Z, 
  controlUnscaled, x, y},
 (* don't need v term *)
 
 expJt = {{Cos[t], -Sin[t]}, {Sin[t], Cos[t]}};
 expJtI = Transpose[expJt];
 A1 = A2 /. {a -> a[t], b -> b[t] + v[t], c -> b[t] - v[t]};
 exp = I2 + A1 eps + A1.A1 eps^2/2;
 expinv = I2 - A1 eps + A1.A1 eps^2/2;
 Ytilde =    
  Series[J + expJtI.expinv.D[exp, t].expJt, {eps, 0, 2}] // Simplify;
 (* this is the cost from Reinhardt paper *)
 
 cost = Series[-3/2 Tr[J.Ytilde], {eps, 0, 2}] // Simplify;
 (* Compute control (u0,u1,u2) up to scalar *)
 
 Z = Ytilde.(I2 -  D[Ytilde, t]) // Simplify;
 controlUnscaled = {Det[{v0, Z.v0}], Det[{v2, Z.v2}], Det[{v4, Z.v4}]};
 Series[controlUnscaled, {eps, 0, 2}] // Simplify;
 Normal[Ytilde];
 (* not unit speed. don't use: {x,y}=zofX[Ytilde]//Simplify;
 (3/2)(x^2+y^2+1)/y//Simplify;
 Tr[Inverse[Ytilde].D[Ytilde,t]] *)
 cost;
 ((Ytilde - J /. t -> 0 // Normal)/eps // Simplify) /. eps -> 0
 ]


(* No possible transition between circular arc and 001 link.  Cannot \
match constants of integration.  By symmetry we cannot make any \
transition from circular arc to a bang-bang link. *)

adjCircleLieInit = 
  AdjointSolLie011 /. u -> 1 /. c0alpha011sub /. {x0 -> 0, 
     y0 -> 1} /. m001sub;
adjCircle001sub = 
  Solve[adjCircleLieInit == 3/2 lambda0 J, {C[1], C[2], C[3]}][[1]];
(* normal solution, take lambda0\[Rule] -1 *)

adjCircleInit = 
  AdjointSol011 /. {C[4] -> 0, C[5] -> 0} /. 
        c0alpha011sub /. {x0 -> 0, y0 -> 1} /. m001sub /. 
     adjCircle001sub /. lambda0 -> -1 // Simplify;
adjCircleInit[[2]] Sqrt[3] // Simplify;
(* lambda2 (switch32 \[LessEqual] 0) , so don't switch between \
circular arc and 001 control *)

Plot[lambda2 /. {lambda2 -> adjCircleInit[[2]]}, {t, -1, 4}];
Series[adjCircleInit[[2]], {t, 0, 3}];
(* switch bad. never get 001 control *)

switch31circle = -switch13 /. xy011sub /. 
         usub /. {lambda1 -> adjCircleInit[[1]], 
         lambda2 -> adjCircleInit[[2]]} /. c0alpha011sub /. {x0 -> 0, 
       y0 -> 1} /. m001sub /. adjCircle001sub // Simplify;
(* need both positive *)
Plot[{adjCircleInit[[2]], 
  switch31circle}, {t, -0.1, 0.1}]
Series[switch31circle, {t, 0, 3}];


(* Singular Arc, edge of simplex case  *)


gr2 = Module[{sig0, sig1, sig2, G2, u0, u2},
   G2 = {{a, b}, {c, d}};
   u0 = {1, 0}; u2 = {-1/2, Sqrt[3]/2};
   sig0 = {a0 t + b0, -1};
   sig2 = (1/2) {{1, -(a0 t + b0)}, {0, 1}}.{Sqrt[3], 1 + s[t]};
   G2 /. Solve[G2.Tx[{u0, u2}] == Tx[({sig0, sig2})], {a, b, c, d}][[
      1]] // Factor];
Det[gr2] // Simplify;
Det[{gr2.{1, 0},
    gr2.{-1/2, Sqrt[3]/2}}] // Simplify;

Yr2 = Inverse[gr2].D[gr2, t] // Simplify;
Det[Yr2] // Simplify;


{"Yr2", Tr[Yr2], Det[Yr2]} // Simplify;

costr2 = Module[{a, b, c, d},
   {{a, b}, {c, d}} = Yr2;
   (3/2) (c - b) // Simplify];

controlsing = Module[{curv, ccr3, a, b, c, d, w0, w1, w2},
   curv = Yr2 + Inverse[Yr2].D[Yr2, t];
   ccr3 = curv - (1/2) Tr[curv] I2 // Simplify;
   {{a, b}, {c, d}} = ccr3;
   w0 = c;
   w1 = 1/4 (2 Sqrt[3] a - 3 b + c);
   w2 = (1/4) (-2 Sqrt[3] a - 3 b + c);
   {w0, w1, w2}/(w1 + w2 + w0) // Simplify];
hamsing = Module[{d2ssub, hamsing},
   d2ssub = Solve[controlsing[[2]] == u, s''[t]][[1]];
   hamsing = 
    lambda1 r + lambda2 s''[t] /. d2ssub /. {s[t] -> s, s'[t] -> r} //
      Simplify;
   hamsing];
(hamsing /. u -> 0) - (hamsing /. u -> 1) // Simplify;
-{D[hamsing, s], D[hamsing, r]} // Simplify;

(* Singular Arc along full simplex *)


(* singular arc lambda1=lambda2=0 *)

Hamsing = 
  Tr[Xupper.{{a, b}, {c, -a}}] + 3/2 lambda0 (x^2 + y^2 + 1)/(y);
{D[Hamsing, x],
    D[Hamsing, y], Hamsing} /. x -> 0 // Simplify;
Solve[{D[Hamsing, x],
    D[Hamsing, y], Hamsing} == 0, {a, b, c}];
Lie[J, Xupper] // Factor;
(* end of rank 3 singular arc *)




