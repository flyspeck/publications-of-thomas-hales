(* ::Package:: *)

d := t^2;
c := 1;

tau[{x_, y_}] := {1/(x t), 1/(y t)};
rho[{x_, y_}] := {-y, x};
rho3[{x_, y_}] := {y, -x};

plusB[z1_, z2_] := tau[plus[tau[z1], z2]] // Factor;
deltaBx[{x1_, y1_}, {x2_, y2_}] :=
  x2 y1 - x1 y2;
deltaBy[{x1_, y1_}, {x2_, y2_}] :=
   x1 x2 + y1 y2;
deltaB[z1_, z2_] := deltaBx[z1, z2] deltaBy[z1, z2];
deltaA[{x1_, y1_}, {x2_, y2_}] :=
  delta[x1, y1, x2, y2];
plusC[z1_, z2_, i_] := If[i == 0, plus[z1, z2], plusB[z1, z2]]

zB12 = plusB[z1, z2];
z12 = plus[z1, z2];

(* coherence *)

Remainder[zB12 - z12, {e1, e2}, {x1, y1, x2, y2}] // Expand

(* group closure *)
Module[{closureB },
 closureB = 
  ez[zB12] t^4 deltaBx[z1, z2]^2 deltaBy[z1, z2]^2 // Together // 
   Factor;
 Remainder[closureB, {e1, e2}, {x1, y1, x2, y2}] ]

(* easy identities *)

plus[tau[z1], z2] - plus[z1, tau[z2]] // Together
plusB[tau[z1], z2] - plusB[z1, tau[z2]] // Together
rho[plus[z1, z2]] - plus[rho[z1], z2] // Together
rho[plusB[z1, z2]] - plusB[rho[z1], z2] // Together
deltaA[z1, rho[z2]] - deltaA[z1, z2] // Together
deltaB[z1, rho[z2]] + deltaB[z1, z2] // Together

(* dichotomy *)
z2i = {1/(t x0), 1/(t y0)};
dx = x0 y0 Together[deltad[-d, x1, y1, 1/(t x0), 1/(t y0)]];
dBx = t x0 y0 deltaBx[z1, z2i] // Together;
dBy = t x0 y0 deltaBy[z1, z2i] // Together;
 
Module[{polx, gbx, prx},
  polx = {e0, e1, dx, dBx, x0 y0 x1 y1 q - 1};
  gbx = GroebnerBasis[polx, {x0, y0, x1, y1, q}];
  prx = Remainder[{q (x0^2 - y1^2), y0^2 - x1^2, x0 y0 - x1 y1}, 
    gbx, {x0, y0, x1, y1}]]

Module[{poly, gby, pry},
  poly = {e0, e1, dx, dBy, x0 y0 x1 y1 q - 1};
  gby = GroebnerBasis[poly, {x0, y0, x1, y1, q}];
  pry = Remainder[{(x0^2 - y1^2), q (y0^2 - x1^2), x0 y0 - x1 y1}, 
    gby, {x0, y0, x1, y1}]]

(* dichotomy 2 *)
plus[z1, iota[z2]] // Simplify;

gb = GroebnerBasis[{e1, e2, q x1 x2 y1 y2 - 1, 
    x1 y2 + x2 y1, (x1 x2 - y1 y2) - 1 + t^2 x1 x2 y1 y2}, {x1, y1, 
    x2, y2, q}];
Remainder[{x1 - x2, y1 + y2}, gb, {x1, y1, x2, y2}]

(* this has a denominator with 2.
Must assume char ne 2 here. In char 2, image of plusB does not
contain identity and (P,iota(P)) not in domain.  So identity still \
holds.  *)

plusB[z1, iota[z2]] // Simplify;
gb2 = GroebnerBasis[{e1, e2, q x1 x2 y1 y2 - 1, x1 y1 + x2 y2, 
    x1 y1 - x2 y2 - (x2 y1 - x1 y2)}, {x1, y1, x2, y2, q}];
Remainder[{x1 - x2, y1 + y2}, gb2, {x1, y1, x2, y2}] // Factor

(* inverse rules  *)
(* iota[{x_, y_}] := {x, -y}; *)
iota[tau[z1]] - tau[iota[z1]] // Together
iota[rho[z1]] - rho3[iota[z1]] // Together
iota[plus[z1, z2]] - plus[iota[z1], iota[z2]] // Together
iota[plusB[z1, z2]] - plusB[iota[z1], iota[z2]] // Together

(* extended associativity, law1 *)

plus[rho[z1], z2] -
   rho[plus[z1, z2]] // Simplify;
plusB[rho[z1], z2] -
   rho[plusB[z1, z2]] // Simplify;
   
(* general associativity *)
(* extended assoc, law2 *)

zd = plus[plus[z1, z2], z3] - plusB[z1, plus[z2, z3]] // Factor;
pr = Remainder[zd, {e1, e2, e3}, {x1, y1, x2, y2, x3, y3}]

(* all 16 cases *)

genassoc[i1_, i2_, i3_, i4_] :=
  (plusC[plusC[z1, z2, i1], z3, i2] -
     plusC[z1, plusC[z2, z3, i3], i4]) // Factor;
prassoc[i1_, i2_, i3_, i4_] := Module[{},
   Remainder[
    genassoc[i1, i2, i3, i4], {e1, e2, e3}, {x1, y1, x2, y2, x3, y3}]
   ];

Table[prassoc[i1, i2, i3, i4], {i1, 0, 1}, {i2, 0, 1}, {i3, 0, 
  1}, {i4, 0, 1}]



