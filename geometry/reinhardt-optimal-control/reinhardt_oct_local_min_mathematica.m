(* Proof of the local optimality of the smoothed octagon using automatic differentiation *)
(* The calculations are quite time-consuming! *)


(* quadratic jets *)

Clear[Jet];

Jet /: Plus[Jet[x_], Jet[y_]] := Jet[x + y];

Jet /: Times[Jet[{x0_, x1_, x2_}], Jet[{y0_, y1_, y2_}]] := 
  Jet[{x0 y0, x0 y1 + x1 y0, x0 y2 + 2 x1 y1 + x2 y0}];

Jet /: Exp[Jet[{x0_, x1_, x2_}]] :=
  
  Jet[{Exp[x0], Exp[x0] x1, Exp[x0] (x1^2 + x2)}];

Jet /: E^Jet[{x0_, x1_, x2_}] :=
  
  Jet[{E^x0, E^x0 x1, E^x0 (x1^2 + x2)}];

Jet /: A^Jet[{x0_, x1_, x2_}] :=
  
  Jet[{A^x0, A^x0 x1 Log[A], A^x0 x2 Log[A] + A^x0 x1^2 Log[A]^2}]; 

Jet /: Jet[{x0_, x1_, x2_}]/Jet[{y0_, y1_, y2_}] := 
  Jet[{x0/y0, (x1 y0 - x0 y1)/
     y0^2, (x2*y0^2 - 2*x1*y0*y1 + 2*x0*y1^2 - x0*y0*y2)/y0^3}];

Jet /: Jet[{x0_, x1_, x2_}]^n_Integer := 
  Jet[{x0^n, n x0^(n - 1) x1, 
    n x0^(n - 1) x2 + n (n - 1) x0^(n - 2) x1^2}];

Jet /: Plus[c0_Integer, Jet[{x0_, x1_, x2_}]] := 
  Jet[{c0 + x0, x1, x2}];

Jet /: Plus[Jet[{x0_, x1_, x2_}], c0_Integer] := 
  Jet[{c0 + x0, x1, x2}];

Jet /: Plus[c0_Rational, Jet[{x0_, x1_, x2_}]] := 
  Jet[{c0 + x0, x1, x2}];

Jet /: Plus[Jet[{x0_, x1_, x2_}], c0_Rational] := 
  Jet[{c0 + x0, x1, x2}];

Jet /: Plus[c0_Real, Jet[{x0_, x1_, x2_}]] := Jet[{c0 + x0, x1, x2}];

Jet /: Plus[Jet[{x0_, x1_, x2_}], c0_Real] := Jet[{c0 + x0, x1, x2}];

Jet /: Plus[c0_Interval, Jet[{x0_, x1_, x2_}]] := 
  Jet[{c0 + x0, x1, x2}];

Jet /: Plus[Jet[{x0_, x1_, x2_}], c0_Interval] := 
  Jet[{c0 + x0, x1, x2}];

Jet /: Times[c0_Integer, Jet[{x0_, x1_, x2_}]] := Jet[c0*{x0, x1, x2}];

Jet /: Times[Jet[{x0_, x1_, x2_}], c0_Integer] := Jet[c0*{x0, x1, x2}];

Jet /: Times[c0_Rational, Jet[{x0_, x1_, x2_}]] := 
  Jet[c0*{x0, x1, x2}];

Jet /: Times[Jet[{x0_, x1_, x2_}], c0_Rational] := 
  Jet[c0*{x0, x1, x2}];

Jet /: Times[c0_Real, Jet[{x0_, x1_, x2_}]] := Jet[c0*{x0, x1, x2}];

Jet /: Times[Jet[{x0_, x1_, x2_}], c0_Real] := Jet[c0*{x0, x1, x2}];

Jet /: Times[c0_Interval, Jet[{x0_, x1_, x2_}]] := 
  Jet[c0*{x0, x1, x2}];

Jet /: Times[Jet[{x0_, x1_, x2_}], c0_Interval] := 
  Jet[c0*{x0, x1, x2}];



(* There seems to be a simplification bug in Mathematica.
It fails to rewrite terms of the form 
x*i1 + x*i2 \[Rule] x*(i1+i2), where i1, i2 are intervals.
This is a workaround. *)

JetSimp[{x0_, x1_, x2_}] := Module[{c0, c1, c2},
   c0 = x0;
   c1 = (x1 /. {xj1 -> 0, tj1 -> 0}) + tj1*(Simplify[D[x1, tj1]]) + 
     xj1*(Simplify[D[x1, xj1]]);
   c2 = (x2 /. {xj1 -> 0, tj1 -> 0, xj2 -> 0, yj2 -> 0, t1j2 -> 0, 
        t2j2 -> 0, t3j2 -> 0, t4j2 -> 0}) +
     t1j2*(Simplify[D[x2, t1j2]]) +
     t2j2*(Simplify[D[x2, t2j2]]) +
     t3j2*(Simplify[D[x2, t3j2]]) +
     t4j2*(Simplify[D[x2, t4j2]]) +
     yj2*(Simplify[D[x2, yj2]]) +
     xj2*(Simplify[D[x2, xj2]]) +
     tj1*xj1*(Simplify[D[x2, {tj1, 1}, {xj1, 1}]]) +
     xj1^2*(Simplify[D[x2, {xj1, 2}]/2]) +
     tj1^2*(Simplify[D[x2, {tj1, 2}]/2]);
   Jet[{c0, c1, c2}]];

(* Chopping can lead to some errors of order machine epsilon.
Chopping cleans up the results, but for complete rigor, the chop \
should be removed from the JetSimplify command *)

ChopI[x_] := Chop[x] /. Interval[{0, 0}] -> 0;

JetSimplify[t_] := (t /. Jet -> JetSimp) // ChopI // Simplify;


NN[x_] := N[x, 40];
test = (3*4 + 7 E^x)/(x^2 + E^(5 x)) /. 
    x -> Jet[{Interval[{1, 11/10}], Interval[{4, 45/10}], 
       Interval[{6, 65/10}]}] // NN;
test = Jet[{1, 2, 3}] + Jet[{4, 5, 6}];
tmaxoctI = Interval[tmaxoct] // NN;
y0octI = Interval[y0oct] // NN;
halfI = Interval[1/2] // NN;
rt32 = Interval[Sqrt[3]/2] // NN;
m001I = Interval[1/Sqrt[3]] // NN;


(* Preliminary calculations show that y remains fixed to first order. \
and that the first derivatives of tijet have the indicated form.  The \
undertermined coefficients are
{xj1,tj1},{yj2,xj2,t1j2,t2j2,t3j2,t4j2} *) 
yjet = Jet[{y0octI, 0, yj2}];
xjet = Jet[{0, xj1, xj2}];
t1jet = Jet[{tmaxoctI, tj1, 0}];
t2jet = Jet[{tmaxoctI, -tj1, t2j2}];
t3jet = Jet[{tmaxoctI, tj1, t3j2}];
t4jet = Jet[{tmaxoctI, -tj1, t4j2}];
z0jet = {xjet, yjet};
T0jet = Jet[{0, 0, 0}];
T1jet = T0jet + t1jet;
T2jet = T1jet + t2jet;
T3jet = T2jet + t3jet;
T4jet = T3jet + t4jet;

Rjet = {{Jet[{halfI, 0, 0}], Jet[{-rt32, 0, 0}]}, {Jet[{rt32, 0, 0}], 
     Jet[{halfI, 0, 0}]}} // NN;
R1jet = Inverse[Rjet] // ChopI;

Clear[xyjfnhold, xyjfn, xyjfnDeprecated];
(*
xyjfnhold = \
{x,y}/.xy011sub/.usub/.c0alpha011sub/.m\[Rule]NN[Interval[1/Sqrt[3]]];\

xyjfnDeprecated[{x0_,y0_},t_]:=Release[xyjfnhold];
xy011sub
usub

*)

xyjfn[{x0_, y0_}, t_] := Module[{c0, alpha, u},
   c0 = m001I + x0 // Simplify;
   alpha = y0/c0 // Simplify;
   u = E^(alpha t) // Simplify;
   {-m001I + c0*u, alpha*c0*u} // Simplify // JetSimplify];

z1jet = (Repfrac[Rjet, xyjfn[z0jet, t1jet]] // Simplify) // 
   JetSimplify;
   
z2jet = Repfrac[Rjet, xyjfn[z1jet, t2jet]] // Simplify // JetSimplify;

z3jet = Repfrac[Rjet, xyjfn[z2jet, t3jet]] // Simplify // JetSimplify;

z4jet = Repfrac[Rjet, xyjfn[z3jet, t4jet]] // Simplify // JetSimplify;

xj1sub = Module[{zz1, zz2, x},
    {zz1, zz2} = (z4jet - z0jet // Simplify) /. Jet -> Id;
    x = xj1 /. ({Solve[zz1[[2]] == 0, xj1],
           Solve[zz2[[2]] == 0, xj1]} // Simplify // Flatten)[[1]];
    {xj1 ->  x (* tj1 D[x,tj1] *)}
    ] // ChopI;

xyj2sub = Module[{zz1, zz2, sub, xyj2, xysimp},
    {zz1, zz2} = (z4jet - z0jet // Simplify) /. Jet -> Id;
    sub = 
     Solve[{zz1[[3]] == 0, zz2[[3]] == 0}, {xj2, yj2}] /. xj1sub // 
      Simplify;
    (* cleanup *)
    xyj2 = {xj2, yj2} /. (sub[[1]] /. tj1^2 -> tj12);
    xysimp = 
     Transpose[
      Map[#*Simplify[D[xyj2, #]] &, {t1j2, t2j2, t3j2, t4j2, 
         tj12}] /. {tj12 -> tj1^2}];
    {xj2 -> Apply[Plus, xysimp[[1]]], 
     yj2 -> Apply[Plus, xysimp[[2]]]}
    ] // ChopI;

Jet2Simplify[t_] := 
 JetSimplify[(t /. xyj2sub /. xj1sub)] /. {xj1 -> 0, xj2 -> 0, 
   yj2 -> 0}

z0jetC = z0jet /. xyj2sub /. xj1sub // Jet2Simplify;
z1jetC = z1jet /. xyj2sub /. xj1sub // Jet2Simplify;
z2jetC = z2jet /. xyj2sub /. xj1sub // Jet2Simplify;
z3jetC = z3jet /. xyj2sub /. xj1sub // Jet2Simplify;
Clear[t0jetC, t0jet];
t1jetC = t1jet // Jet2Simplify;
t2jetC = t2jet // Jet2Simplify;
t3jetC = t3jet // Jet2Simplify;
t4jetC = t4jet // Jet2Simplify;

Clear[gammafnj];
(*
gammafnj0hold = Module[{s},
s = StateSolG/.usub/.c0alpha011sub/.m\[Rule]Interval[1/Sqrt[3]]//\
Simplify;
Inverse[(s/.t\[Rule]0)].s//Simplify]/.Interval[{0,0}]\[Rule]0;

gammafnj[{x0_,y0_},t_]:= Release[gammafnj0hold];
*)

gammafnj[{x0_, y0_}, t_] := Module[{c0, alpha, u, m, one, a2c0u},
   c0 = m001I + x0 // Simplify;
   alpha = y0/c0 // Simplify;
   u = E^(alpha t) // Simplify // JetSimplify;
   m = m001I;
   one = Jet[{1, 0, 0}];
   a2c0u = one/(alpha*alpha*c0*u) // Simplify // JetSimplify;
   a2c0u*{{m - m*u + 
         c0*(-1 + u + 
            alpha^2*u), -((-1 + u)*(m^2 + (1 + alpha^2)*c0^2*u - 
             c0*m*(1 + u)))}, {-1 + u, 
        m*(-1 + u) + c0*(1 + alpha^2 - u)*u}} // Simplify // 
    JetSimplify];


g1jet = R1jet.gammafnj[z0jetC, t1jetC] // Simplify // Jet2Simplify;
(* g1jet = (g1jet//Chop)/.Interval[{0,0}]\[Rule]0 *)

g2jet = R1jet.gammafnj[z1jetC, t2jetC] // Simplify // Jet2Simplify;

g3jet = R1jet.gammafnj[z2jetC, t3jetC] // Simplify // Jet2Simplify;

g4jet = R1jet.gammafnj[z3jetC, t4jetC] // NN // Simplify // 
   Jet2Simplify;
   
jetprod = g1jet.g2jet.g3jet.g4jet // Simplify // Jet2Simplify;

Det[jetprod] // Simplify;

(* Use det condition to drop the d coefficient *)
(* Use t1jet as a \
local parameter to make t1j2\[Equal]0 *)

tij2sub = Module[{a, b, c, d, O},
   O = Interval[{0, 0}];
   {{a, b}, {c, d}} = jetprod /. Jet -> Id /. tj1 -> 1;
   Solve[{a[[3]] == O, b[[3]] == O, c[[3]] == O, t1j2 == 0},
     {t1j2, t2j2, t3j2, t4j2}][[1]]
   ];



cost011jhold = 
  cost011 /. c0alpha011sub /. {m -> m001I} /. t1 -> t // Simplify;
cost011jrDep[{x0_, y0_}, t_] := Release[cost011jhold];

Clear[cost011jr];
cost011jr[{x0_, y0_}, t_] := Module[{m, c0, alpha, u, den},
  m = m001I;
  c0 = m001I + x0 // Simplify;
  alpha = y0/c0 // Simplify;
  u = E^(alpha t) // Simplify // JetSimplify;
  den = 2*alpha*alpha*c0*u // Simplify // JetSimplify;
  (3*(-1 - 
         m^2 + (1 + m^2 - 
            2*alpha*c0*m*t + (1 + alpha^2)*c0^2*(-1 + u))*u))/den // 
    Simplify // JetSimplify]


cost1jet = cost011jr[z0jetC, t1jetC] // Jet2Simplify;
(* cost011jrDep[z0jetC,t1jetC]//Jet2Simplify *)


cost2jet = cost011jr[z1jetC, t2jetC] // Jet2Simplify;

cost3jet = cost011jr[z2jetC, t3jetC] // Jet2Simplify;

cost4jet = cost011jr[z3jetC, t4jetC] // Jet2Simplify;

costjet = 
 cost1jet + cost2jet + cost3jet + cost4jet /. tij2sub /. tj1 -> 1 // 
  Jet2Simplify

(*  It works! Second derivative is positive. *)

(* second run results:
Jet[{Interval[{3.\
1260544288436697339206250480472087904757744364271019418064`37.\
3747177027716,3.\
1260544288436697339206250480472088018925212743834968056379`37.\
3747177027716}],0,Interval[{4.\
797611877923857324776577677651350617997868382620516120192`25.\
697795643042276,4.\
7976118779238573247765852613717389673795030179664332894077`25.\
697795643042276}]}] *)

(* First run results: 
Jet[{Interval[{3.12605442884295`,3.1260544288443883`}],Interval[{-6.\
213189962522848`*^-10,6.213149994493962`*^-10}],Interval[{4.\
797416252033407`,4.7978075038607795`}]}] *)


