(* Mathematica code for the Edwards elliptic curve group law verification *)
Clear[plus,c,d,e,delta,deltad];

e[x_, y_] := (c x^2 + y^2 - 1 - d x^2 y^2);
{e1,e2,e3} = {e[x1,y1],e[x2,y2],e[x3,y3]};

delta[x1_, y1_, x2_, y2_] := 1 - d^2 x1^2 x2^2 y1^2 y2^2;
delta12 = delta[x1,y1,x2,y2];
delta23 = delta[x2,y2,x3,y3];
deltad[d_, x1_, y1_, x2_, y2_] := 1 + d x1 x2 y1 y2;

delta12 - deltad[d, x1, y1, x2, y2] deltad[-d, x1, y1, x2, y2] // Simplify

plus[{x1_, y1_}, {x2_, y2_}] :=
  {
   (x1 y2 + y1 x2)/(1 + d x1 x2 y1 y2),
   (y1 y2 - c x1 x2)/(1 - d x1 x2 y1 y2)
   };
{x3p, y3p} = plus[{x1, y1}, {x2, y2}];
{x1p, y1p} = plus[{x2, y2}, {x3, y3}];

(* group closure *)
groupclosure = e[x3p, y3p] delta[x1, x2, y1, y2]^2 // Together // Factor;
polyclosure = PolynomialReduce[
  groupclosure, {e1,e2}, {x1, y1, x2, y2}] // Expand;

(* associativity *)
deltaX =
delta12 * delta23 *
deltad[d,x3p, y3p, x3, y3] * 
deltad[d,x1, y1, x1p, y1p] // Factor;

deltaY = deltaX/.{d->(-d)};

{gx, gy} = (plus[{x3p,y3p}, {x3, y3}] - 
       plus[{x1, y1}, {x1p,y1p}]) // Together // Factor;
       
gxpoly = gx * deltaX//Factor;
gypoly = gy * deltaY//Factor;

polyassoc = PolynomialReduce[{gxpoly, gypoly}, {e1,e2,e3}, 
                    {x1, y1, x2, y2, x3, y3}] // Simplify // Expand;

(* completeness identity *)

complete = 
{d^2 x1^2 x2^2 y2^2 e1 +  (1 - d x1^2) delta[x1, y1, x2, y2] - 
  d x1^2 e2 , (1 - c d x1^2 x2^2) (1 - d x1^2 y2^2) };

completereduce = complete//Expand;

(* Bernstein-Lange version of completeness
complete = {
d x1^2 y1^2 (t x2 + y2)^2 - e2 d x1^2 y1^2 + 
      e1 + (1 - y1^2) delta12 - (t x1 + d x1 y1 x2 y2 y1)^2 +
    (c - t^2) x1^2 (-1 + d x2^2 y1^2),
           d x1^2 y1^2 (t x2 - y2)^2 - e2 d x1^2 y1^2 + 
      e1 + (1 - y1^2) delta12 - (t x1 - d x1 y1 x2 y2 y1)^2 +
           (c - t^2) x1^2 (-1 + d x2^2 y1^2)};
*)

(* group addition and family of hyperbolas *)

hyp[{x_, y_}] := x y + a y + b x + a;

absub = First[
   Solve[{hyp[{x1, y1}] == 0, hyp[{x2, y2}] == 0}, {a, b}] // 
    Simplify];

neg[{x_, y_}] := {-x, y};

hypsum = delta[x1, y1, x2, y2]*
   (x1 (1 + y2) - x2 (1 + y1))*
   (hyp[neg[plus[{x1, y1}, {x2, y2}]]] /. absub) // 
   Factor;

hypreduce= PolynomialReduce[hypsum, {e1, e2}, {x1, y1, x2, y2}]
     
(* convert to HOL Light *)

Clear[ToHOL];
ts[x_] := ToString[x];
list[x_]:= Apply[List,x];
join[x__] := StringJoin[x];
pjoin[x__] := join["(", x, ")"];
rjoin[x_, t_] := pjoin[Riffle[x, t]];
ToHOL[Power[x_, n_]] := pjoin[ ToHOL[x], " pow ", ts[n]];
ToHOL[x_Times] := rjoin[Map[ToHOL,list[x]], "*"];
ToHOL[x_Plus] := rjoin[Map[ToHOL, list[x]], "+"];
ToHOL[x_Integer /; x >= 0] := join["&", ts[x]];
ToHOL[x_Integer /; x < 0] := pjoin["-- &", ts[-x]];
ToHOL[x_Symbol] := ts[x];

(* HOL Light material *)
(* completeness *)
join[ToHOL[complete[[1]]]," = ",ToHOL[complete[[2]]]];

(* closure *)
join[ToHOL[groupclosure]," = ",
     ToHOL[e1]," * ",
     ToHOL[polyclosure[[1,1]]]," + ",
     ToHOL[e2]," * ",
     ToHOL[polyclosure[[1,2]]]];

(* associativity *)
join[ToHOL[gxpoly], " = ",
     ToHOL[e1]," * ",
     ToHOL[polyassoc[[1,1,1]]], " + ",
     ToHOL[e2]," * ",
     ToHOL[polyassoc[[1,1,2]]], " + ",
     ToHOL[e3], "  * ",
     ToHOL[polyassoc[[1,1,3]]]];

join[ToHOL[gypoly], " = ",
     ToHOL[e1]," * ",
     ToHOL[polyassoc[[2,1,1]]], " + ",
     ToHOL[e2]," * ",
     ToHOL[polyassoc[[2,1,2]]], " + ",
     ToHOL[e3], "  * ",
     ToHOL[polyassoc[[2,1,3]]]];
