(*  These are mathematica functions used in the paper
    Twisted Endoscopy ... GL(4)...
    It gives some preliminary calculations for the two-regular
      germ in the biquadratic situation
*)

cross  = (x2-x4)(x1-x3)/(x3-x4)/(x1-x2);
crossy = (y2-y4)(y1-y3)/((y3-y4)(y1-y2));
xtoy = {x1->y1,x2->y2,x3->y3,x4->y4};
ytox = {y1->x1,y2->x2,y3->x3,y4->x4};

xsub = {x1-> u1 + e1 u2 + e2 u3 + e1 e2 u4,
        x2-> u1 - e1 u2 + e2 u3 - e1 e2 u4,
        x3-> u1 + e1 u2 - e2 u3 - e1 e2 u4,
        x4-> u1 - e1 u2 - e2 u3 + e1 e2 u4};

crossu=cross/.xsub//Factor;

squ:= cong1 e2 u3/(e1 u2);

(* cong1^2 is cong2 *)
cong2 =  (u2^2*(-u3 + e1*u4)*
          (u3 + e1*u4))/(u3^2*(-u2 + e2*u4)*(u2 + e2*u4))

(* used in biquadratic *)


g1[x_] := x
 
g2[x_] := x /. {e1 -> -e1, t1 -> -t1}
 
g3[x_] := x /. {e2 -> -e2, t2 -> -t2}
 
g4[x_] := g2[g3[x]]
 
par1[x_] := Together[(g1[x] + g2[x] + g3[x] + g4[x])/4]
 
par2[x_] := Together[(g1[x] - g2[x] + g3[x] - g4[x])/4]
 
par3[x_] := Together[(g1[x] + g2[x] - g3[x] - g4[x])/4]
 
par4[x_] := Together[(g1[x] - g2[x] - g3[x] + g4[x])/4]

rot[x_]:= x/.{e1->e2,e2->e1,t1->t2,t2->t1,u2->u3,u3->u2,cong1->1/cong1};

diffy=
(t1*t2*(-t1 + t2)*(t1 + t2)*(-3*y1*y2 + sqrtc*y1*y2 - y1*y3 + 
      3*sqrtc*y1*y3 + 4*y2*y3 - 4*sqrtc*y2*y3 + 4*y1*y4 - 4*sqrtc*y1*y4 - 
      y2*y4 + 3*sqrtc*y2*y4 - 3*y3*y4 + sqrtc*y3*y4))/
  (2*(y1*y2 - sqrtc*y1*y3 - y2*y3 + sqrtc*y2*y3 - y1*y4 + sqrtc*y1*y4 - 
      sqrtc*y2*y4 + y3*y4)*(t2*y1*y2 + t1*y1*y3 - sqrtc*t1*y1*y3 - 
       sqrtc*t2*y1*y3 - t1*y2*y3 + sqrtc*t1*y2*y3 - t2*y2*y3 + 
       sqrtc*t2*y2*y3 - t1*y1*y4 + sqrtc*t1*y1*y4 - t2*y1*y4 + 
       sqrtc*t2*y1*y4 + t1*y2*y4 - sqrtc*t1*y2*y4 - sqrtc*t2*y2*y4 + t2*y3*y4
       )^2);

diffx=diffy/.ytox;


sa[x_]:= x/.{t1->t2,t2->t1,x2->x3,x3->x2,sqrtc->1/sqrtc,y2->y3,y3->y2,
             e1->e2,e2->e1,u2->u3,u3->u2};

(* The Power2 term in diffx can be simplified  to *)

newden =  t2 (-x1 + x3) (-x2 + x4)/sqrtc +
             t1 (-x1 + x2) (x3 - x4);

newden = ((-t1 + sqrtc t2) (-x1 + x3) (-x2 + x4))/cross;

oldden =  t2*x1*x2 + t1*x1*x3 - sqrtc*t1*x1*x3 - 
            sqrtc*t2*x1*x3 - t1*x2*x3 + 
   sqrtc*t1*x2*x3 - t2*x2*x3 + sqrtc*t2*x2*x3 - 
            t1*x1*x4 + sqrtc*t1*x1*x4 - 
   t2*x1*x4 + sqrtc*t2*x1*x4 + t1*x2*x4 - sqrtc*t1*x2*x4 - 
             sqrtc*t2*x2*x4 + t2*x3*x4;
 
difx = diffx Power[oldden,2]/(-1+sqrtc)^2/Power[newden,2]//Factor;

(* The main pieces of difx are f1x and f2x  *)

f1x =  -3*x1*x2 + sqrtc*x1*x2 - x1*x3 + 3*sqrtc*x1*x3 + 4*x2*x3 - 4*sqrtc*x2*x3 + 
   4*x1*x4 - 4*sqrtc*x1*x4 - x2*x4 + 3*sqrtc*x2*x4 - 3*x3*x4 + sqrtc*x3*x4;

(* this is a simpler form of f1x *)
f1xx = (x1-x2)(x3-x4) (sqrtc-1)^3;

f2x =  x1*x2 - sqrtc*x1*x3 - x2*x3 + sqrtc*x2*x3 - x1*x4 + sqrtc*x1*x4 - 
   sqrtc*x2*x4 + x3*x4;

(* This is equal to f2x  *)
f2xx = (x1-x2)(x3-x4)(sqrtc-1) sqrtc;

dix = difx f1xx f2x/(f1x f2xx)//Factor;

difu= dix/.xsub//Together//Simplify;

(*  Here is some chaff from way back when   *)

chaff:=(
diffu=diffx/.xsub//Together//Simplify;
diffu1 = 32 diffu/(t1 t2 (t1-t2) (t1+t2))//Factor;

denom[x_]:= x1 x2 x3 + x1 x2 x4 + x1 x3 x4 + 
            x2 x3 x4 + 4 x1 x2 x3 x4/x;

full[x_]:= x1 x2 x3 x4/denom[x]//Together;

JacRow[x_,z1_,z2_,z3_,z4_]:=
     {D[fx[x],z1],D[fx[x],z2],D[fx[x],z3],D[fx[x],z4]}//Simplify;
Jac[z1_,z2_,z3_,z4_]:=
     Det[{JacRow[x1,z1,z2,z3,z4],JacRow[x2,z1,z2,z3,z4],
          JacRow[x3,z1,z2,z3,z4],JacRow[x4,z1,z2,z3,z4]}]//Simplify;
Jac1[z1_,z2_,z3_,z4_]:= Jac[z1,z2,z3,z4] (difx/.newsub)//Simplify//Factor;

fx[x_]:= (x/.newsub);
fy[x_]:= Factor[Simplify[Together[fx[full[x]]]]];
fx1:=fy[x1]; fx2:=fy[x2]; fx3:= fy[x3]; fx4:=fy[x4];

sub1 := {x2 -> -(Z12*(x4 - x1)) + x1, x3 -> -(Z13*(x4 - x1)) + x1};
 
sub2 = {x2 -> X1*Z12 - Z12*(x4 - X1*Z12), x3 -> X1*Z12 - (x4 - X1*Z12)*Z13, 
   x1 -> X1*Z12};
 
sub3 = {x2 -> X1*Z12 - Z12*(X1*X4 - X1*Z12), 
   x3 -> X1*Z12 - (X1*X4 - X1*Z12)*Z13, x1 -> X1*Z12, x4 -> X1*X4};
 
sub4 = {x2 -> X1*Z12 - Z12*(X1^n*X4 - X1*Z12), 
   x3 -> X1*Z12 - (X1^n*X4 - X1*Z12)*Z13, x1 -> X1*Z12, x4 -> X1^n*X4};

n:=1;
 
sub5 = {x2 -> X1^2*ZZ12 - X1*ZZ12*(X1^2*X4 - X1^2*ZZ12), 
   x3 -> X1^2*ZZ12 - (X1^2*X4 - X1^2*ZZ12)*Z13, x1 -> X1^2*ZZ12, 
   x4 -> X1^2*X4, Z12 -> X1*ZZ12};
 
sub6 = {x2 -> X1*(-1 + X1*ZZZ12) - 
     (-1 + X1*ZZZ12)*(X1^2*X4 - X1*(-1 + X1*ZZZ12)), 
   x3 -> X1*(-1 + X1*ZZZ12) - (X1^2*X4 - X1*(-1 + X1*ZZZ12))*Z13, 
   x1 -> X1*(-1 + X1*ZZZ12), x4 -> X1^2*X4, Z12 -> -1 + X1*ZZZ12};
 
sub7 = {x2 -> X1*Z12 - Z12*(X1^2*X4 - X1*Z12), 
   x3 -> X1*Z12 - (-1 + X1*ZZ13)*(X1^2*X4 - X1*Z12), x1 -> X1*Z12, 
   x4 -> X1^2*X4, Z13 -> -1 + X1*ZZ13};








);


(* This is for case 2b  *)

case2bsub=
{y1 ->                u0 + pip u1 + pip^2 u2 + pip^3 u3,
 y2 -> zeta^( ell) ( u0 + pip u1 zeta + pip^2 u2 zeta^2 + pip^3 zeta^3 u3),
 y3 -> zeta^(2 ell) (u0 + pip u1 zeta^2 + pip^2 u2 zeta^4 + pip^3 zeta^6 u3),
 y4 -> zeta^(3 ell) (u0 + pip u1 zeta^3 + pip^2 u2 zeta^6 + pip^3 zeta^9 u3)};
