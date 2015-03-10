(* verify results of Section 3 of twist.tex  *)

(* GSp4, page 240  *)

wa = 2(t1-t2) w + 1;
wwa = wa + (t1-t2)^2 el wb;
wb = -2t2 w + 1;
d = t2^2-t1^2;
ww = w + (t1-t2) el wb;

sa[x_]:= x/.{w-> ww/wwa,el-> el/(1+ d el), z-> z/wwa,t1->t2,t2->t1,
             y2->y3,y3->y2};
sb[x_]:= x/.{w->w/wb,xi-> xi+ 2 t2 z,t2->-t2,y1->y2,y2->y1,y3->y4,y4->y3};
Print["calculating x1, x2, x3, x4"];
x1 = xi;
x2 = sb[x1];
x3 = (sa[x2]-x1//Together//Simplify) + x1;
x4 = (sb[x3]-x1//Together//Simplify) + x1;

Print["back substitution"];
crossy = (y2-y4)(y1-y3)/((y3-y4)(y1-y2));
wbbak = (t1+t2)c1(c1-1)(y1-y2)(y4-y3)/((-t1+t2)
            (-y1+y3)(-y1+y4));

checkback:=(
back={x1,x2,x3,x4}/.{xi->y1,el-> (-t2 c1 + t1)/(t2 c1 d),
           z-> (y2-y1)/(2t2),
           w-> 1/(2 t2) - 1/(2 t2) (wbbak)}//Together//Simplify;
back1=back/.c1^2->crossy//Together//Simplify;);

(* verification for 2-regular cases 1 and 2  *)
ysub = 
  {y1-> u0 + u1 e + u2 ep + u3 e ep,
   y2-> u0 - u1 e + u2 ep - u3 e ep,
   y3-> u0 + u1 e - u2 ep - u3 e ep,
   y4-> u0 - u1 e - u2 ep + u3 e ep};

Q1sub=
  {u2 -> u1 u21,u3-> u1 u32 u21};
Q2sub=
  {u1 -> u2 u12,u3-> u1 u31};


omegaf = t1 t2 (t2^2-t1^2)/(2 c1 (-t1+t2 c1)^2 (-y1+y2)^2(-y3+y4)^2 );

jac[z1_,z2_,z3_,z4_,uu1_,uu2_,uu3_,uu4_]:=
Det[{{D[z1,uu1],D[z1,uu2],D[z1,uu3],D[z1,uu4]},
     {D[z2,uu1],D[z2,uu2],D[z2,uu3],D[z2,uu4]},
     {D[z3,uu1],D[z3,uu2],D[z3,uu3],D[z3,uu4]},
     {D[z4,uu1],D[z4,uu2],D[z4,uu3],D[z4,uu4]}}]//Together//Simplify;




(* case 4 *)
newcrossy = (y2 y4)/(y1 y3);
y1c41 = pip u1 + pip^2 u2 + pip^3 u3;
y2c41 = y1c41/.pip-> I pip;
y3c41 = y1c41/.pip-> -pip;
y4c41 = y1c41/.pip-> -I pip;
case41sub = {y1 -> y1c41,y2->y2c41,y3->y3c41,y4->y4c41};
(* in case 41 jac = 4 I pip^6 *)

y1c43 = pip^3 u1 + pip^5 u2 + pip^6 u3;
y2c43 = y1c43/.pip->I pip;
y3c43 = y1c43/.pip -> -pip;
y4c43 = y1c43/.pip -> -I pip;
case43sub = {y1 -> y1c43,y2->y2c43,y3->y3c43,y4->y4c43};
(* in case 43 jac = 4 I pip^14 *)

(* case 5 *)
y1c5 = pip u1 + pip eps u2 + pi eps u3;
y2c5 = y1c5/.{pip-> gamma pip,eps-> -eps};
y3c5 = y1c5/.{pip-> -pip};
y4c5 = y1c5/.{pip ->-gamma pip,eps->-eps};
case5sub = {y1->y1c5,y2->y2c5,y3->y3c5,y4->y4c5};
(* in case 5, jac = -4 eps^2 gamma pi pip^2 *)

(* case 6 *)
y1c61 = pip I u1 + pip^2 I u2 + pip^3 I u3;
y2c61 = y1c61/.{pip-> I pip};
y3c61 = y1c61/.{pip-> -pip};
y4c61 = y1c61/.{pip-> -I pip};
case61sub= {y1->y1c61,y2->y2c61,y3->y3c61,y4->y4c61};
(* in case 61, jac = 4 pip^6 *)

y1c63 = pip^3 I u1 + pip^5 I u2 + pip^6 I u3;
y2c63 = y1c63/.pip-> I pip;
y3c63 = y1c63/.pip -> -pip;
y4c63 = y1c63/.pip -> -I pip;
case63sub = {y1-> y1c63,y2->y2c63,y3->y3c63,y4->y4c63};
(* in case 63, jac = 4 pip^14  *)




