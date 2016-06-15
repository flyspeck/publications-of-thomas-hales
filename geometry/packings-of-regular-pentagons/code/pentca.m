kappa = Cos[Pi/5]; 
sigma = Sin[Pi/5];
aK = (1 + kappa) (3 kappa sigma)/2.0;
densityK = (5 - Sqrt[5])/3 // N;
epso = aK - 1.237;

rads[r_, theta_] := r {Cos[theta], Sin[theta]};

area[x_, y_, z_] := x*y*Sin[arc[x, y, z]]/2;

(* law of cosines *)
loc[x_, y_, alpha_] := Sqrt[x^2 + y^2 - 2 x*y*Cos[alpha]];

(* areta *)
aretaEdge[a_, b_, r_] := 
  Module[{x}, (x /. Solve[eta[a, b, x] == r, x])];
  
aretaEdgeMax[a_, b_, r_] := aretaEdge[a,b,r]//Max;

aretaEdgeMin[a_,b_,r_]:= aretaEdge[a,b,r]//Min;

areta[a_, b_, r_] := area[a, b, aretaEdgeMax[a, b, r]];

ell[h_, psi_] := Module[{r, theta},
   r = Sqrt[h^2 + kappa^2];
   theta = ArcCos[h/r];
   Sqrt[1 + r^2 - 2 *r * Cos[psi + theta]]];

ellx[x_, alpha_] := 
  ell[sigma - x, 3 Pi/10 + alpha];

lawsines[a_, alpha_, beta_, gamma_] := 
   (a/Sin[alpha]) {Sin[beta], Sin[gamma]};
   
thetax[xalpha_, alpha_] := 
  Module[{ h, r, phi,psi, psip, elx, ely, 
    theta, thetap},
   h = xalpha - sigma;
   r = Sqrt[h^2 + kappa^2];
   phip = ArcSin[h/r];
   delta = 6 Pi/5 - (alpha + phip);
   elx = loc[r,1,delta];
   ely = loc[r,2 sigma,delta- 3Pi/10];
   thetap = 2Pi/5 - arc[1,elx,ely];
   theta = alpha - thetap;
   {elx,theta, thetap}
   	];

shifttheta[xalpha_,alpha_]:=
  Module[{d,th,thp},
	 {d,th,thp} = thetax[2*sigma - xalpha ,alpha - 2 Pi/5];
	 {d,thp+2Pi/5,th}];

ethetax[xalpha_,alpha_]:=
  If[alpha > 2Pi/5,shifttheta[xalpha,alpha],thetax[xalpha,alpha]];
  
pinwheeledge[alpha_, beta_, xgamma_] := 
  Module[{gamma, xalpha, xbeta},
   gamma = Pi/5 - (alpha + beta);
   {xalpha, xbeta} = 
    lawsines[xgamma, 2 Pi/5 - alpha, 2 Pi/5 - beta, 2 Pi/5 - gamma];
   {ellx[xalpha, alpha], ellx[xbeta, beta], ellx[xgamma, gamma]}];

pinwheelarea[alpha_, beta_, xgamma_] := Module[{a, b, c},
   {a, b, c} = pinwheeledge[alpha, beta, xgamma];
   area[a, b, c]];

pintedge[alpha_,beta_,xalpha_]:=
  Module[{gamma,alphap,betap,gammap,eps,epsp,delta,deltap,
         w1,w2,w3,w4,w5,w6},
         gamma = Pi - (alpha+beta);
         alphap = 2Pi/5 - alpha;
         betap = 2Pi/5 - beta;
         gammap = 2Pi/5 - gamma;
         epsp = Pi - (alphap+2Pi/5);
         eps = Pi - epsp;
         delta = Pi - (betap + eps);
         deltap = Pi - delta;
         {w1,w2} = lawsines[xalpha,epsp,2Pi/5,alphap];
         {w3,w4} = lawsines[2sigma+w2,delta,betap,eps];
         {w5,w6} = lawsines[2sigma,deltap,2Pi/5,gammap];
         Print["alpha=",alpha," beta=",beta," gamma=",gamma,
               "alphap=",alphap," betap=",betap,"gammap= ",gammap,
               "w1,w2,w3,w4,w5,w6",{w1,w2,w3,w4,w5,w6}];
         {ellx[xalpha,alpha],ellx[w4-w6,beta],ellx[w1+w3+w5,gamma]}];
  
pintarea[alpha_, beta_, xalpha_] := 
  Module[{a, b, c},
   {a, b, c} = pintedge[alpha, beta, xalpha];
   area[a, b, c]];
  
         

ljedgealt[alpha_, beta_, x4_] :=
Module[{x1, x2, x3, xgamma, x5, x6, gamma, alphap, betap, gammap, 
    delta1, delta2},
   gamma = 3 Pi/5 - (alpha + beta);
   alphap = 2 Pi/5 - alpha;
   betap = 2 Pi/5 - beta;
   gammap = 2 Pi/5 - gamma;
   delta1 = Pi - (gammap + 2 Pi/5);
   delta2 = Pi - delta1;
   {x3, x5} = lawsines[x4, delta2, betap, alphap];
   x1 = 2 sigma - x3;
   {xgamma, x2} = lawsines[x1, 2 Pi/5, delta1, gammap];
   x6 = x5 - x2;
    Print[{"x4", N[x4], "xgamma", N[xgamma]}];
   {ellx[x4, alpha], ellx[x6, beta], ellx[xgamma, gamma]}
   ];

ljareaalt[alpha_, beta_, xalpha_] := Module[{a, b, c},
   {a, b, c} = ljedgealt[alpha, beta, xalpha];
   area[a, b, c]];

tjedge[alpha_, beta_, xgamma_] :=
  Module[{x1, x2, x3, x4, x5, x6, x7, x8, x9, gamma, alphap, betap, 
    gammap, delta1, delta2, delta3, delta4},
   gamma = Pi - (alpha + beta);
   alphap = 2 Pi/5 - alpha;
   betap = 2 Pi/5 - beta;
   gammap = 2 Pi/5 - gamma;
   delta1 = Pi - (gammap + 2 Pi/5);
   delta2 = Pi - delta1;
   delta3 = Pi - (alphap + delta2);
   delta4 = Pi - (betap + 2 Pi/5);
   {x1, x2} = lawsines[xgamma, delta1, 2 Pi/5, gammap];
   x3 = 2 sigma - x1;
   {x4, x5} = lawsines[x3, delta3, delta2, alphap];
   x6 = 2 sigma - (x5 - x2);
   {x7, x8} = lawsines[x6, 2 Pi/5, betap, delta4];
   x9 = x4 - x7;
   (* Print[{x1,x2,x3,x4,x5,x6,x7,x8,x9}//
   N]; *)
   {ellx[x9, alpha], ellx[x6, beta], 
    ellx[xgamma, gamma]}]; 

tjarea[alpha_, beta_, xgamma_] := Module[{a, b, c},
  {a, b, c} = tjedge[alpha, beta, xgamma];
  area[a, b, c]];



