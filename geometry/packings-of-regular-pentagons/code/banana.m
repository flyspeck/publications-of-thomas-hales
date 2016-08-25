(* 
   This file contains Mathematica functions related to banana domains,
   expressing theta in terms of (ell,theta') and
   theta' in terms of (ell,theta).
   
   This file is not in polished form.
   It contains a collection of graphics that were used in
   numerical exploration of these functions.
   
*)
   
(* read in pentca.m before using these functions *)
(* << "~/Desktop/git/publications-of-thomas-hales/geometry/packings-of-regular-pentagons/code/pentca.m"; *)

mm[x_] := Mod[x, 2 Pi/5, -Pi/5];

elxp[xalpha_, alpha_] := Module[{t = thetax[xalpha, alpha]},
   {t[[3]], t[[1]]}];

(* ---- *)
(* ell,theta' admissible domain *)

Clear[pp, r];
pp = ParametricPlot;
(* r [{x_,y_}]= {y,-x}; *) (* rotate*)
r[{x_, y_}] := {x, y};
ks = Sqrt[(2 kappa)^2 + sigma^2];
thetapks = ArcCos[2 kappa/ks];

V = pp[r[{ArcCos[(1 + kappa)/t], t}], {t, 1 + kappa, 
    Sqrt[(1 + kappa)^2 + sigma^2]}];
IV = pp[{r[{ArcCos[(1 + t^2 - kappa^2)/(2 t)], t}],
    r[{-ArcCos[(1 + t^2 - kappa^2)/(2 t)], t}]}, {t, ks, 1 + kappa}];
III = pp[r[{Pi/5 - ArcCos[2 kappa/t], t}], {t, 2 kappa, ks}];
II = pp[r[{ArcCos[t/2], t}], {t, 2 kappa, 2}];
Ix = pp[r[{ArcCos[2 kappa/t] - Pi/5, t}], {t, ks, 2}];
rotatedrange = {{2 kappa, 2}, {-0.65, 0.3}};
showElThetaXp = Show[{Ix, II, IV, III, V}, Axes -> False, 
  ImageSize -> 200,(* 300 *) 
  PlotRange -> {{-0.3, 0.65}, {2 kappa, 2}}]

(* ---- *)

(* Now (ell,theta) coordinates *)
Clear[pp, r];
pp = ParametricPlot;
 (*r [{x_,y_}]= {y,-x}; *)
 (* rotate*)
r[{x_, y_}] := {x, y};
DV = pp[r[{Pi/5 + ArcCos[(kappa^2 + t^2 - 1)/(2 t kappa)], t}], {t, 
    ks, 1 + kappa}];
DIV = pp[r[{th, (1 + kappa)/Cos[Pi/5 - th]}], {th, Pi/10, 3 Pi/10}];
DIII = pp[r[{th, 2 Cos[th - 2 Pi/5]}], {th, 3 Pi/10, 2 Pi/5}];
DII = pp[r[{th, 2 kappa/Cos[th - Pi/5]}], {th, Pi/5, 2 Pi/5}];
DI = pp[r[{th, 2 Cos[th]}], {th, Pi/10, Pi/5}];
D0 = pp[r[{th, 2 Cos[Pi/10]}], {th, Pi/10, 3 Pi/10}];
rotatedrange = {{2 kappa, 2}, {-2 Pi/5, -Pi/10}};
showElThetaZ = Show[{DI, DII, DIII, DIV, DV}, Axes -> False, 
  ImageSize -> 200,(* 300 *) 
  PlotRange -> {{Pi/10, 2 Pi/5}, {2 kappa, 2}}]

Clear[r, delta, phip];
thetaHpos[lx_, thetap_] := 
  Module[{ly, r, h, xa, delta, phip, alpha, theta},
   ly = loc[1, lx, 2 Pi/5 - thetap];
   r = loc[1, lx, thetap];
   h = Sqrt[r^2 - kappa^2];
   xa = h + sigma;
   delta = 3 Pi/10  + arc[r, 2 sigma, ly];
   phip = ArcSin[h/r];
   alpha = 6 Pi/5 - phip - delta;
   theta = alpha - thetap;
   theta];
thetaPacute[lx_, theta_] :=
  	
  Module[{x, phi, alphap, thetap}, 
   x = Sin[3 Pi/10]/Sin[7 Pi/10 - theta];
   phi = ArcSin[(lx - x) Sin[theta + 3 Pi/10]];
   alphap = phi - 3 Pi/10;
   thetap = 2 Pi/5 - alphap - theta;
   thetap];
  
  ParametricPlot3D[{lx, thp, thetaHpos[lx, thp]},
 {thp, thetapks - Pi/5, 0}, {lx, 
  Cos[thp] + Sqrt[Cos[thp]^2 + kappa^2 - 1], 
  2 kappa/(Cos[thp + Pi/5])}]
  
thetaHpos[Sqrt[2 (1 + kappa)], Pi/10] // N;

cp = ContourPlot[
   thetaHpos[t, thp] == 0.9, {thp, -0.28, 0.628}, {t, 2 kappa, 2}, 
   Axes -> False];
Show[{cp, Ix, II, IV, III, V}, Axes -> False, 
 ImageSize -> 200,(* 300 *) PlotRange -> {{-0.3, 0.65}, {2 kappa, 2}}]

thetaPacute[1 + kappa, Pi/5] // N

dp = ContourPlot[
   thetaPacute[t, th] == -0.3, {th, Pi/10, 2 Pi/5}, {t, 2 kappa, 2}, 
   Axes -> False];
Show[{dp, D0, DI, DII, DIII, DIV, DV}, Axes -> False, 
 ImageSize -> 200,(* 300 *) PlotRange -> {{Pi/10, 2 Pi/5}, {1.8, 2}}]

Sqrt[2 (1 + kappa)] // N

(* ---- *)
(* Now (theta,theta') coordinates *)
Clear[pp, r];
pp = ParametricPlot;
 (*r [{x_,y_}]= {y,-x}; *)
 (* rotate*)
r[{x_, y_}] := {x, y};
E1 = pp[{r[{th, th}], r[{th, -th}]}, {th, 0, Pi/5}];
E2 = pp[{r[{th, 2 Pi/5 - th}], r[{th, th - 2 Pi/5}]}, {th, Pi/5, 
    2 Pi/5}];
E0 = pp[{r[{th, th - Pi/5}], r[{th, -th + Pi/5}]}, {th, 0, 2 Pi/5}];
rotatedrange = {{2 kappa, 2}, {-2 Pi/5, -Pi/10}};
showElThetaE = Show[{E0, E1, E2}, Axes -> False, 
  ImageSize -> 200,(* 300 *) 
  PlotRange -> {{0, 2 Pi/5}, {-Pi/5, Pi/5}}]

ellz[theta_, thetap_] := Module[{alpha, alphap, x, y},
   alpha = theta + thetap;
   alphap = 2 Pi/5 - alpha;
   x = Sin[3 Pi/10]/Sin[theta + 3 Pi/10];
   y = Sin[alphap + 3 Pi/10]/Sin[thetap + alphap + 3 Pi/10];
   {x, y, (x + y)}];

ellz[0.4318545, 0.201379]

ep = ContourPlot[
   ellz[th, thp] == 1.809, {th, 0, 2 Pi/5}, {thp, -Pi/5, Pi/5}, 
   Axes -> False];
Show[{ep, E0, E1, E2}, Axes -> False, 
 ImageSize -> 200,(* 300 *) PlotRange -> {{0, 2 Pi/5}, {-Pi/5, Pi/5}}]



