(*
Mathematica code related to the Exhaustive Search algorithm in

Michael Rao
"Exhaustive search of convex pentagons which tile the plane"
May 1, 2017
http://perso.ens-lyon.fr/michael.rao/publi/penta.pdf
Citations to "Exhaustive search" algorithm are to page 9
of this preprint.

We check his claim on page 9 that there are 193 non-empty
maximal good sets with nonempty proper ordered angle sets.
This is the finite classification that caps the possibilities
for convex pentagon tilings.
  
We construct 194 good sets (including one empty one), in confirmation
of his work.

Thomas Hales, 2017.
Licensed under MIT license.
*)

forAll[f_, r_] := MemberQ[{{}, {True}}, Union[Map[f, r]]];
SubsetQ[x_, y_] := forAll[MemberQ[y, #] &, x];
feasible[lp_] := ListQ[lp];
infeasible[lp_] := Not[feasible[lp]];
Off[LinearProgramming::lpsnf];
On[Assert];

(* Compat, line 2 of "Exhaustive search" *)
Annihilator[X_] := 
  NullSpace[Join[{{1, 1, 1, 1, 1, 3}}, Map[Join[#, {2}] &, X]]];
table5[j_] := 
  Flatten[Table[{i1, i2, i3, i4, i5}, {i1, 0, j[1]}, {i2, 0, 
     j[2]}, {i3, 0, j[3]}, {i4, 0, j[4]}, {i5, 0, j[5]}], 4];
  
Compat[X_, posv_] := Module[{A, vmax, i, Z, list},
   A = Annihilator[X];
   Z = Table[0, {Length[A]}];
   vmax[i_] := Floor[2/posv[[i]]];
   list = table5[vmax];
   Sort[Select[list, (A.Join[#, {2}] == Z) &]]
   ];

(* ordered angle-set constraints, line 3 of "Exhaustive search" *)

BLP[objective_, X_] := Module[{min, alpha0},
   alpha0 = {{{1, 1, 1, 1, 1}, {3, 0}},
     {{1, 0, 0, 0, 0}, {1, -1}},
     {{1, -1, 0, 0, 0}, {0, 1}},
     {{0, 1, -1, 0, 0}, {0, 1}},
     {{0, 0, 1, -1, 0}, {0, 1}},
     {{0, 0, 0, 1, -1}, {0, 1}},
     {{0, 0, 0, 0, 1}, {0, 1}}};
   min = LinearProgramming[objective, Join[Map[First, alpha0], X], 
     Join[Map[Last, alpha0], Table[{2, 0}, {Length[X]}]]];
   min];

(* extremal angle sets, line 3 continued *)
delta[i_] := Table[If[i == j, 1, 0], {j, 1, 5}];
maxv[i_, X_] := BLP[-delta[i], X];
minv[i_, X_] := BLP[delta[i], X];
mintable[X_] := Table[minv[i, X], {i, 1, 5}];
maxtable[X_] := Table[maxv[i, X], {i, 1, 5}];
minX[mintab_] := Table[mintab[[i, i]], {i, 1, 5}];
maxX[maxtab_] := Table[maxtab[[i, i]], {i, 1, 5}];

(* goodness calculations, line 4 of "Exhaustive search" *)
goodQ1[X_, v_] := 
  infeasible[
   LinearProgramming[{0, 0, 0, 0, 0}, 
    Join[X, {v}, {{1, 1, 1, 1, 1}}],
    Join[Table[{0, 1}, {Length[X]}], {{1, 1}}, {{0, 
       0}}], -Infinity]];
goodQ[X_] := Module[{f, v},
   f[v_] := goodQ1[X, v];
   forAll[f, X]]; 

(* vector u, line 7 of "Exhaustive search" *)
pickU[X_, mtab_, Mtab_] := Module[{alpha1, m4, m5},
   alpha1 = Mtab[[5]];
   m4 = mtab[[4]];
   m5 = mtab[[5]];
   Which[
    m5[[5]] > 0, m5 - alpha1,(*{0,0,0,0,0},*)
    m4[[4]] > 0, 
    m5 - alpha1,
    True, m4 - alpha1]];

(* V, line 8 of "Exhaustive search" *)
makeV[u_, m_, M_] := Module[{vmax, smax, list, n, i},
   vmax[1] = Floor[2/m[[1]]];
   vmax[2] = Floor[2/m[[2]]];
   vmax[3]  = Floor[2/m[[3]]];
   smax[n_] := -Sum[vmax[i]*Max[0, u[[i]]], {i, 1, n - 1}]/u[[n]];
   vmax[4] = Floor[If[m[[4]] > 0, 2/m[[4]],
      smax[4]]];
   vmax[5] = 
    Floor[If[m[[5]] > 0, 2/m[[5]],
      smax[5]]];
   list = table5[vmax];
   Select[list, ((#.u) >= 0 && (#.m) <= 2 && (2 <= #.M)) &]];

(* Initialization of "Exhaustive search", 
   global variables: MaxSet,TreatedSet,counter. *)
Reset := (MaxSet = {}; TreatedSet = {}; counter = 0);
AddMaxSet[C_] := If[Not[MemberQ[MaxSet, C]], AppendTo[MaxSet, C]];
Treated[C_] := 
  If[MemberQ[TreatedSet, C], True, AppendTo[TreatedSet, C]; False];
PrintDiagnostics[depth_]:= 
  Print[counter, "/", depth, " ms:", Length[MaxSet], " ts:",Length[TreatedSet]];

(* Main recursion of "Exhaustive search" *)
Recursion[depth_, X_] :=
  Module[{max5, mins, maxs,mintab, maxtab, maxcounter=100000 (*never reached*),pickedU, compat, V, i},
   max5 = maxv[5, X];
   If[infeasible[max5] || max5[[5]] == 0, "return:pentagon infeasible or zero angle",
    (* else compute extremal angles *)
    mintab = mintable[X];
    mins = minX[mintab];
    maxtab = maxtable[X];
    maxs = maxX[maxtab];
    If[mins[[1]] == 1, "return:pentagon angle pi",
     (* else *)
     compat = Compat[X, max5];
     If[Treated[compat], "return:duplicate case",(*else*)
      If[goodQ[compat], AddMaxSet[compat]];
      pickedU = pickU[compat, mintab, maxtab];
      V = makeV[pickedU, mins, maxs];
      V = Complement[V, compat, {{0, 0, 0, 0, 0}}];
      For[i = 1, i <= Length[V] && counter <= maxcounter, (i++; counter++),
       If[Mod[counter, 1000] == 0,PrintDiagnostics[depth]];
       Recursion[depth + 1, Join[X, {V[[i]]}]]]
      ]]]];

(* takes several minutes to run, counter goes to 32786 *)
runExhaustiveSearch:= (Reset;Recursion[0, {}];Length[MaxSet]);
