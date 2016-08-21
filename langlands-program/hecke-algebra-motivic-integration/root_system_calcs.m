(* Construct E7 and E6 root systems inside E8 *)

vm = e6extended = {0, 0, 0, 0, 0, 0, -1, 1};
v0 = e7extended = {-1, 0, 0, 0, 0, 0, 0, 1};
wp = e8extended = -(1/2) {1, 1, 1, 1, 1, 1, 1, 1};

v1 = {1, -1, 0, 0, 0, 0, 0, 0};
v2 = {0, 1, -1, 0, 0, 0, 0, 0};
v3 = {0, 0, 1, -1, 0, 0, 0, 0};
v4  = {0, 0, 0, 1, -1, 0, 0, 0};
v5 = {0, 0, 0, 0, 1, -1, 0, 0};
v6 = {0, 0, 0, 0, 0, 1, -1, 0};
v7 = (1/2) {-1, -1, -1, 1, 1, 1, 1, -1};
v8 = {0, 0, 0, 0, 0, 0, 1, 1};

e8simple = {v1, v2, v3, v4, v5, v6, v7, v8};

(* positive roots *)

pos[v_] := (v.{8, 7.9, 7.8, 7.7, 7.6, 7.5, 7.4, 3} > 0);
neg[v_] := Not[pos[v]];
test = Map[pos, {v1, v2, v3, v4, v5, v6, v7, v8}] // Union

(* E8 root system *)

delta[i_] := delta[i] = Table[If[j == i, 1, 0], {j, 1, 8}];
sign[i_] := sign[i] = If[i == 0, 1, -1];
type1 = Flatten[
   Table[sign[i1] delta[i2] - sign[i3] delta[i4], {i1, 0, 1}, {i2, 1, 
     7}, {i4, i2 + 1, 8}, {i3, 0, 1}], 3];
type2 = Flatten[(1/2) Table[{sign[i1],
      sign[i2], sign[i3] ,
      sign[i4], sign[i5],
      sign[i6], sign[i7],
      sign[Mod[i1 + i2 + i3 + i4 + i5 + i6 + i7, 2]]}, {i1, 0, 
      1}, {i2, 0, 1}, {i3, 0, 1}, {i4, 0, 1}, {i5, 0, 1}, {i6, 0, 
      1}, {i7, 0, 1}], 6];
Length[type1] + Length[type2];
e8roots = Union[type1, type2];
e7roots = Select[e8roots, (#.wp == 0) &];
e6roots = Select[e7roots, (#.v8 == 0) &];
e7pos = Select[e7roots, pos];
e6pos = Select[e6roots, pos];

(* preliminaries for Kottwitz basis *)
check[alpha_] := 2 alpha/(alpha.alpha);
refl[alpha_, w_] := w - (w.check[alpha]) alpha;
test = refl[v1, refl[v1, v2]] - v2 // Union
testvector = {1, 2, 3, 4, 5, 6, 7, 8}; test = 
 refl[v1, refl[v3, testv]];
 
 (* Casselman-Kottwitz structure constants *)
(* <<w alpha>> warning: \
only implemented in simply laced case *)

dbl[w_, alpha_] := Max[0, (w.check[alpha])];
(* Choice of 0 node is the node of degree 3 in the E6 or E7 root \
system. *)
{dist[v1], dist[v2], dist[v3], dist[v4], dist[v5], 
   dist[v6], dist[v7]} = {2, 1, 0, 1, 2, 3, 1};
cc[v_] := cc[v] = (-1)^(dist[v]);
CC[w_, alpha_] := (-1)^(dbl[w, alpha]) cc[alpha]^(w.check[alpha]);

(* action on Kottwitz basis *)

act[alpha_, ee[coef_, w_]] := ee[coef*CC[w, alpha] , refl[alpha, w]];
actlist[alpha_, vv_] := Map[act[alpha, #] &, vv];
actlistrec[xs_, vv_] :=
  
  If[xs == {}, vv, actlistrec[Drop[xs, 1], actlist[xs[[1]], vv]]];

(* reduced word finding *)

eval[xs_, w_, v_] := 
  If[xs == {}, w[v], eval[Drop[xs, 1], w, Simplify[refl[xs[[1]], v]]]];
RR[xs_, w_, posroots_] := Select[posroots, neg[eval[xs, w, #]] &];

(* calculate the E7 linear transformation weyl7. Do for E6 too. *)

A = Table[a[i, j], {i, 1, 8}, {j, 1, 8}];
A7sub = Solve[{A.v0 == v6, A.v1 == v5, A.v2 == v4, A.v3 == v3, 
     A.v4 == v2, A.v5 == v1, A.v6 == v0, A.v7 == v7, 
     A.wp == -wp}, (A // Flatten)][[1]];
B7 = weyl7transform = A /. A7sub;
A6sub =
  Solve[{A.v1 == v5, A.v2 == v4, A.v3 == v3, A.v4 == v7, A.v5 == vm, 
     A.v7 == v2, A.vm == v1, A.wp == wp, 
     A.v8 == v8}, (A // Flatten)][[1]];
B6 = A /. A6sub;
Eigenvalues[B7]
Eigenvalues[B6]

(* find reduced word for weyl7 *)

weyl7[{x1_, x2_, x3_, x4_, x5_, x6_, x7_, 
    x8_}] := {-x6, -x5, -x4, -x3, -x2, -x1, -x8, -x7};
test = Map[weyl7, {v0, v1, v2, v3, v4, v5, v6, v7}] - {v6, v5, v4, v3,
      v2, v1, v0, v7} // Union;

word7 = {v6, v5, v4, v3, v7, v2, v3, v4, v5, v6, v1, v2, v3, v4, v5, 
   v7, v3, v4, v2, v3, v7, v1, v2, v3, v4, v5, v6};
Length[word7];
 eval[word7, 
  weyl7, {x1, x2, x3, x4, x5, x6, x7, 
   x8}] ; (* RR[word7,weyl7,e7pos]//Length *)

 
 (* find reduced word for weyl6 *)
weyl6[v_] := B6.v // Simplify;
word6 = {v1, v2, v3, v4, v5, v7, v3, v4, v2, v3, v7, v1, v2, v3, v4, 
   v5};
test = Length[word6]
test = RR[{}, weyl6, e6pos] // Length
test = RR[word6, weyl6, e6pos] // Length

(* kottwitz basis, action of w *)
kottwitz7 = Map[ee[1, #] &, e7roots];

answer7 = actlistrec[word7, kottwitz7];
(* all the signs are +1 for all roots! *)
test = 
 Map[#[[1]] &, answer7] // Union

kottwitz6 = Map[ee[1, #] &, e6roots];
answer6 = actlistrec[word6, kottwitz6];
test = Map[#[[1]] &, answer6] // Union

(* E7 orbit structure *)

e7fix = Select[e7roots, (weyl7[#] == #) &];
e7unfix = Complement[e7roots, e7fix];
e7orbit = Map[Sort[{#, weyl7[#]}] &, e7unfix] // Union;
null77 = Select[e7orbit, Union[Apply[Plus, #]] == {0} &];
e7orbitsum = Map[Apply[Plus, #] &, e7orbit];

ss = {t1, t2, t3, t4, t5, t6, t7, t8};
{t4, t5, t6, t7, t8} = 
  {t3 s43, t2 s52 , t1 s61, t8 s78, 
   s1238/(t1 t2 t3)};
ev7[v_] := Module[{vv, ts},
   (*ts = {tau-> 1/Sqrt[s7]}; *)
   
   vv = If[2 Abs[v[[1]]] == 1, v + wp, v]; (Apply[Times, 
     Table [ss[[i]]^(vv[[i]]), {i, 1, 8}]](* /.ts*) )];
s7roots = Map[ev7, Join[  e7fix, e7orbitsum ]] // Sort // Tally;
null7 = Select[e7orbitsum, (ev7[#] == 1) &];

test = Map[(# + v7) &, 
     Select[Map[(# - v7) &, e7fix ], ((#.# != 2) && (#.# != 0)) &]][[
    4]] - v7;


lengtheq[i_][x_] := (x[[2]] == i);
Select[Tally[s7roots], lengtheq[2]];

(* back to e7, find phi and epsilon. *)
Clear[t1, t2, t3, t4, t5, t6, t7, t8, ss7, ev7, edd7];

dd = {{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 
    1}} (* /2 *);
ss7 = {t1, t2, t3, t4, t5, t6, t7, t8};
(* phi *)
t1 = dd.{1, 0, 0, 0}; 
t2 = dd.{0, 1, 0, 0}; 
t3 = dd.{0, 0, 1, 0}; 
t4 = dd.{0, 0, 0, 1}; 
t5 = -t4;
t6 = -t3;
t7 = -t2;
t8 = -t1;
edds7[s_, v_] :=
  Module[{vv},
   vv = If[2 Abs[v[[1]]] == 1, v + wp, v]; (Apply[Plus, 
     Table [s[[i]] (vv[[i]]), {i, 1, 8}]] )];
edd7[v_] := edds7[ss7, v];
exp7[s_, v_] := Module[{vv},
   vv = If[2 Abs[v[[1]]] == 1, v + wp, v]; (Apply[Times, 
     Table [s[[i]]^(vv[[i]]), {i, 1, 8}]] )];

evv7 = Map[edd7, e7roots] // Tally // Sort;

(* relation between E7 and F4 *)
f4long = Select[Map[First, evv7], (#.# == 4) &];
f4short = Select[Map[First, evv7],
   (#.# == 2) &];
f4null = {0, 0, 0, 0};
e7f4long = Select[e7roots, MemberQ[f4long, edd7[#]] &];
e7f4short = Select[e7roots, MemberQ[f4short, edd7[#]] &];
e7f4null = Select[e7roots,
  edd7[#] == f4null &]
Map[(# + {1, 1, 1, 1, 1, 1, 1, 1}/2) &, e7f4long];

(* find phi for E7 *)
f4vec = {121, 110, 50, 17};
posF4[x_] := (x.f4vec > 0);
f4pos = Select[Map[First, evv7], posF4];
e7f4 = Select[e7roots, MemberQ[f4pos, edd7[#]] &];
Map[edd7, e7f4] // Tally;
e7vec = {80, 71, 60, 50, 40, 30, 20, 10};
e7indice = Map[{#.e7vec, #} &, e7f4];
Select[e7indice, (#[[1]] <= 0) &];

(* find epsilon *)
Clear[s1, s2, s3, s4, ff, signe7, gg, rr];
Clear[signe7];
signe7[{s1_, s2_, s3_}] := Module[{s4 = (s1*s2*s3)^(-1)},
   {s1, s2, s3, s4, s4, s3, s2, s1}];
ff[s_] := {s, 
   Map[{edd7[#], exp7[signe7[s], #]} &, e7f4long] // Tally   };
ee = Sqrt[Sqrt[-1]];
ff[{-ee, ee, ee}][[2]] // Sort;
(* ok, we have epsilon and phi *)



(************************************)
(* E6 orbit structure *)

e6fix = Select[e6roots, (weyl6[#] == #) &];
e6unfix = Complement[e6roots, e6fix];
null66 = Select[e6orbit, Union[Apply[Plus, #]] == {0} &];
e6orbit = 
  Map[Sort[{#, weyl6[#], weyl6[weyl6[#]]}] &, e6unfix] // Union;
e6orbitsum = Map[Apply[Plus, #] &, e6orbit];
Tally[e6orbitsum];


(* now e6 phi,epsilon *)

Clear[t1, t2, t3, t4, t5, t6, t7, t8, ss7, ev7, edd7];
dd6 = {} ;
ss6 = {t1, t2, t3, t4, t5, t6, t7, t8};
(* phi *)
  t1 =  {1, -1, 0};
t2 = t1; 
t3 = t1 ; 
t4 = -t1 ; 
t5 = -t1;
t6 = -t1;
t7 = {1, 1, -2};
t8 = -t7;
edds6[s_, v_] :=
  Module[{vv},
   vv = If[2 Abs[v[[1]]] == 1, v + wp, v]; (Apply[Plus, 
     Table [s[[i]] (vv[[i]]), {i, 1, 8}]] )];
edd6[v_] := edds6[ss6, v];
exp6[s_, v_] := Module[{vv},
   vv = If[2 Abs[v[[1]]] == 1, v + wp, v]; (Apply[Times, 
     Table [s[[i]]^(vv[[i]]), {i, 1, 8}]] )];

evv6 = Map[edd6, e6roots] // Tally // Sort
  
(* relation of E6 and G2 *)
g2long = Select[Map[First, evv6], (#.# == 24) &];
g2short = Select[Map[First, evv6],
   (#.# == 8) &];
g2null = {0, 0, 0};
e6g2long = Select[e6roots, MemberQ[g2long, edd6[#]] &];
e6g2short = Select[e6roots, MemberQ[g2short, edd6[#]] &];
e6g2null = Select[e6roots,
   edd6[#] == g2null &];
Map[(# + {1, 1, 1, 1, 1, 1, 1, 1}/2) &, e6g2long];
e6g2null // Length

(* find phi for E6 *)
g2vec = {121, 110, 50};
posG2[x_] := (x.g2vec > 0);
g2pos = Select[Map[First, evv6], posG2];
e6g2 = Select[e6roots, MemberQ[g2pos, edd6[#]] &];
Map[edd6, e6g2] // Tally;
e6vec = {62, 61, 60, 58, 31, 30, 29, -40} + 45;
e6indice = Map[{#.e6vec, #} &, e6g2];
e66z = Select[e6indice, (#[[1]] <= 0) &];
e66z // Length
e66z

(* find epsilon for E6 *)
Clear[s1, s2, s3, s4, ff, signe6, gg, rr, ee];
Clear[signe6];
signe6[{s1_, s2_, s4_, s5_, s7_}] := 
  Module[{s8 = s7, s3 = s7/(s1*s2), s6 = s7/(s4*s5)},
   {s1, s2, s3, s4, s5, s6, s7, s8}];
ff[s_] := {s, 
   Map[{edd6[#], exp6[signe6[s], #]} &, e6g2short] // Tally   };
ee = Exp[2 Pi I/3];
ff[{ee, ee^2, ee, 1, 1}][[2]] // Sort



