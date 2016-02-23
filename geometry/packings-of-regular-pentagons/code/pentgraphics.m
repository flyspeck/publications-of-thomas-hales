(* Useful primitives:
Polygon, Circle
*)

(* Kusner graphics *)
Clear[rtf, rtfw, vert, center];
rtf = RotationMatrix[2 Pi/5];
rtfpw[i_] := MatrixPower[rtf, i].{1, 0};
pentvertices = Table[rtfpw[i], {i, 0, 4}];
movepent[x_, y_, 
   t_] := ({x, y} + # &) /@ (RotationMatrix[t].# & /@ pentvertices);
pp[x__] := Polygon@movepent[x];
disk[x__] := Disk[{x}, 0.02];
twopent[{x1_, y1_, t1_}, {x2_, y2_, t2_}] := Module[{},
   Graphics[{EdgeForm[Red], LightRed, pp[x1, y1, t1], pp[x2, y2, t2], 
     Blue, EdgeForm[Blue], Line[{{x1, y1}, {x2, y2}}], disk[x1, y1], 
     disk[x2, y2]}]
   ];
threepent[{x1_, y1_, t1_}, {x2_, y2_, t2_}, {x3_, y3_, t3_}] := 
  Module[{},
   Graphics[{EdgeForm[Red], LightRed, pp[x1, y1, t1], pp[x2, y2, t2], 
     pp[x3, y3, t3], Blue, EdgeForm[Blue], 
     Line[{{x1, y1}, {x2, y2}, {x3, y3}, {x1, y1}}], disk[x1, y1], 
     disk[x2, y2], disk[x3, y3]}]
   ];
delA[dAB_, dAC_, dBC_, thABC_, thBAC_, thCAB_] := 
  Module[{arcA, A1, A2, B1, B2, C1, C2, thA, thB, thC},
   arcA = arc[dAC, dAB, dBC];
   {A1, A2} = {0, 0};
   {B1, B2} = dAB {Cos[arcA], Sin[arcA]};
   {C1, C2} = {dAC, 0};
   thA = arcA + thABC;
   thB = arcA + Pi - thBAC;
   thC = Pi + thCAB;
   threepent[{A1, A2, thA}, {B1, B2, thB}, {C1, C2, thC}]
   ];

twopent[{0, 0, 0.3}, {2, 1, 0.4}]
threepent[{0, 0, 0.3}, {2, 1, 0.4}, {0.2, 2.1, 0.5}]

(* Graphics[{EdgeForm[Blue],LightBlue,pp[0,0,0.2],pp[2,0,Pi/3],Red,\
EdgeForm[Red],Line[{{0,0},{2,0}}],disk[0,0],disk[2,0]}] *)

