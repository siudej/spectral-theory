(*
PolyNeg[P,{x,y},{dx,dy}]: 
	Shows that polynomial P with variables x, y is nonpositive on rectangle (0, 0) (dx, dy). 
	
	Outcome True means the inequality is true. Outcome False means that the algorithm failed to prove the inequality. 
	
	See http://www.ams.org/mathscinet-getitem?mr=MR2779073 for detail.
*)
CumFun[f_, l_] := Rest[FoldList[f, 0, l]];

PolyNeg[P_, {x_, y_}, {dx_, dy_}] := (
    (
	Fold[
	    CumFun[
	    	Min[#1, 0]/dy + #2 &,
		Map[Max[#1, 0] &, #1] dx + #2
	        ]&, 
      	    0, 
	    Reverse[CoefficientList[P, {x, y}]]
	    ] // Max
    ) <= 0);
