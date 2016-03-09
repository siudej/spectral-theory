(* ::Package:: *)

BeginPackage["TrigInt`"]

TrigInt::usage =
        "TrigInt is faster than Integrate for large trigonometric functions.";

Equilateral::usage=
		"Eigenfunctions of Neumann and Dirichlet Laplacian on the equilateral triangle with vertices (0,0), (1,0), (1/2,Sqrt[3]/2):
		 Equilateral[\"Dirichlet\",\"Symmetric\"] [m,n]  -  1<=m<=n
		 Equilateral[\"Dirichlet\",\"Antisymmetric\"] [m,n]  -  1<=m<n
		 Equilateral[\"Neumann\",\"Symmetric\"] [m,n]  -  0<=m<=n
		 Equilateral[\"Neumann\",\"Antisymmetric\"] [m,n]  -  0<=m<n
		 Equilateral[\"Eigenvalue\"] [m,n]
Eigenfunctions of the right triangle with vertices (0,0), (1,0), (0,Sqrt[3]):
		 Equilateral[\"Dirichlet\",\"Half\"] [m,n]  -  1<=m<n
		 Equilateral[\"Neumann\",\"Half\"] [m,n]  -  0<=m<=n
		 Equilateral[\"Eigenvalue\",\"Half\"] [m,n]
Vertices:
		 Equilateral[]
		 Equilateral[\"Half\"]";

Square::usage=
		"Eigenfunctions of Neumann and Dirichlet Laplacian on the square with vertices (0,0), (1,0), (1,1), (0,1):
		 Square[\"Dirichlet\"] [m,n]  -  m>=1,n>=1
		 Square[\"Neumann\"] [m,n]  -  m>=0,n>=0
		 Square[\"Eigenvalue\"] [m,n]
Eigenfunctions of the right isosceles triangle with vertices (0,0), (1,0), (0,1):
		 Square[\"Dirichlet\",\"Half\"] [m,n]  -  1<=m<n
		 Square[\"Neumann\",\"Half\"] [m,n]  -  0<=m<=n
Vertices:
		 Square[\"Half\"]";

Rayleigh::usage="Rayleigh quotient for functions on triangular domains. 
Many functions can be specified, each having more than one domain, but all domains should be disjoint.

Rayleigh[f1,T11,T12,...,T1n,f2,T21,T22,...,T2m,...]";

Transplant::usage="Linear change of coordinates.

Transplant[Function,TargetTriangle,InitialTriangle]";

Limits::usage="Generates limits for integration over a triangle with one side contained in the x-axis.";

Del::usage="Gradient with respect to x and y.";

Area::usage="Area of a triangle with given vertices.";
Perimeter::usage="Perimeter of a polygon with given vertices.";
T::usage="T[a,b] - triangle with vertices (0,0), (1,0) and (a,b). Optional 3rd variable may contains conditions on a and b.";

TBounds::usage="Write a triangle T[a,b] as inequalities. Can be used for plotting inside RegionPlot.";

TrigIntInit[c_:True]:=(Clear[Global`x,Global`y,Global`m,Global`n,Global`a,Global`b];$Assumptions=Global`m>=0&&Global`n>=0&&{Global`m,Global`n}\[Element]Integers&&Global`b>0&&c);

Begin["`Private`"]

Print["This package uses global x and y as variables, hence these should be cleared. 

It might also be a good idea to setup assumptions for some variables. For example m,n are nonnegative integers and b is positive:
  $Assumptions=m\[GreaterEqual]0&&n\[GreaterEqual]0&&{m,n}\[Element]Integers&&b>0;

Execute TrigIntInit[] to clear variables and setup default assumptions."];

(* TrigInt *)
TrigInt[f_,x__]:=Expand[TInt[TrigReduce[f],x]];
TInt[f_,x__,y_]:=TInt[TInt[f,y],x];
TrigInt::nomatch="No match for `1`. Integrate used.";
(* integrals *)
psin[n_]:=psin[n]=Evaluate[Integrate[y^n Sin[#1+#2 y],{y,#3,#4}]]&;
pcos[n_]:=pcos[n]=Evaluate[Integrate[y^n Cos[#1+#2 y],{y,#3,#4}]]&;
pp[n_]:=pp[n]=Evaluate[Integrate[y^n,{y,#1,#2}]]&;
(* substitutions *)
sub[x_,a_,b_]:={
X_. x^n_. Sin[A_.+B_. x]/;FreeQ[{X,A,B,n},x]:>(X psin[n][A,B,a,b]),
X_. x^n_. Cos[A_.+B_. x]/;FreeQ[{X,A,B,n},x]:>(X pcos[n][A,B,a,b]),
X_. Sin[A_.+B_. x]/;FreeQ[{X,A,B},x]->(X psin[0][A,B,a,b]),
X_. Cos[A_.+B_. x]/;FreeQ[{X,A,B},x]->(X pcos[0][A,B,a,b]),
X_. x^n_./;FreeQ[{X,n},x]:>(X pp[n][a,b]),
X_/;FreeQ[{X},x]->X (b-a),
X_:>(Message[TrigInt::nomatch,X];Integrate[X,{x,a,b}])
};
(* single integral *)
TInt[f_,{x_,a_,b_}]:=(
ff=f/.Sin[X_]:>Sin[Collect[X,{x},Simplify]]/.Cos[X_]:>Cos[Collect[X,{x},Simplify]];
ff=Expand[ff];
ff=ff+f0+f1;
ff=Replace[ff,sub[x,a,b],1];
ff/.f0->0/.f1->0
);

(* eigenfunctions *)
h=1;
r=h/(2Sqrt[3]);
u=r-Global`y;
v=Sqrt[3]/2(Global`x-h/2)+(Global`y-r)/2;
w=Sqrt[3]/2(h/2-Global`x)+(Global`y-r)/2;
EqFun[f_,g_]:=f[Pi (-#1-#2)(u+2r)/(3r)]g[Pi (#1-#2)(v-w)/(9r)]+
	f[Pi #1 (u+2r)/(3r)]g[Pi (2#2+#1)(v-w)/(9r)]+
	f[Pi #2 (u+2r)/(3r)]g[Pi (-2#1-#2)(v-w)/(9r)];
Equilateral["NS"]=Equilateral["Neumann","Symmetric"]=Evaluate[Simplify[EqFun[Cos,Cos]]]&;
Equilateral["NA"]=Equilateral["Neumann","Antisymmetric"]=Evaluate[Simplify[EqFun[Cos,Sin]]]&;
Equilateral["DS"]=Equilateral["Dirichlet","Symmetric"]=Evaluate[Simplify[EqFun[Sin,Cos]]]&;
Equilateral["DA"]=Equilateral["Dirichlet","Antisymmetric"]=Evaluate[Simplify[EqFun[Sin,Sin]]]&;
Equilateral["E"]=Equilateral["Eigenvalue"]=Evaluate[4/27(Pi/r)^2(#1^2+#1 #2+#2^2)]&;
Equilateral["NH"]=Equilateral["Neumann","Half"]=Equilateral["Neumann","Symmetric"]/.Global`x->(1-Global`x)/2/.Global`y->Global`y/2//Simplify;
Equilateral["DH"]=Equilateral["Dirichlet","Half"]=Equilateral["Dirichlet","Antisymmetric"]/.Global`x->(1-Global`x)/2/.Global`y->Global`y/2//Simplify;
Equilateral["EH"]=Equilateral["Eigenvalue","Half"]=Evaluate[1/27(Pi/r)^2(#1^2+#1 #2+#2^2)]&;
Equilateral[]=T[1/2,Sqrt[3]/2];
Equilateral["H"]=Equilateral["Half"]=T[0,Sqrt[3]];

Square["Dirichlet"]=Evaluate[Sin[#1 Pi Global`x]Sin[#2 Pi Global`y]]&;
Square["Neumann"]=Evaluate[Cos[#1 Pi Global`x]Cos[#2 Pi Global`y]]&;
Square["Eigenvalue"]=Evaluate[Pi^2(#1^2+#2^2)]&;
Square["Dirichlet","Half"]=Evaluate[Sin[#1 Pi Global`x]Sin[#2 Pi Global`y]-(-1)^(#1+#2)Sin[#2 Pi Global`x]Sin[#1 Pi Global`y]]&;
Square["Neumann","Half"]=Evaluate[Cos[#1 Pi Global`x]Cos[#2 Pi Global`y]+(-1)^(#1+#2)Cos[#2 Pi Global`x]Cos[#1 Pi Global`y]]&;
Square["Half"]=T[0,1];

(* Transplantation *)
LT[{p1_,p2_,p3_},{q1_,q2_,q3_}]:=Module[{ff},
ff[x_]:={x.{aa,bb}+cc ,x.{dd,ee}+ff};
AffineTransform[{{{aa,bb},{dd,ee}},{cc,ff}}]/.Solve[{ff[p1]==q1,ff[p2]==q2,ff[p3]==q3},{aa,bb,cc,dd,ee,ff}][[1]]
];
ST[p_,q_]:=Thread[{Global`x,Global`y}->LT[p,q][{Global`x,Global`y}]];
Transplant[f_,T1_,T2_]:=f/.ST[T1,T2];

(* Rayleigh quotient *)
Rayleigh[p__]:=Num[p]/Denom[p];
Num[f_,T__List]:=Total[GInt[f,#]&/@{T}];
Num[f_,Longest[T__List],p__]:=Num[f,T]+Num[p];
Denom[f_,T__List]:=Total[NInt[f,#]&/@{T}];
Denom[f_,Longest[T__List],p__]:=Denom[f,T]+Denom[p];
GInt[f_,T_]:=TrigInt[Del[f].Del[f],Limits[T]];
NInt[f_,T_]:=TrigInt[f^2,Limits[T]];

Limits[{{c_,0},{d_,0},{a_,b_}}]:=Sequence[{Global`y,Min[0,b],Max[0,b]},{Global`x,Min[c,d]+(a-Min[c,d])Global`y/b,Max[c,d]+(a-Max[c,d])Global`y/b}];
Limits[{{c_,0},{d_,0},{a_,b_},cond_}]:=Sequence@@Refine[{{Global`y,Min[0,b],Max[0,b]},{Global`x,Min[c,d]+(a-Min[c,d])Global`y/b,Max[c,d]+(a-Max[c,d])Global`y/b}},cond];
(*
Limits[{{c_,0},{d_,0},{a_,b_}}]:=Sequence[{Global`y,0,b},{Global`x,c+(a-c)Global`y/b,d+(a-d)Global`y/b}];
*)
Del[f_]:={D[f,Global`x],D[f,Global`y]};
T[a_,b_]:={{0,0},{1,0},{a,b}};
T[a_,b_,c_]:={{0,0},{1,0},{a,b},c};
Area[{p1_,p2_,p3_}]:=Abs[Cross[Append[p2-p1,0],Append[p3-p1,0]]][[3]]/2//Simplify;
Perimeter[l_]:=Total[Sqrt[#.#]&/@(l-RotateLeft[l])]//Simplify;
TBounds[t_]:=And@@(#[[2]]<=#[[1]]<=#[[3]]&/@{Limits[t]});



End [ ]

EndPackage [ ]



















