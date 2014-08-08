(* ::Package:: *)

BeginPackage["WeylAlgebra`"];
(*
dim::usage = "Dimension";
u::usage = "Spinor component";
v::usage = "Spinor component";
ubar::usage = "Spinor component";
vbar::usage = "Spinor component";
slashed::usage = "slashed[p] = \!\(\*SubscriptBox[\(p\), \(a\)]\)\!\(\*SuperscriptBox[\(\[Gamma]\), \(a\)]\)";
mass::usage = "mass";
FP::usage = "Feynman parameters";
mom::usage = "mom[p,\[Mu]] = \!\(\*SuperscriptBox[\(p\), \(\[Mu]\)]\); mom[p,Null,\[Mu]] = \!\(\*SubscriptBox[\(p\), \(\[Mu]\)]\).";
mom2::usage = "mom2[p] is momentum squared.";
gamma::usage = "Gamma matrix : gamma[x] = \!\(\*SuperscriptBox[\(\[Gamma]\), \(x\)]\)";
g::usage = "Metric \!\(\*SubscriptBox[\(g\), \(\[Mu]\[Nu]\)]\)";
gH::usage = "Metric \!\(\*SuperscriptBox[\(g\), \(\[Mu]\[Nu]\)]\)";
eps::usage = "Levi-Civita Tensor \!\(\*SubscriptBox[\(\[CurlyEpsilon]\), \(\[Mu]\[Nu]\[Rho]\[Sigma]\)]\)";
epsH::usage = "Levi-Civita Tensor \!\(\*SuperscriptBox[\(\[CurlyEpsilon]\), \(\[Mu]\[Nu]\[Rho]\[Sigma]\)]\)";
delta::usage = "Identity matrix delta[a,b]=\!\(\*SubsuperscriptBox[\(\[Delta]\), \(b\), \(a\)]\). Note the order.";
five::usage = "\!\(\*SubscriptBox[\(\[Gamma]\), \(5\)]\). gamma[5] is interpreted as this.";
PL::usage = "Left projection";
PR::usage = "Right projection";

CDot::usage = "Inner product in Minkowski space";

DF::usage = "Remark that the index (or momentum) lives in 4-dimensional space (relevant if dim =!= 4)";
DX::usage = "Remark that the index (or momentum) lives in (D-4)-dimensional (i.e. extra dimensional) space";

ConstructSpinorProduct::usage = "Input wrapper for SpinorProduct.";
SpinorProduct::usage = "Dirac Spinor product.";
SpinorSimplify::usage = "Simpilfy spinor product";
SpinorFullSimplify::usage = "FullSimpilfy spinor product";
SpinorSquared::usage = "Take squared of SpinorProduct";
SpinSum::usage = "Take SpinSUm of SpinorProduct";
SpinorTrace::usage = "Take Trace of SpinorProduct";
ExpandEpsilons::usage = "Expand Levi-Civita tensor";
OrderEpsilons::usage = "Order Levi-Civita tensor";

RewriteDX::usage = "Rew (D-4)-dimensional component";
RewriteDF::usage = "Rewrite 4-dimensional component";
Begin["Private`"]
*)


Unprotect[SubsuperscriptBoxSub,SpinorL,SpinorH,SpinorBarL,SpinorBarH,SigmaL,SigmaH,SigmaBarL,SigmaBarH,EpsilonH,EpsilonL,Tensor,Spinor,SpinorBar,Sigma,SigmaBar,Epsilon,\[Sigma],\[Epsilon],x,TensorList,TensorListBox,TensorListSimplify,SpinorToH,Dx];
Remove[SubsuperscriptBoxSub,SpinorL,SpinorH,SpinorBarL,SpinorBarH,SigmaL,SigmaH,SigmaBarL,SigmaBarH,EpsilonH,EpsilonL,Tensor,Spinor,SpinorBar,Sigma,SigmaBar,Epsilon,\[Sigma],\[Epsilon],x,TensorList,TensorListBox,TensorListSimplify,SpinorToH,Dx];

SubsuperscriptBoxSub[z_,{},    {},    f_]:=z
SubsuperscriptBoxSub[z_,a_List,{},    f_]:=SubscriptBox[z,MakeBoxes[#,f]]&@Row[a]
SubsuperscriptBoxSub[z_,{},    b_List,f_]:=SuperscriptBox[z,MakeBoxes[#,f]]&@Row[b]
SubsuperscriptBoxSub[z_,a_List,b_List,f_]:=SubsuperscriptBox[z,MakeBoxes[#1,f],MakeBoxes[#2,f]]&@{Row[a],Row[b]}
Spinor   /:MakeBoxes[obj:Spinor[z_[x]],                   f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@StyleBox[MakeBoxes[z,f],{Bold,Blue}]
SpinorBar/:MakeBoxes[obj:SpinorBar[z_[x]],                f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@StyleBox[MakeBoxes[OverBar[z],f],{Bold,Blue}]
Spinor   /:MakeBoxes[obj:Spinor[z_],                   f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@StyleBox[MakeBoxes[z,f],Bold]
SpinorBar/:MakeBoxes[obj:SpinorBar[z_],                f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@StyleBox[MakeBoxes[OverBar[z],f],Bold]
Sigma    /:MakeBoxes[obj:Sigma[low_List,high_List],    f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@SubsuperscriptBoxSub[StyleBox[MakeBoxes[\[Sigma],f],Bold],low,high,f]
SigmaBar /:MakeBoxes[obj:SigmaBar[low_List,high_List], f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@SubsuperscriptBoxSub[StyleBox[MakeBoxes[OverBar[\[Sigma]],f],Bold],low,high,f]
Epsilon  /:MakeBoxes[obj:Epsilon,                      f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@StyleBox[MakeBoxes[\[Epsilon],f],Bold]
Tensor   /:MakeBoxes[obj:Tensor[z_,low_List,high_List],f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@SubsuperscriptBoxSub[MakeBoxes[z,f],low,high,f]

SpinorL[x_,a_]:=Tensor[Spinor[x],{a},{}]
SpinorH[x_,a_]:=Tensor[Spinor[x],{},{a}]
SpinorBarL[x_,a_]:=Tensor[SpinorBar[x],{OverDot[a]},{}]
SpinorBarH[x_,a_]:=Tensor[SpinorBar[x],{},{OverDot[a]}]
SigmaL[\[Mu]_,a_,b_]:=Tensor[Sigma[{\[Mu]},{}],{a,OverDot[b]},{}]
SigmaH[\[Mu]_,a_,b_]:=Tensor[Sigma[{},{\[Mu]}],{a,OverDot[b]},{}]
SigmaBarL[\[Mu]_,a_,b_]:=Tensor[SigmaBar[{\[Mu]},{}],{},{OverDot[a],b}]
SigmaBarH[\[Mu]_,a_,b_]:=Tensor[SigmaBar[{},{\[Mu]}],{},{OverDot[a],b}]
EpsilonH[a_,b_]:=Tensor[Epsilon,{},{a,b}]
EpsilonL[a_,b_]:=Tensor[Epsilon,{a,b},{}]

Tensor[Times[a:TensorList[___],b___],p___]:=Times[a,Tensor[Times[b],p]]
Tensor[Plus[a_,b__],p__]:=Plus[Tensor[a,p],Tensor[Plus[b],p]]
Spinor[0]:=0
SpinorBar[0]:=0
Tensor[0,__]:=0

Dx/:MakeBoxes[obj:Dx[z_,\[Mu]_],f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@RowBox[{SubscriptBox[MakeBoxes["\[PartialD]",f],MakeBoxes[\[Mu],f]],MakeBoxes[z,f]}]
Dx[Plus[a_,b__],m_]:=Plus[Dx[a,m],Dx[Plus[b],m]]
Dx[Times[a_,b__],m_]:=Times[Dx[a,m],b]+Times[a,Dx[Times[b],m]]
Dx[Tensor[x_,b__],\[Mu]_]:=Tensor[Dx[x,\[Mu]],b]
Dx[TensorList[a_,b___],\[Mu]_]:=TensorList[Dx[a,\[Mu]],b]+TensorList[a,Dx[TensorList[b],\[Mu]]]


TensorList::DuplicatedIndices = "The index `1` duplicated.";

TensorList/:MakeBoxes[obj:TensorList[a__],f:StandardForm|TraditionalForm]:=InterpretationBox[#,obj]&@TensorListBox[a,f]
TensorListBox[___,Tensor[_,_,{___,p_Symbol,___}],___,Tensor[_,_,{___,p_Symbol,___}],___]:=(Message[TensorList::DuplicatedIndices, p]; Abort[])
TensorListBox[___,Tensor[_,{___,p_Symbol,___},_],___,Tensor[_,{___,p_Symbol,___},_],___]:=(Message[TensorList::DuplicatedIndices, p]; Abort[])
TensorListBox[a___,Tensor[x_,xlow_,{xhigh___,p_Symbol}],Tensor[y_,{p_Symbol,ylow___},yhigh_],b___,f_]:=TensorListBox[a,Tensor[x,xlow,{xhigh}],Tensor[y,{ylow},yhigh],b,f]
TensorListBox[a___,Tensor[x_,{xlow___,OverDot[p_Symbol]},xhigh_],Tensor[y_,ylow_,{OverDot[p_Symbol],yhigh___}],b___,f_]:=TensorListBox[a,Tensor[x,{xlow},xhigh],Tensor[y,ylow,{yhigh}],b,f]
TensorListBox[obj:RepeatedNull[Tensor[__]],f:StandardForm|TraditionalForm]:=RowBox[Flatten[{"[",MakeBoxes[#,f]&/@{obj},"]"}]]

(*
TensorListSimplify[a___,b:Tensor[s:(Spinor|SpinorBar)[_],__],c___,d_,e:Tensor[s_,__],f___]:=TensorListSimplify[TensorList[a,b,c,Swap[d,e],f]]

TensorListSimplify[a___,Tensor[Spinor[x_],{p_Symbol},{}],Tensor[Spinor[x_],{q_Symbol},{}],b___]:=Module[{u},u=Unique["\[Alpha]"];TensorListSimplify[TensorList[a,1/2 EpsilonL[p,q],SpinorH[x,u],SpinorL[x,u],b]]]
TensorListSimplify[a___,Tensor[Spinor[x_],{},{p_Symbol}],Tensor[Spinor[x_],{},{q_Symbol}],b___]:=Module[{u},u=Unique["\[Alpha]"];TensorListSimplify[TensorList[a,-(1/2)EpsilonH[p,q],SpinorH[x,u],SpinorL[x,u],b]]]
TensorListSimplify[a___,Tensor[SpinorBar[x_],{OverDot[p_Symbol]},{}],Tensor[SpinorBar[x_],{OverDot[q_Symbol]},{}],b___]:=Module[{u},u=Unique["\[Alpha]"];TensorListSimplify[TensorList[a,-(1/2)EpsilonL[OverDot[p],OverDot[q]],SpinorBarL[x,u],SpinorBarH[x,u],b]]]
TensorListSimplify[a___,Tensor[SpinorBar[x_],{},{OverDot[p_Symbol]}],Tensor[SpinorBar[x_],{},{OverDot[q_Symbol]}],b___]:=Module[{u},u=Unique["\[Alpha]"];TensorListSimplify[TensorList[a,1/2 EpsilonH[OverDot[p],OverDot[q]],SpinorBarL[x,u],SpinorBarH[x,u],b]]]

TensorListSimplify[a___,Tensor[Epsilon,{p_,q_},{}],b___,Tensor[s:(Spinor|SpinorBar)[_],{},{q_}],c___]:=TensorListSimplify[TensorList[a,b,Tensor[s,{p},{}],c]]
TensorListSimplify[a___,Tensor[Epsilon,{},{p_,q_}],b___,Tensor[s:(Spinor|SpinorBar)[_],{q_},{}],c___]:=TensorListSimplify[TensorList[a,b,Tensor[s,{},{p}],c]]
TensorListSimplify[a___,b:Tensor[Spinor[_],{p_},{}],c:Tensor[Spinor[_],{},{p_}],d___]:=TensorListSimplify[TensorList[a,Swap[b,c],d]]
TensorListSimplify[a___,b:Tensor[SpinorBar[_],{},{p_}],c:Tensor[SpinorBar[_],{p_},{}],d___]:=TensorListSimplify[TensorList[a,Swap[b,c],d]]

TensorListSimplify[a___]:=TensorList[a]
TensorListSimplify[a_]:=ReplaceAll[a,TensorList->TensorListSimplify]
*)

Swap[a:Tensor[(Spinor|SpinorBar)[_],__],b:Tensor[(Spinor|SpinorBar)[_],__]]:=TensorList[-b,a]
Swap[a:Tensor[_,__],b:Tensor[_,__]]:=TensorList[b,a]
TensorList[a___,Plus[x_,y__],b___]:=Plus[TensorList[a,x,b],TensorList[a,Plus[y],b]]
TensorList[a___,Times[x_,y__],b___]:=TensorList[a,x,y,b]
TensorList[]:=1




SpinorToH[s:Tensor[Spinor[x_Symbol],{},{a_}]]:=s
SpinorToH[s:Tensor[Spinor[x_Symbol],{a_},{}]]:=Module[{\[Alpha]},\[Alpha]=Unique["\[Alpha]"];TensorList[EpsilonL[a,\[Alpha]],SpinorH[x,\[Alpha]]]]
SpinorToH[s:Tensor[Spinor[OverBar[x_Symbol]],{},{OverDot[a_]}]]:=s
SpinorToH[s:Tensor[Spinor[OverBar[x_Symbol]],{OverDot[a_]},{}]]:=Module[{\[Alpha]},\[Alpha]=Unique["\[Alpha]"];TensorList[EpsilonL[OverDot[a],OverDot[\[Alpha]]],SpinorBarH[x,\[Alpha]]]]



Renumbering[exp_]:=Module[{\[Mu]s,\[Alpha]s,\[Beta]s,list,GetAlphas,GetMus},
  GetAlphas[term_]:=Module[{all},
    all=Cases[term,Tensor[a_,b_,c_]:>{b,c},Infinity]//.OverDot[x_]:>x//Flatten//DeleteDuplicates;
    {Select[all,StringMatchQ[SymbolName[#],"\[Alpha]"~~__]&],Select[all,StringMatchQ[SymbolName[#],"\[Beta]"~~__]&]}];
  GetMus[term_]:=Module[{all},
    all=Join[
      Cases[term,(Sigma|SigmaBar)[a__]:>{a},Infinity],
      Cases[term,Dx[_,b_]:>{b},Infinity]]//Flatten//DeleteDuplicates;
    Select[all,StringMatchQ[SymbolName[#],"\[Mu]"~~__]&]];
  list=List@@Expand[exp];
  \[Alpha]s=GetAlphas/@list;
  \[Mu]s=GetMus/@list;
  {\[Alpha]s,\[Beta]s,\[Mu]s}={Unique["\[Alpha]"]&/@Range[Max[Length/@\[Alpha]s[[All,1]]]],Unique["\[Beta]"]&/@Range[Max[Length/@\[Alpha]s[[All,2]]]],Unique["\[Mu]"]&/@Range[Max[Length/@\[Mu]s]]};
  Module[{tmp,tmp2,rule},
    tmp=GetAlphas[#];
    tmp2=GetMus[#];
    rule={Rule@@#&/@Transpose[{tmp[[1]],\[Alpha]s[[1;;Length[tmp[[1]]]]]}],
          Rule@@#&/@Transpose[{tmp[[2]],\[Beta]s[[1;;Length[tmp[[2]]]]]}],
          Rule@@#&/@Transpose[{tmp2,\[Mu]s[[1;;Length[tmp2]]]}]
    }//Flatten;
    #//.rule]&/@list
]//Total


Dx[z_,\[Mu]_]:=0/;FreeQ[z,x|Pattern|Blank,Infinity]
Tensor[s:Times[x_,y__],p__]:=Tensor[Expand[s],p]/;Not[FreeQ[{x,y},Plus]]
Tensor[Times[a_,b___],p___]:=Times[a,Tensor[Times[b],p]]/;FreeQ[a,Spinor|SpinorBar|Sigma|SigmaBar|Epsilon|Pattern|Blank]
TensorList[a___,x_,b___]:=Times[x,TensorList[a,b]] /; FreeQ[x,Tensor|Pattern|Blanck]
(*
TensorList[a__,x_,b___]:=Times[x,TensorList[a,b]] /; FreeQ[x,Tensor]
TensorList[x_,b__]:=Times[x,TensorList[b]] /; FreeQ[x,Tensor]
TensorList[x_]:=x /; FreeQ[x,Tensor]
*)
SetAttributes[TensorList,Flat]
Protect[SubsuperscriptBoxSub,SpinorL,SpinorH,SpinorBarL,SpinorBarH,SigmaL,SigmaH,SigmaBarL,SigmaBarH,EpsilonH,EpsilonL,Tensor,Spinor,SpinorBar,Sigma,SigmaBar,Epsilon,\[Sigma],\[Epsilon],x,TensorList,TensorListBox,TensorListSimplify,SpinorToH,Dx];



(* ::Input:: *)
(*{SpinorL[x,a],SpinorH[x,a],SpinorBarL[x,a],SpinorBarH[x,a],SigmaL[\[Mu],a,b],SigmaH[\[Mu],a,b],SigmaBarL[\[Mu],a,b],SigmaBarH[\[Mu],a,b],EpsilonH[a,b],EpsilonL[a,b]}*)
(*TensorList[SpinorL[x,a],SpinorH[x,a],SpinorBarL[y,b],SpinorBarH[y,b]]*)
(*TensorList[2SpinorH[x,a],3SigmaH[\[Mu],a,b],5,4SpinorBarH[y,b]]*)


(* ::Input:: *)
(*{*)
(*TensorList[SpinorH[\[Theta],a],SpinorL[\[Phi],a],SpinorH[\[Theta],b],SpinorL[\[Psi],b]],*)
(*TensorList[SpinorBarL[\[Theta],a],SpinorBarH[\[Phi],a],SpinorBarL[\[Theta],b],SpinorBarH[\[Psi],b]]*)
(*}*)
(*TensorListSimplify[%]*)


EndPackage[]
