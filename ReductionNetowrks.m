(*6] A.Veliz-Cuba.Reduction of Boolean Network Models.Journal of \
Theoretical Biology,289:167-172,2011.
paper: https://sites.google.com/site/alanvelizcuba/reduction-of-\
boolean-network-models
code: https://sites.google.com/site/alanvelizcuba/redbn*)

(* PRELIMINARY FUNCTIONS *)
(* Preprocess Boolean expressions *)

STR[F_] := 
  Module[{S}, S = ToString[F]; 
   S = StringReplace[
     S, {"{" -> " { ", "}" -> " } ", "," -> " , ", "!" -> " ! ", 
      "&&" -> " && ", "||" -> " || ", "(" -> " ( ", ")" -> " ) "}];
   Return[" " <> StringReplace[S, " " .. -> "  "] <> " "]];
(* Transform strings into symbolic expressions and simplify *)

SIM[{VV_, FF_}] := 
  Module[{n, SS}, n = Length[FF]; SS = ToExpression[FF]; 
   Return[{VV, Map[ToString, BooleanMinimize[FullSimplify[SS]]]}]];
(* Remove variable v and return string *)

DEL[{VV_, FF_}, v_] := 
 Module[{i, n, S, k}, n = Length[FF]; S = {}; 
  For[i = 1, i <= n, i++, AppendTo[S, STR[FF[[i]]]]];
  k = Position[VV, v]; 
  If[k == {},(*Print["ERROR"];*)Return[{VV, FF}], k = k[[1, 1]]]; 
  If[StringPosition[S[[k]], " " <> v <> " "] != {}, 
   Return[{VV, FF}]];(*Print[S];*)
  
  For[i = 1, i <= n, i++, If[i == k, Continue[]]; 
   S[[i]] = 
    StringReplace[S[[i]], 
     " " <> v <> " " -> "( " <> S[[k]] <> " )"]];
  Return[{Drop[VV, {k}], Drop[S, {k}]}]
  ]

(* FUNCTIONS FOR REDUCTION *)
(* Remove variable v and return \
simplified symbolic expression *)

REMOVEVERTEX[{VV_, FF_}, v_] := SIM[DEL[{VV, FF}, v]]
(* Remove one vertex only: try x1 first (forward) *)

REDUCEonestepF[{VV_, FF_}] := Module[{V, F, n, i},
   n = Length[VV]; {V, F} = {VV, FF};
   For[i = 1, i <= n, i++, {V, F} = SIM[DEL[{V, F}, V[[i]]]]; 
    If[Length[V] < n, Return[{V, F}]]];
   Return[{V, F}]];
(* Remove one variable only: try xn first (backward) *)

REDUCEonestepB[{VV_, FF_}] := Module[{V, F, n, i},
   n = Length[VV]; {V, F} = {VV, FF};
   For[i = n, i >= 1, i = i - 1, {V, F} = SIM[DEL[{V, F}, V[[i]]]]; 
    If[Length[V] < n, Return[{V, F}]]];
   Return[{V, F}]];

(* Remove all removable variables: try x1 first (forward) *)

REDUCEALLF[{VV_, FF_}] := Module[{V, F, n},
   n = Length[VV];
   {V, F} = REDUCEonestepF[{VV, FF}];
   While[n > Length[V], n = Length[V];
    {V, F} = REDUCEonestepF[{V, F}]
    ];
   Return[{V, F}]
   ];

(* Remove all removable variables: try xn first (backward) *)

REDUCEALLB[{VV_, FF_}] := 
  Module[{V, F, n}, 
   n = Length[VV]; {V, F} = REDUCEonestepB[{VV, FF}]; 
   While[n > Length[V], 
    n = Length[V]; {V, F} = REDUCEonestepB[{V, F}]];
   Return[{V, F}]];
(*We have two ways of reducing, "forward" reduction and "backward" \
reduction*)



(*Given a CM in binary format and a dynamic, it translate it into
a boolean network connected by logic gates*)
TRANSLATECm2BN[cm_, dynamic_] :=
    Module[ {completeNet, nodesline, i, row, op, indexes, line, h },
        completeNet = List[];
        nodesline = List[];
        For[i = 1, i <= Length[cm], i++,
         row = Part[cm, i];
         op = Part[dynamic, i];
         indexes = Flatten[ Position[row, 1]];
         AppendTo[nodesline, "x" <> ToString[i]];
         (*Print[row];
         Print[op];
         Print[indexes];*)
         line = "";
         If[ op === "OR",
             Do[If[ h < Length[indexes],
                    line = line <> "x" <> ToString[indexes[[h]]] <> " || ",
                    line = line <> "x" <> ToString[indexes[[h]]]
                ], {h, 1, Length[indexes], 1}],
             If[ op === "AND",
                 Do[If[ h < Length[indexes],
                        line = line <> "x" <> ToString[indexes[[h]]] <> " && ",
                        line = line <> "x" <> ToString[indexes[[h]]]
                    ], {h, 1, Length[indexes], 1}],
                 If[ op === "NOT",
                     Do[If[ h < Length[indexes],
                            line = line <> "x" <> ToString[indexes[[h]]] <> " ! ",
                            line = line <> "x" <> ToString[indexes[[h]]]
                        ], {h, 1, Length[indexes], 1}],
                     If[ op === "XOR",
                         Do[If[ h < Length[indexes],
                                line = line <> "x" <> ToString[indexes[[h]]] <> " \[Xor] ",
                                line = line <> "x" <> ToString[indexes[[h]]]
                            ], {h, 1, Length[indexes], 1}],
                         If[ op === "NAND",
                             Do[If[ h < Length[indexes],
                                    line = line <> "x" <> ToString[indexes[[h]]] <> " \[Nand] ",
                                    line = line <> "x" <> ToString[indexes[[h]]]
                                ], {h, 1, Length[indexes], 1}],
                             Null
                         ]
                     ]
                 ]
             ]
         ];
         AppendTo[completeNet, ToExpression[line]];
         ];
        <|"NewNetwork" -> completeNet, "NewNodeList" ->  nodesline|>
    ];

(* Translate a Boolean netowork format to a AND-NOT Network
This format is necesary for reduction of network*)
TranslateNetwokToAndNotString[BNSource_] := Module[{f},
   Return[
     Table[BooleanMinimize[BNSource[[f]], "AND"], {f, 1, Length[BNSource], 1}]];
   ];
   
createRandomDynamic[length_] := Block[{}, dina = List[];
   For[mm = 1, mm <= length, mm++, ere = RandomInteger[3];
	    If[ere === 0, ele = "AND", 
	     If[ere === 1, ele = "OR", 
	      If[ere === 2, ele = "NOT", 
	      	If[ere === 3, ele = "XOR"], 
	       	  If[ere === 4, ele = "NAND"]
	       	 ]
	       	]
	      ];
	    AppendTo[dina, ele];
    ];
   dina = Flatten[dina];
   <|"Dynamic" -> dina|>];
    
    
    connMatrix2EdgeList[cm_] :=
    Block[ {},
        grafo = List[];
        For[o = 0, o < Length[cm], o++;
                                   noNodo = o;
                                   fila = Part[cm, o];
                                   (*Print["Fila "<> ToString[noNodo]<>": "<> ToString[fila]];*)
                                   inputIndexes = Position[fila, 1];
                                   inputIndexes = Flatten[inputIndexes];
                                   For[u = 0, u < Length[inputIndexes], u++;
                                                                        nodo = ToExpression[ToString[Extract[inputIndexes, u]] <> "->" <> ToString[noNodo]];
                                                                        AppendTo[grafo, nodo];
                                   ];
        ];
        (*Print["Edge LIst: "<> ToString[grafo]];*)
        <|"EdgeList" -> grafo|>
    ];
    
    
   edgelist2CM[edgelist_] :=
       Module[ {gr,vl,newEL,cm,newNames,ii},
           gr = Graph[edgelist];
           vl = Sort[VertexList[gr]];
           newNames = Range[Length[vl]];
           newEL = edgelist /. Thread[vl -> newNames];

           cm = ConstantArray[0, {Length[vl], Length[vl]}];

           For[ii = 1, ii <= Length[newEL], ii++,
            (* begin -----------------*)
            (*Print["Who receives: "<> 
            ToString[newEL[[ii]][[2]]]];
            Print["cm element"<> ToString[cm[[newEL[[ii]][[2]]]]]];*)
            (* 
            end -----------------*)
            
            cm = ReplacePart[cm, {newEL[[ii]][[2]], newEL[[ii]][[1]]} -> 1];
		    (* begin -----------------*)
		    (*Print["CM Updated: "<> 
		    ToString[cm]];
		    Print["------------------"];*)
		    (* 
		    end -----------------*)
    		];
        <|"CM" -> cm|>
   ];
    
    extractSubMatrix[cm_, wholeDynamic_, mainComplex_] :=
        Module[ {allNodes, colsToRemove, submatrix, oneRow, newRow, uu, newDynamic},
            allNodes = Range[Length[cm]];
            colsToRemove = Partition[Flatten[Complement[allNodes, mainComplex]], 1];
            submatrix = List[];
            newDynamic = Delete[wholeDynamic, colsToRemove];
            
            (*Print["number or rows to remove: "<> ToString[numberRows]];
            Print["Columns to remove: "<> ToString[colsToRemove]];
            Print["New Dynamica: "<> ToString[newDynamic]];*)
            For[uu = 1, uu <= Length[mainComplex], uu++,
             oneRow = Part[cm, mainComplex[[uu]]];
             newRow = Delete[oneRow, colsToRemove];
             AppendTo[submatrix, newRow];
             ];
            <|"Submatrix" -> submatrix, "SubDynamic" -> newDynamic|>
        ];
        
        
elementsInColumn[col_] := Module[{res},
   res = 0;
   If[Length[Position[col, 0]] > 0 && Length[Position[col, 1]] > 0,
                     res = "*",
                      
    If[Length[Position[col, 0]] > 0 && 
      Length[Position[col, 1]] === 0,
                    res = 0,
                           
     If[Length[Position[col, 0]] === 0 && Length[Position[col, 1]] > 0,
                          res = 1,
                          Null]
                        ]
                   ];
   <|"RES" -> res|>
   ];


        
findPatternsInInputsPerAttTotal[inputsPerAtt_] :=
    Module[ {kk},
        ptt = Table[
          Table[elementsInColumn[Part[inputsPerAtt, kk][[All, hh]]]["RES"], {hh, 1, Length[Part[inputsPerAtt, kk][[1]]], 1}], 
              {kk,1, Length[inputsPerAtt], 1}];
        <|"Pattern" -> ptt|>
    ];

giveIndexesOfDifferences[list1_, list2_] := Module[{},
   diff = 
    (Table[If[Part[list1, bb] !=  Part[list2, bb], bb, Null], {bb, 1, Length[list1], 1}] /. Null -> Sequence[]) /. {} -> Sequence[];
   <|"Differences" -> diff|>
   ];

(*This function works in RAM, supposing my networks are around 22 \
nodes*)
analysisBasinsAttraction[myInputs_, myOutputs_,currentState_,path_String:""] :=
    Module[{assoInputsOutputs,attAndItsInputs,qq,FlatAtts,inputsPerAtt,assAttAndInputs,allPatterns, ff, gg, 
    	assPattOfInputsAndAtt, ll, assInputPattersToAtts, onlyPattOfAtts, onlyInputsPattToAtts, mm, changesInInputs, 
    	effectInOutputs,atts,whereCSIs,kk },
    	
        assoInputsOutputs = Table[Association[Part[myInputs, qq] -> Part[myOutputs, qq]], {qq,1, Length[myInputs], 1}];
        attAndItsInputs = GroupBy[assoInputsOutputs, Values];
        atts = Keys[attAndItsInputs];
        (*flat attractors*)
        FlatAtts = Map[Flatten[#] &, Keys[attAndItsInputs]];
        (*number of inputs per attractor*)
        inputsPerAtt = Table[Map[Flatten[#] &, Keys[attAndItsInputs[Part[atts, ff]]]], {ff, 1, Length[atts], 1}];
        (*association attractors->Inputs*)
        assAttAndInputs = Table[Association[<|Part[FlatAtts, gg] -> Part[inputsPerAtt, gg]|>], {gg, 1, Length[FlatAtts], 1}];
        SortBy[assAttAndInputs, Identity];
        (* begin ---------------------------*)
        (*Print["Attractors and its inputs"];
        Print[assAttAndInputs];*)
        (* end ------------------------------*)
        (*evaluate all intputs associated to attractors and find patternss*)
        allPatterns = findPatternsInInputsPerAttTotal[inputsPerAtt]["Pattern"];
        (*associations between found patters in inputs and its attractors*)
        assPattOfInputsAndAtt = Table[Association[<|Part[allPatterns, ll] -> Part[FlatAtts, ll]|>], {ll, 1,Length[FlatAtts], 1}];
        (*associations sorted by number of "*" *)
        assInputPattersToAtts = KeySortBy[Merge[assPattOfInputsAndAtt, Identity], Count[#, "*"] &];
        (*Only patterns in inputs*)
        onlyInputsPattToAtts = Keys[assInputPattersToAtts];
        (*only attractors*)
        onlyPattOfAtts = Flatten[#] & /@ Values[assInputPattersToAtts];
        
        (*look for position in the list of attractors the current state*)
        (*whereCSIs = Position[onlyPattOfAtts,currentState][[1]];*)
        
        (* begin -------------------------------------*)
        (*Print["cs is in: "<> ToString[whereCSIs]<> " in:"];
        Print[onlyPattOfAtts];
        Print[onlyInputsPattToAtts];*)
        kk=Keys[assInputPattersToAtts];
        whereCSIs = Position[Keys[assInputPattersToAtts], currentState][[1]];
        Print["cs is in: "<> ToString[whereCSIs]<> " in:"];
        Print[assInputPattersToAtts//TableForm];
        (* end ---------------------------------------*)
        
        (*and locate it in the beggining of list*)
        (*If[whereCSIs !={1},
        	onlyPattOfAtts=Permute[onlyPattOfAtts,Cycles[{{1,whereCSIs[[1]]}}]];
        	onlyInputsPattToAtts=Permute[onlyInputsPattToAtts,Cycles[{{1,whereCSIs[[1]]}}]]
        	,Null];*)
        	
        If[whereCSIs !={1},
        	assInputPattersToAtts=Permute[assInputPattersToAtts,Cycles[{{1,whereCSIs[[1]]}}]];
        	Print["CS moved to first place"];
        	Print[assInputPattersToAtts//TableForm];
        	,Null];
        
        (* begin -------------------------*)	
        (*Print["New arragement:"];
        Print[onlyPattOfAtts];
        Print[onlyInputsPattToAtts];*)
        (* end -----------------------------*)
        
        changesInInputs = Table[giveIndexesOfDifferences[Part[onlyInputsPattToAtts, 1],Part[onlyInputsPattToAtts, mm]]["Differences"],
            {mm, 2,Length[onlyInputsPattToAtts], 1}];
        
        effectInOutputs = Table[giveIndexesOfDifferences[Part[onlyPattOfAtts, 1], Part[onlyPattOfAtts, mm]]["Differences"], 
            {mm, 2,Length[onlyPattOfAtts], 1}];
            
        (*If a path is definted, results are saved*)
        If[path!="",Export[path<>"InputsPerAttractor.csv",inputsPerAtt,"CSV"];
        	Export[path<>"Attractors.csv",onlyPattOfAtts,"CSV"];
        	Export[path<>"InputPatters2Attractors.csv",allPatterns,"CSV"];
        	,Null];
        
        <|
        "ChangeInNodes" -> changesInInputs, 
         "EffectInNodes" -> effectInOutputs,
         "ImputsPerAttractor"-> inputsPerAtt,
         "Attractors"-> onlyPattOfAtts,
         "AssociationInputs2Attractors"-> assAttAndInputs,
         "PatternsOfInputs"-> allPatterns
         |>
    ];



myOr[list_] :=
    (hayUnos = Position[list, 1];
     If[ Length[hayUnos] > 0,
         Return[1],
         Return[0]
     ];);

myNand[list_] :=
    (hayCeros = Position[list, 0];
     If[ Length[hayCeros] > 0,
         Return[1],
         Return[0]
     ];);

myAnd[list_] :=
    (ayCeros = Position[list, 0];
     If[ Length[ayCeros] === 0,
         Return[1],
         Return[0]
     ];);

myXor[list_] :=
    (posi0 = Position[list, 0];
     posi1 = Position[list, 1];
     If[ Length[posi0] === 0 || Length[posi1] === 0,
         Return[0],
         Return[1]
     ];);
     
     
     
     
executeBooleanRule[inputList_, rule_]:=(
	If[rule === "AND", Return[myAnd[inputList]], 
		If[rule === "OR", Return[myOr[inputList]],
			If[rule === "XOR", Return[myXor[inputList]],
				If[rule === "NAND", Return[myNand[inputList]],Null]
			]
		]
	];
);     

     
     
     
     
allPosibleInputsReverse[noNodes_] :=
    (Table[Reverse[IntegerDigits[x, 2, noNodes]], {x, 0, (2^noNodes) - 1, 1}]);
    
    getRow[matrix_, noRow_] :=
    (Return[matrix[[noRow]]]);

	getCol[matrix_, noCol_] :=
    (Return[matrix[[All, noCol]]]);
    
    getIndexesOfNodesInputs[node_, matrix_] :=
    (Return[Position[getRow[matrix, node], 1]]);
    
    getListInputsByIndex[input_, indexes_] :=
    (Return[Extract[input, indexes]]);

(*Run one step in a network over all repertoire of possible inputs using a specific dynamic*)
runDynamic[cm_, dynamic_, direction_] :=
    Block[ {noNodes, inputs,unitaryInputUnrestrictedProbability,associationsInputOutputs,noInputs,repertoireResultsNet,
    	ucInputVectorProbability,k,oneNetOutput,input,n,indexesInputs,inputsToThisNode,nodeOp,resOp,attAssociations,attractors,
    	attracDec,attracProbprobAttractors, b,r,attracProb,probAttractors,completeAttractorsProb},
        noNodes = Length[dynamic];
        
        If[direction=== "inverse",inputs = allPosibleInputsReverse[noNodes],inputs=allPosibleInputsNormal[noNodes]];

        unitaryInputUnrestrictedProbability = Divide[1, Length[inputs]];
        associationsInputOutputs = List[];
        (*Print["INPUTS "];
        Print[inputs];*)
        noInputs = Length[inputs];
        repertoireResultsNet = List[];
        ucInputVectorProbability = List[];
        For[k = 0, k < noInputs, k++;
                                 oneNetOutput = List[];
                                 input = Part[inputs, k];
                                 (*Print[input];*)
                                 For[n = 0, n < noNodes, n++;
                                                         indexesInputs = getIndexesOfNodesInputs[n, cm];
                                                         inputsToThisNode = getListInputsByIndex[input, indexesInputs];
                                                         nodeOp = Part[dynamic, n];
                                                         (*Print[indexesInputs];
                                                         Print[inputsToThisNode];
                                                         Print[nodeOp];*)
                                                         If[ nodeOp === "AND",
                                                             resOp = myAnd[inputsToThisNode],
                                                             Null
                                                         ];
                                                         If[ nodeOp === "OR",
                                                             resOp = myOr[inputsToThisNode],
                                                             Null
                                                         ];
                                                         If[ nodeOp === "XOR",
                                                             resOp = myXor[inputsToThisNode],
                                                             Null
                                                         ];
                                                         If[ nodeOp === "NAND",
                                                             resOp = myNand[inputsToThisNode],
                                                             Null
                                                         ];
                                                         (*Print[resOp];*)
                                                         AppendTo[oneNetOutput, resOp];
                                 ];
                                 AppendTo[repertoireResultsNet, oneNetOutput];
                                 AppendTo[associationsInputOutputs,Association[{input-> Flatten[oneNetOutput]}]];
                                 AppendTo[ucInputVectorProbability, N[unitaryInputUnrestrictedProbability]];
        ];
        attAssociations = Merge[associationsInputOutputs,Identity];
        attractors = DeleteDuplicates[repertoireResultsNet];
        attracDec = Table[FromDigits[Part[attractors, b], 2], {b, 1, Length[attractors], 1}];
        attracProb = 1/Length[attractors];
        probAttractors = Table[attracProb*Count[repertoireResultsNet, Part[attractors, r]], {r, 1, Length[attractors], 1}];
        completeAttractorsProb = Table[N[attracProb*Count[repertoireResultsNet,Part[repertoireResultsNet, r]]], {r, 1,Length[repertoireResultsNet], 1}];
        <|"RepertoireInputs" -> inputs,
        "RepertoireOutputs" -> repertoireResultsNet,
        "UnitaryInputUnrestrictedProbability" -> unitaryInputUnrestrictedProbability,
        "Attractors" -> attractors,
        "AttractorsDec" -> attracDec,
        "AttAssociations"-> attAssociations,
        "OnlyAttractorsProbabilities" -> probAttractors,
        "CompleteAttractorProbVector" -> completeAttractorsProb,
        "UCInputVectorProbability" -> ucInputVectorProbability
        |>
    ];



runDynamicHD[cm_, dynamic_,path_, direction_] :=
    Block[ {noNodes, inputs,unitaryInputUnrestrictedProbability,associationsInputOutputs,noInputs,repertoireResultsNet,
    	ucInputVectorProbability,k,oneNetOutput,input,n,indexesInputs,inputsToThisNode,nodeOp,resOp,attAssociations,attractors,
    	attracDec,attracProbprobAttractors, b,r,attracProb,probAttractors,completeAttractorsProb},
        noNodes = Length[dynamic];
        If[direction=== "inverse",inputs = allPosibleInputsReverse[noNodes],inputs=allPosibleInputsNormal[noNodes]];

        unitaryInputUnrestrictedProbability = Divide[1, Length[inputs]];
        associationsInputOutputs = List[];
        (*Print["INPUTS "];
        Print[inputs];*)
        noInputs = Length[inputs];
        repertoireResultsNet = List[];
        ucInputVectorProbability = List[];
        For[k = 0, k < noInputs, k++;
                                 oneNetOutput = List[];
                                 input = Part[inputs, k];
                                 (*Print[input];*)
                                 For[n = 0, n < noNodes, n++;
                                                         indexesInputs = getIndexesOfNodesInputs[n, cm];
                                                         inputsToThisNode = getListInputsByIndex[input, indexesInputs];
                                                         nodeOp = Part[dynamic, n];
                                                         (*Print[indexesInputs];
                                                         Print[inputsToThisNode];
                                                         Print[nodeOp];*)
                                                         If[ nodeOp === "AND",
                                                             resOp = myAnd[inputsToThisNode],
                                                             Null
                                                         ];
                                                         If[ nodeOp === "OR",
                                                             resOp = myOr[inputsToThisNode],
                                                             Null
                                                         ];
                                                         If[ nodeOp === "XOR",
                                                             resOp = myXor[inputsToThisNode],
                                                             Null
                                                         ];
                                                         If[ nodeOp === "NAND",
                                                             resOp = myNand[inputsToThisNode],
                                                             Null
                                                         ];
                                                         (*Print[resOp];*)
                                                         AppendTo[oneNetOutput, resOp];
                                 ];
                                 AppendTo[repertoireResultsNet, oneNetOutput];
                                 AppendTo[associationsInputOutputs,Association[{input-> Flatten[oneNetOutput]}]];
                                 AppendTo[ucInputVectorProbability, N[unitaryInputUnrestrictedProbability]];
        ];
        
        attAssociations = Merge[associationsInputOutputs,Identity];
        attractors = DeleteDuplicates[repertoireResultsNet];
        attracDec = Table[FromDigits[Part[attractors, b], 2], {b, 1, Length[attractors], 1}];
        attracProb = 1/Length[attractors];
        probAttractors = Table[attracProb*Count[repertoireResultsNet, Part[attractors, r]], {r, 1, Length[attractors], 1}];
        completeAttractorsProb = Table[N[attracProb*Count[repertoireResultsNet,Part[repertoireResultsNet, r]]], {r, 1,Length[repertoireResultsNet], 1}];
        
        
        Export[path<>"outputs.csv",repertoireResultsNet];
        Export[path<>"inputs.csv",inputs];
        Export[path<>"atts.csv",attractors];
        
        <|"RepertoireInputs" -> inputs,
        "RepertoireOutputs" -> repertoireResultsNet,
        "UnitaryInputUnrestrictedProbability" -> unitaryInputUnrestrictedProbability,
        "Attractors" -> attractors,
        "AttractorsDec" -> attracDec,
        "AttAssociations"-> attAssociations,
        "OnlyAttractorsProbabilities" -> probAttractors,
        "CompleteAttractorProbVector" -> completeAttractorsProb,
        "UCInputVectorProbability" -> ucInputVectorProbability
        |>
    ];


   
(*inputs to this module must be in terms of edgeLists*)
findBridges[edgeListFullGraph_, edgeListSubG1_, edgeListSubG2_] := 
  Module[{orG1,orG2,allOutputsFromSubNet,ss,outBridges,outG12G2,allInputsFromSubNet,inBridges,
  	inG22G1,bridges},
   
   orG1 = Sort[DeleteDuplicates[#[[1]] & /@ edgeListSubG1]];
   orG2 = Sort[DeleteDuplicates[#[[1]] & /@ edgeListSubG2]];
   
   (* begin -------------------------------------*)
   (*Print["Inputs"];
   Print["G1: "<>ToString[edgeListSubG1]];
   Print["G2: "<>ToString[edgeListSubG2]];
   
   Print["First step: "];
   Print[orG1];
   Print[orG2];*)
   (* end ---------------------------------------*)
   
   (*elements towards outside of G1*)
   
   allOutputsFromSubNet = Table[If[Length[Position[orG1, First[edgeListFullGraph[[ss]]]]] > 0,edgeListFullGraph[[ss]], Null],
   	{ss, 1, Length[edgeListFullGraph], 1}] /. Null -> Sequence[];
   
   (*elements that do not belong to G1 but goes outside G1*)
   
   outBridges = Complement[allOutputsFromSubNet, edgeListSubG1];
   
   (*elements goes outside towards G2*)
   
   outG12G2 = 
    Table[If[
       Length[Position[orG2, allOutputsFromSubNet[[ss]][[2]]]] > 0, 
       allOutputsFromSubNet[[ss]], Null], {ss, 1, 
       Length[allOutputsFromSubNet], 1}] /. Null -> Sequence[];
   
   
   allInputsFromSubNet = 
    Table[If[Length[Position[orG1, edgeListFullGraph[[ss]][[2]]]] > 0,
        edgeListFullGraph[[ss]], Null], {ss, 1, 
       Length[edgeListFullGraph], 1}] /. Null -> Sequence[];
   
   inBridges = Complement[allInputsFromSubNet, edgeListSubG1];
   
   inG22G1 = 
    Complement[
     Table[If[
        Length[Position[orG2, First[allInputsFromSubNet[[ss]]]]] > 0, 
        allInputsFromSubNet[[ss]], Null], {ss, 1, 
        Length[allInputsFromSubNet], 1}] /. Null -> Sequence[], 
     edgeListSubG1];
   
   bridges = Union[outG12G2, inG22G1];
   
   (* begin --------------------*)
   (*Print["G1"];
   Print[edgeListSubG1];
   Print["Origins G1"];
   Print [orG1];
   Print["All which first element is in origin:"];
   Print[allOutputsFromSubNet];
   Print["Bridges"];
   Print[outBridges];
   
   Print["Origins G2"];
   Print[orG2];
   Print["Briges 2 G2"];
   Print[outG12G2];
   
   Print["Briges 2 G1"];
   Print[inG22G1];*)
   (* end ------------------------*)
   
   <|
    "AllOutputs" -> allOutputsFromSubNet,
    "OutBridges" -> outBridges,
    "AllInputs" -> allInputsFromSubNet,
    "InBridges" -> inBridges,
    "Bridges2G2" -> outG12G2,
    "Bridges2G1" -> inG22G1,
    "Bridges" -> bridges
    |>
   ];

(*fullGraph = Graph*)
calculateSchemata4SetSubnetworks[fullGraph_, fullDynamic_,currentState_, setVertexListOfSubnetworks_] :=
    Module[ {xx,schemataChanges,schemataEffect,oneSubnetwork,oneSubgraph,cmOneSubnetwork,dynSubnetwork,
    	running,analysis,rules,source,effect,csSubnetwork},
    	
        schemataChanges = List[];
        schemataEffect = List[];
        For[xx = 1, xx <= Length[setVertexListOfSubnetworks], xx++,
          oneSubnetwork = Part[setVertexListOfSubnetworks, xx];
          oneSubgraph = Subgraph[fullGraph, oneSubnetwork];
          cmOneSubnetwork = Transpose[Normal[AdjacencyMatrix[oneSubgraph]]];
          dynSubnetwork = Part[fullDynamic, oneSubnetwork];
          csSubnetwork = Part[currentState, oneSubnetwork];
          (*being --------------------*)
          (*Print["----------------------------------"];
          Print["Nodes subnetwrok: "<> ToString[oneSubnetwork]];
          Print["CM: "<> ToString[cmOneSubnetwork]];
          Print["Dynamic: "<> ToString[dynSubnetwork]];*)
          (*end --------------------*)
          running = runDynamic[cmOneSubnetwork, dynSubnetwork];
          analysis = analysisBasinsAttraction[running["RepertoireInputs"], running["RepertoireOutputs"],csSubnetwork];
          rules = Thread[Range[1, Length[oneSubnetwork]] -> oneSubnetwork];
          
          source = analysis["ChangeInNodes"] /. rules;
          effect = analysis["EffectInNodes"] /. rules;
          AppendTo[schemataChanges, source];
          AppendTo[schemataEffect, effect];
          
          (* begin ------------------------*)
          (*Print[source];
          Print[effect];*)
          (* end -------------------------*)
        ];
        
        <|
        "Origins"-> schemataChanges,
        "Effects"-> schemataEffect
        
        |>
    ];

    
combineSchemataSets[setScheA_,  SetSchB_] := Return[Table[Union[#, setScheA[[cc]]] & /@ SetSchB, {cc, 1, Length[setScheA],1}]];


selectSetByRule[setSourceSchemataA_, setSourceSchemataB_, rule_] := 
  Module[
   {origin, originsA, originsB, bb, nn, originAIndexes, 
    oringinBIndexes,end},
   
   origin = rule[[1]];
   end = rule[[2]];
   
   originAIndexes = List[];
   oringinBIndexes = List[];
   
   originsA = 
    Table[If[
       Length[Position[Part[setSourceSchemataA, bb], origin]] > 0, 
       AppendTo[originAIndexes, bb]; Part[setSourceSchemataA, bb], 
       Null], {bb, 1, Length[setSourceSchemataA], 1}] /. 
     Null -> Sequence[];
   
   originsB = 
    Table[If[Length[Position[Part[setSourceSchemataB, nn], end]] > 0, 
       AppendTo[oringinBIndexes, nn]; Part[setSourceSchemataB, nn], 
       Null], {nn, 1, Length[setSourceSchemataB], 1}] /. 
     Null -> Sequence[];
     
     (*If rule does not get results, maybe it is an inverse rule*)
     If[(Length[originsA]===0 && Length[originsB]===0),origin=rule[[2]]; end =rule[[1]];
     	originsA = 
    Table[If[
       Length[Position[Part[setSourceSchemataA, bb], origin]] > 0, 
       AppendTo[originAIndexes, bb]; Part[setSourceSchemataA, bb], 
       Null], {bb, 1, Length[setSourceSchemataA], 1}] /. 
     Null -> Sequence[];
     
     originsB = 
    Table[If[Length[Position[Part[setSourceSchemataB, nn], end]] > 0, 
       AppendTo[oringinBIndexes, nn]; Part[setSourceSchemataB, nn], 
       Null], {nn, 1, Length[setSourceSchemataB], 1}] /. 
     Null -> Sequence[];
     
     
     ,Null];
     
   
   <|
    "OriginsA" -> originsA,
     "OriginsB" -> originsB,
    "OriginIndexesA" -> originAIndexes,
    "OriginIndexesB" -> oringinBIndexes
    |>
   
   ];
   
   
   
joinSchematByRule[setOriginSchA_, setEffectSchA_, setOriginSchemB_, setEffectSchB_, rule_] :=
    Module[ {selected,selectedOriginsA,selectedOriginsB,orAInd,orBInd,effectsA,effectsB,
    	newOriginsAB,newEffectsAB},
        selected = selectSetByRule[setOriginSchA, setOriginSchemB, rule];
        selectedOriginsA = selected["OriginsA"];
        selectedOriginsB = selected["OriginsB"];
        orAInd = selected["OriginIndexesA"];
        orBInd = selected["OriginIndexesB"];
        effectsA = Part[setEffectSchA, orAInd];
        effectsB = Part[setEffectSchB, orBInd];
        newOriginsAB = combineSchemataSets[selectedOriginsA, selectedOriginsB];
        newEffectsAB = combineSchemataSets[effectsA, effectsB];
        (* begin -----------------------------*)
        Print[" **************   COMBINATION STARTS HERE *******************"];
        Print[" ************************************************************"];
        Print["********************   COMPLETES ****************************"];
        Print["*************************************************************"];
        Print["Origins A:"];
        Print[setOriginSchA];
        Print["Origins B:"];
        Print[setOriginSchemB];
        Print["Effects A:"];
        Print[setEffectSchA];
        Print["Effects B:"];
        Print[setEffectSchB];
        Print[" ************************************************************"];
        Print["*************************************************************"];
        Print["------------  Combination rule: "<> ToString[rule]];
        
        Print["Origins selected A: "<> ToString[selectedOriginsA]];
        (*Print["From: "<>ToString[setOriginSchA]];*)
        Print["Origins selected B: "<> ToString[selectedOriginsB]];
        (*Print["From: "<>ToString[setOriginSchemB]];*)
        
        Print["Effects selected A: "<> ToString[effectsA]];
        (*Print["From: "<>ToString[setEffectSchA]];*)
        Print["Effects selected B: "<> ToString[effectsB]];
        (*Print["From: "<>ToString[setEffectSchB]];*)
        
        Print["Origins combined: "<> ToString[newOriginsAB]];
        Print["Effects combined: "<> ToString[newEffectsAB]];
        Print["***************   COMBINATIONS ENDS HERE *********************"];
        
        (* end ---------------------------------*)
        <|
         "JoinedOrigins" -> newOriginsAB,
         "JoinedEffects" -> newEffectsAB
         |>
    ];
   
joinSchematBySetRules[setOriginSchA_, setEffectSchA_, setOriginSchemB_, setEffectSchB_, setRules_] :=
    Module[{joinedOrigins,joinedEffects,nn,jsr,jo,je},
        joinedOrigins = List[];
        joinedEffects = List[];
        For[nn = 1, nn <= Length[setRules], nn++,
         jsr = joinSchematByRule[setOriginSchA, setEffectSchA, setOriginSchemB, setEffectSchB, Part[setRules, nn]];
         AppendTo[joinedOrigins, jsr["JoinedOrigins"]];
         AppendTo[joinedEffects, jsr["JoinedEffects"]];         
         ];
         (*jo=DeleteDuplicates[Level[joinedOrigins, {-2}]];
         je=DeleteDuplicates[Level[joinedEffects, {-2}]];
         Print[joinedOrigins];
         Print[joinedEffects];*)
         jo=Level[joinedOrigins, {-2}];
         je=Level[joinedEffects, {-2}];
         (*
         Print["JUST JOINED: "];
         Print[jo];
         Print[je];
         *)
        <|"NewOrigins" -> jo,"NewEffects" ->je 
         |>
    ];
   
   
detectDeleteInverseRules[setRules_] := Module[{},
   g = Graph[setRules];
   indexes2Remove = List[];
   For[ii = 1, ii <= Length[EdgeList[g]], ii++,
    oneRule = Part[EdgeList[g], ii];
    inverse = DirectedEdge[oneRule[[2]], oneRule[[1]]];
    (*Print[inverse];
    Print[Position[EdgeList[g],inverse]];*)
    
    If[Length[Position[EdgeList[g], inverse]] > 0, 
     g = Graph[EdgeList[EdgeDelete[g, inverse]]]];
    ];
   <|"CleanSetRules" -> EdgeList[g]|>
   ];
   
   
   
   calculateOneOutptuOfNetwork[input_,cm_,dynamic_] :=
    Block[ {noNodes,oneNetOutput,n,indexesInputs,inputsToThisNode,nodeOp,resOp},
    	noNodes=Length[input];
        oneNetOutput = List[];

        For[n = 0, n < noNodes, n++;
                                indexesInputs = getIndexesOfNodesInputs[n, cm];
                                inputsToThisNode = getListInputsByIndex[input, indexesInputs];
                                nodeOp = Part[dynamic, n];

                                If[ nodeOp === "AND",
                                    resOp = myAnd[inputsToThisNode],
                                    Null
                                ];
                                If[ nodeOp === "OR",
                                    resOp = myOr[inputsToThisNode],
                                    Null
                                ];
                                If[ nodeOp === "XOR",
                                    resOp = myXor[inputsToThisNode],
                                    Null
                                ];
                                If[ nodeOp === "NAND",
                                    resOp = myNand[inputsToThisNode],
                                    Null
                                ];

                                AppendTo[oneNetOutput, resOp];
        ];
        
     <|"Output"-> oneNetOutput |>
    ];
    
    
saveDataSubnetwork[dir_,nodeName_,originSche_,effectSche_,pattInputs_,attractors_]:=
   Module[{},
   	Export[dir<>"originSche"<>nodeName, originSche];
   	Export[dir<>"effectSche"<>nodeName, effectSche];
   	Export[dir<>"pattInputs"<>nodeName, pattInputs];
   	Export[dir<>"attractors"<>nodeName, attractors];
   ];
   
recoverOriginSch[dir_,nodeName_]:=Return[Import[dir<>originSch<>nodeName]];
recoverEffectSch[dir_,nodeName_]:=Return[Import[dir<>effectSch<>nodeName]];
recoverPattInputs[dir_,nodeName_]:=Return[Import[dir<>pattInputs<>nodeName]];
recoverAttractors[dir_,nodeName_]:=Return[Import[dir<>attractors<>nodeName]];

allPosibleInputsReverse[noNodes_] :=
    (Table[Reverse[IntegerDigits[x, 2, noNodes]], {x, 0, (2^noNodes) - 1, 1}]);

allPosibleInputsNormal[noNodes_] :=
    (Table[IntegerDigits[x, 2, noNodes], {x, 0, (2^noNodes) - 1, 1}]);

(*buildCompleteProbDistrib[{{0,0},{1,1}},{1,2},inputs, {1,3}, 0.25]
keys and values = <|{0,0}\[Rule]1,{1,1}\[Rule] 2|>  this is number of \
times a patter appears
inputs = complete list to analyze. Its length = complete \
probabilities distribution length.
0.25 = unitary probability
*)
buildCompleteProbDistrib[keys_, values_, objectList_, part_, unitaryProb_] :=
    Block[ {distProb,hh,objectElement,subPart,assignedProb,pa},
   (*Print["----INTO buildCompleteProbDistrib PROCEDURE -----"];*)
        distProb = List[];
        For[hh = 0, hh < Length[objectList], hh++;
                                             objectElement = Part[objectList, hh];
                                             subPart = Part[objectElement, part];
                                             assignedProb = 0;
                                             (*begin -----------------------------------------*)
                                             (*Print[
                                             "ObjectList:"];
                                             Print[objectList//MatrixForm];
                                             Print["Part"<>ToString[part]];
                                             Print["Calculating probability element: " <> ToString[hh]<> "**" ];
                                             Print["Object element: "<> ToString[objectElement]];
                                             Print["Subpart: "<> ToString[subPart]];*)
                                             (*end -----------------------------------------*)
                                             For[pa = 1, pa <= Length[keys], pa++,
                                                                             (*begin -----------------------------------------*)
                                                                             (*Print["Testing key: " <> ToString[keys[[pa]]]];*)
                                                                             (*end -----------------------------------------*)
                                                                             If[ subPart === keys[[pa]],
                                                                                 (*Print["Encontrado!!"];*)
                                                                                 assignedProb = values[[pa]]* unitaryProb,
                                                                                 Null
                                                                             ];
                                             ];
                                             AppendTo[distProb, assignedProb];
         ];
        <|"ProbabilityDistribution" -> distProb |>
    ];


getElementContainPattern[tarjectList_, nodes_, subState_] :=
    Module[ {indexesFound, elemFound, decimalRep, f, analizedElem },
        indexesFound = List[];
        elemFound = List[];
        decimalRep = List[];
        (*Print["------------------------------"];
        Print["------------------------------"];
        Print["Nodes: " <> ToString[nodes]];
        Print["Substate in nodes: " <> ToString[subState]];
        Print["Starting  search..."];*)
        For[f = 0, f < Length[tarjectList], f++;
                                            analizedElem = Part[tarjectList, f];
                                            (*Print["Element: " <> ToString[analizedElem]];
                                            Print["Substate: " <> ToString[Part[analizedElem,nodes]]];*)
                                            If[ Part[Part[tarjectList, f], nodes] === subState,
                                                AppendTo[elemFound, Part[tarjectList, f]];
                                                AppendTo[indexesFound, f];
                                                AppendTo[decimalRep, FromDigits[Part[tarjectList, f], 2]],
                                                Null
                                            ];
         ];
        <|"Elements" -> elemFound, "Indexes" -> indexesFound, 
         "DecimalRep" -> decimalRep|>
    ];

probabilityDistributionCalculation[mechanism_, purview_, outputs_, inputs_, currentState_, causalOrEffect_] :=
    Module[ {currentSubstate, elementsWithCurrentSubstate, indexesOutElementsCurrentSubstate, 
    	     possiblePastFutureStates, purviewsOfPossiblePastFutureStates, singleProbability, 
    	     pps,ppp, diffPattPurviews, keys, values, completeProbDistr },
    	 
        currentSubstate = Part[currentState, mechanism];
        If[ causalOrEffect === "causal",
            elementsWithCurrentSubstate = getElementContainPattern[outputs, mechanism, currentSubstate],
            elementsWithCurrentSubstate = getElementContainPattern[inputs, mechanism, currentSubstate]
        ];
        indexesOutElementsCurrentSubstate = elementsWithCurrentSubstate["Indexes"];
        (*begin ----------------------------------------------------*)
        (*nPrint["**Sence: "<>ToString[causalOrEffect]];
        Print["OUTPUTS: "<> ToString[outputs]];
        Print["INPUTS" <> ToString[inputs]];
        Print["Mechanism: "<>ToString[mechanism]<> " Substate:" <> ToString[currentSubstate]];
        Print[ "Purview: "<> ToString[purview]];
        Print["Indixes of elements fulfil requirement:" <> ToString[indexesOutElementsCurrentSubstate]];*)
        (*end ----------------------------------------------------*)
        If[ causalOrEffect === "causal",
            possiblePastFutureStates = Table[Part[inputs, indexesOutElementsCurrentSubstate[[pps]]], {pps, 1,Length[indexesOutElementsCurrentSubstate], 1}],
            possiblePastFutureStates = Table[Part[outputs,indexesOutElementsCurrentSubstate[[pps]]], {pps, 1,Length[indexesOutElementsCurrentSubstate], 1}]
        ];
        purviewsOfPossiblePastFutureStates = Table[Part[possiblePastFutureStates[[ppp]],Flatten[purview]], {ppp, 1, Length[possiblePastFutureStates],1}];
        singleProbability = N[1/Length[purviewsOfPossiblePastFutureStates]];
        diffPattPurviews = Counts[purviewsOfPossiblePastFutureStates];
        
        (*begin ----------------------------------------------------*)
        (*Print["Posible Past/Future states:" <> ToString[possiblePastFutureStates]];
        Print["Purviews of possible past/FutureStates:"<>ToString[purviewsOfPossiblePastFutureStates]];
        Print["Patt found in  purviews: "<> ToString[diffPattPurviews]];*)
        (*end ----------------------------------------------------*)
        keys = Keys[diffPattPurviews];
        values = Values[diffPattPurviews];
        If[ causalOrEffect === "causal",
            completeProbDistr = buildCompleteProbDistrib[keys, values, inputs, purview, singleProbability],
            completeProbDistr = buildCompleteProbDistrib[keys, values, outputs, purview,singleProbability]
        ];
        
        (*begin ----------------------------------------------------*)
        (*Print["Probability Distri:" <>ToString[completeProbDistr]];*)
        (*end ----------------------------------------------------*)
        <|
        "OutputsWithCurrentSubstate" -> elementsWithCurrentSubstate["Elements"], 
         "IndexesOutElementsCurrentSubstate" -> indexesOutElementsCurrentSubstate, 
         "PossiblePastFutureStates" ->  possiblePastFutureStates, 
         "PurviewsOfPossiblePastFutureStates" -> purviewsOfPossiblePastFutureStates, 
         "SingleProbability" -> singleProbability, 
         "AllPatternsPurviews" -> diffPattPurviews,  
         "CompleteProbabilityDistribution" -> completeProbDistr["ProbabilityDistribution"]
         |>
    ];
    

fixHighOrderVertexToLowLevelInputs[vertexCompleteSN_,vertexSN_,sizeInputs_]:=Module[
	{newNames,vcSN,newVertex},
	newNames = Range[1,sizeInputs];
	vcSN = Sort[vertexCompleteSN];
	newVertex=Flatten[vertexSN /.{Thread[vcSN -> newNames]}];
	Print["NewVertex:" <> ToString[newVertex]];
	Return[newVertex];

];
    
probabDistribCalcSubnetwork[vertexCompleteSN_,mechanismSN_, purviewSN_, outputsSN_, inputsSN_, currentStateSN_, causalOrEffect_] :=
    Module[ {currentSubstate, elementsWithCurrentSubstate, indexesOutElementsCurrentSubstate, 
    	     possiblePastFutureStates, purviewsOfPossiblePastFutureStates, singleProbability, 
    	     pps,ppp, diffPattPurviews, keys, values, completeProbDistr, newMecha, newPV },
    	 
    	 newMecha = List[];
    	 newPV = List[];
    	 (* begin --------------------------------------*)
    	 (*Print["MAX MECHA: "<>ToString[Max[mechanismSN]]];
    	 Print["MAX PV: "<>ToString[Max[purviewSN]]];*)
    	 (* end ----------------------------------------*)
    	 
    	If[Max[mechanismSN]> Length[mechanismSN]||Max[purviewSN]>Length[purviewSN],
    		newMecha=fixHighOrderVertexToLowLevelInputs[vertexCompleteSN,mechanismSN,Length[vertexCompleteSN]];
    		newPV=fixHighOrderVertexToLowLevelInputs[vertexCompleteSN,purviewSN,Length[vertexCompleteSN]],
    	newMecha = mechanismSN; newPV=purviewSN
    	];
    	
        currentSubstate = Part[currentStateSN, newMecha];
        If[ causalOrEffect === "causal",
            elementsWithCurrentSubstate = getElementContainPattern[outputsSN, newMecha, currentSubstate],
            elementsWithCurrentSubstate = getElementContainPattern[inputsSN, newMecha, currentSubstate]
        ];
        indexesOutElementsCurrentSubstate = elementsWithCurrentSubstate["Indexes"];
        (*begin ----------------------------------------------------*)
        (*nPrint["**Sence: "<>ToString[causalOrEffect]];
        Print["OUTPUTS: "<> ToString[outputs]];
        Print["INPUTS" <> ToString[inputs]];
        Print["Mechanism: "<>ToString[mechanism]<> " Substate:" <> ToString[currentSubstate]];
        Print[ "Purview: "<> ToString[purview]];
        Print["Indixes of elements fulfil requirement:" <> ToString[indexesOutElementsCurrentSubstate]];*)
        (*end ----------------------------------------------------*)
        If[ causalOrEffect === "causal",
            possiblePastFutureStates = Table[Part[inputsSN, indexesOutElementsCurrentSubstate[[pps]]], {pps, 1,Length[indexesOutElementsCurrentSubstate], 1}],
            possiblePastFutureStates = Table[Part[outputsSN,indexesOutElementsCurrentSubstate[[pps]]], {pps, 1,Length[indexesOutElementsCurrentSubstate], 1}]
        ];
        purviewsOfPossiblePastFutureStates = Table[Part[possiblePastFutureStates[[ppp]],Flatten[newPV]], {ppp, 1, Length[possiblePastFutureStates],1}];
        singleProbability = N[1/Length[purviewsOfPossiblePastFutureStates]];
        diffPattPurviews = Counts[purviewsOfPossiblePastFutureStates];
        
        (*begin ----------------------------------------------------*)
        (*Print["Posible Past/Future states:" <> ToString[possiblePastFutureStates]];
        Print["Purviews of possible past/FutureStates:"<>ToString[purviewsOfPossiblePastFutureStates]];
        Print["Patt found in  purviews: "<> ToString[diffPattPurviews]];*)
        (*end ----------------------------------------------------*)
        keys = Keys[diffPattPurviews];
        values = Values[diffPattPurviews];
        If[ causalOrEffect === "causal",
            completeProbDistr = buildCompleteProbDistrib[keys, values, inputsSN, newPV, singleProbability],
            completeProbDistr = buildCompleteProbDistrib[keys, values, outputsSN, newPV,singleProbability]
        ];
        
        (*begin ----------------------------------------------------*)
        (*Print["Probability Distri:" <>ToString[completeProbDistr]];*)
        (*end ----------------------------------------------------*)
        <|
        "OutputsWithCurrentSubstate" -> elementsWithCurrentSubstate["Elements"], 
         "IndexesOutElementsCurrentSubstate" -> indexesOutElementsCurrentSubstate, 
         "PossiblePastFutureStates" ->  possiblePastFutureStates, 
         "PurviewsOfPossiblePastFutureStates" -> purviewsOfPossiblePastFutureStates, 
         "SingleProbability" -> singleProbability, 
         "AllPatternsPurviews" -> diffPattPurviews,  
         "CompleteProbabilityDistribution" -> completeProbDistr["ProbabilityDistribution"]
         |>
    ];
    

calculateIntegrationInformationToHD[partitions_, purviews_, inputs_, outputs_, 
	currentCandidateSetState_, ucPastProbDist_, ucFutProbDist_,path_,probCandidateSetDistribution_,
	probDistributionAttr_] :=
    Block[ {},

        pastPossDistribArray = List[];
        futPossDistribArray = List[];
        
        For[p = 1, p <= Length[partitions], p++,
            onePartition = Sort[Part[partitions, p]];
            ciByMechanism = List[];
            eiByMechanism = List[];
            ceiByMechanism = List[];
            pastPossDistribArrayByMechanism = List[];
            futPossDistribArrayByMechanism = List[];
            
            onePurview = Sort[ Part[purviews, pp]];
            (*-------------  PAST ANALYSIS -------------*)
            pastProbabilityDistribution = probabilityDistributionCalculation[onePartition, onePurview, outputs, inputs, currentCandidateSetState, "causal"];
            currentPStates = pastProbabilityDistribution["OutputsWithCurrentSubstate"];
            possiblePStates = pastProbabilityDistribution["PossiblePastFutureStates"];
            indexesPStates = pastProbabilityDistribution["IndexesOutElementsCurrentSubstate"];
            pastDistribution = pastProbabilityDistribution["CompleteProbabilityDistribution"];
            (*begin-------------------------------------------------*)
            (*Print[" ------------- an analysis start here ------------"];
            Print["Current set state:"<>ToString[currentCandidateSetState]<>" Partition: "<> ToString[onePartition]<> " Purview:"<> ToString[onePurview]];
            Print["Past Probabilities distribution: "];
            Print[ToString[pastDistribution]];*)
            (*end-------------------------------------------------*)
            (*AppendTo[pastPossDistribArrayByMechanism, pastDistribution];*)
            
            fileName=ToString[onePartition]<>ToString[onePurview];
            keyName ={onePartition,onePurview};
            
            Export[path<>"PastProbDist"<>fileName<>".csv",pastDistribution,"CSV"];
            ci = EuclideanDistance[pastDistribution, ucPastProbDist];
            AppendTo[ciByMechanism,Association[<|keyName->ci|>]];
            (*begin-------------------------------------------------*)
            (*Print["------ Past Analysis  --------"];
            Print["Current states : " <> ToString[Length[currentPStates]] <>" elements"];
            Print[currentPStates];
            Print["Possible Past States: "];
            Print[possiblePStates];
            Print["Indexes Possible Past States" <> ToString[Length[
            indexesPStates]] <> " elements"];
            Print[indexesPStates];
            Print["Past Distribution: " <> ToString[Length[pastDistribution]] <> " elements"];
            Print[pastDistribution];
            Print[Counts[pastDistribution]];
            Print["---------------------------------------------------- "];
            Print["ci: " <> ToString[ci]];
            Print["---------------------------------------------------- "];*)
            (*end-------------------------------------------------*)
            (*-------------  FUTURE ANALYSIS -------------*)
            futureProbabilityDistribution = probabilityDistributionCalculation[onePartition, onePurview,outputs, inputs, currentCandidateSetState, "effect"];
            currentFStates = futureProbabilityDistribution["OutputsWithCurrentSubstate"];
            possibleFStates = futureProbabilityDistribution["PossiblePastFutureStates"];
            futDistribution = futureProbabilityDistribution["CompleteProbabilityDistribution"];
            (*AppendTo[futPossDistribArrayByMechanism, futDistribution];*)
            
            Export[path<>"FutureProbDist"<>fileName<>".csv",futDistribution,"CSV"];
            ei = EuclideanDistance[futDistribution, ucFutProbDist];
            AppendTo[eiByMechanism,Association[<|keyName->ei|>]];
            
            minimo = Min[ci, ei];
            AppendTo[ceiByMechanism,Association[<|keyName->minimo|>]];
            (*Print["---------------------------------"];
            Print["mechanism: " <> ToString[onePartition]<> " purview: "<> ToString[onePurview]];
            Print["cei: "<> ToString[minimo]];
            Print["---------------------------------"];*)
            (*Print["------ FUTURE Analysis  --------"];
            Print["Current states : " <> ToString[Length[currentFStates]] <> " elements"];
            Print[currentFStates];
            Print["Possible Future States: "];
            Print[possibleFStates];
            Print["Future Distribution: "];
            Print[futDistribution];
            Print[Counts[futDistribution]];
            Print["------------------------------------------------- "];
            Print["ei: " <> ToString[ei]];
            Print["------------------------------------------------- "];*)
            (*AppendTo[ciArray, ciByMechanism];
            AppendTo[eiArray, eiByMechanism];
            AppendTo[ceiArray, ceiByMechanism];
            AppendTo[pastPossDistribArray, pastPossDistribArrayByMechanism];
            AppendTo[futPossDistribArray, futPossDistribArrayByMechanism];*)
        ];
        (*Export["/home/alberto/01_ALPHA/ciArray.csv", ciArray, "CSV"];
        Export["/home/alberto/01_ALPHA/eiArray.csv", eiArray, "CSV"];
        Export["/home/alberto/01_ALPHA/ceiArray.csv", ceiArray, "CSV"];
        Export["/home/alberto/01_ALPHA/pastPossDistribArray.csv",pastPossDistribArray, "CSV"];
        Export["/home/alberto/01_ALPHA/futPossDistribArray.csv",futPossDistribArray, "CSV"];*)
        
        (*Maximal Irreducible Cause and Effect = Concept*)
        (*Indexes are needed to recover probability Distributions*)
        (*from Phi view, a mechanism is the max value of ci/ei of each meachanism
        compared with each possible purview. From Alpha view, there are not valid
        comparisons. Then comparisons found by Alpha equivalente to mechanisms and
        purviews' phi are equivalent to concepts.
        *)
        (*cMICE = Table[Max[Part[ciArray, h]], {h, 1, Length[ciArray], 1}];
        indexCMICE = Table[Flatten[Position[Part[ciArray, hh], Part[cMICE, hh]]], {hh, 1, Length[ciArray], 1}];
        eMICE = Table[Max[Part[eiArray, ii]], {ii, 1, Length[eiArray], 1}];
        indexEMICE = Table[Flatten[Position[Part[eiArray, jj], Part[eMICE, jj]]], {jj,1, Length[eiArray], 1}];*)
        
        cMICE = ciByMechanism;
        eMICE = eiByMechanism;
        
        (*It is possible to obtain repeted values in MIP,then I take the first*)
        (*cMIP = Min[Values[ciByMechanism]];
        indexCMIP = Position[ciArray, cMIP];
        noRepIndexesCMIP = Length[indexCMIP];
        
        eMIP = Min[eiArray];
        indexEMIP = Position[eiArray, eMIP];
        noRepIndexEMIP = Length[indexEMIP];
        *)
        
        cMIP = Keys @ MinimalBy[Value]@ ciByMechanism;
        eMIP = Keys @ MinimalBy[Value]@ eiByMechanism;
        
        (*ppPMIPDistrib = Extract[pastPossDistribArray, First[indexCMIP]];
        ppFMIPDistrib = Extract[futPossDistribArray, First[indexEMIP]];*)
        
        ppPMIPDistrib = Import[path<>"PastProbDist"<>ToString[cMIP]<>".csv","CSV"];
        ppFMIPDistrib = Import[path<>"FutureProbDist"<>ToString[cMIP]<>".csv","CSV"];
        
        cIWholeSystemDistrib = Last[Last[pastPossDistribArray]];
        eiWholeSystemDistrib = Last[Last[futPossDistribArray]];
        
        
        (*smallAlpha = Min[Power[EuclideanDistance[ppPMIPDistrib, cIWholeSystemDistrib],noRepIndexesCMIP],
        	Power[EuclideanDistance[ppFMIPDistrib, eiWholeSystemDistrib],noRepIndexEMIP]]/2;*)
        	
        (*[...] small phi is calculated as the distance between the cause-effect repertoire
        specified by the whole mechanism against the cause-effect repertoire of the partitioned
        mechanism. Of the many possible ways to partition a mechanism, ii is evaluated across
         the minimum information partiton (MIP), the partition that makes the last difference
         to the cause and effect repertoires*)
        smallAlpha = Min[EuclideanDistance[ppPMIPDistrib, cIWholeSystemDistrib],
        	EuclideanDistance[ppFMIPDistrib, eiWholeSystemDistrib]];
        	
        (*
        concepts computation: 
        a) distance between each purview's prob. distrib. and the whole sys prob. distribution is calculated.
        b) every max in (a) is found. These are the concepts
        *)
        pastSmallAlphasArray = List[];
        conceptPastIndexes = List[];
        futSmallAlphasArray = List[];
        conceptFutIndexes = List[];
        
        For[aa = 1, aa <= Length[pastPossDistribArray], aa++,
            pastSmallAlphaByMechanism = List[];
            futSmallAlphaByMechanism = List[];
            pastProbDistribOfMechanism = Part[pastPossDistribArray, aa];
            futProbDistribOfMechanism = Part[futPossDistribArray, aa];
            For[bb = 1, bb <= Length[pastProbDistribOfMechanism], bb++,
                  onePastProbDistrb = Part[pastProbDistribOfMechanism, bb];
                  oneFutProbDistrb = Part[futProbDistribOfMechanism, bb];
                  AppendTo[pastSmallAlphaByMechanism,EuclideanDistance[cIWholeSystemDistrib, onePastProbDistrb]];
                  AppendTo[futSmallAlphaByMechanism,EuclideanDistance[eiWholeSystemDistrib, oneFutProbDistrb]];
            ];
            AppendTo[pastSmallAlphasArray, pastSmallAlphaByMechanism];
            AppendTo[futSmallAlphasArray, futSmallAlphaByMechanism];
            maxPastSmallAlpha = Max[pastSmallAlphaByMechanism];
            maxFutSmallAlpha = Max[futSmallAlphaByMechanism];
            secondPastIndex = First[Position[pastSmallAlphaByMechanism, maxPastSmallAlpha]];
            secondFutIndex = First[Position[futSmallAlphaByMechanism, maxFutSmallAlpha]];
            completePastIndex = Flatten[{aa, secondPastIndex}];
            completeFutIndex = Flatten[{aa, secondFutIndex}];
            AppendTo[conceptPastIndexes, completePastIndex];
            AppendTo[conceptFutIndexes, completeFutIndex];
         ];
        
        (*Conceptual Information  By Definition CI=Sum[Distance[probDisCOncept, ucProbDistrb]x conceptValue]*)
        cCITable = Table[
                          EuclideanDistance[Extract[pastPossDistribArray, conceptPastIndexes[[uu]]],ucPastProbDist]*
                          Extract[pastSmallAlphasArray, conceptPastIndexes[[uu]]],{uu,1, Length[conceptPastIndexes], 1}];
        cCI = Total[cCITable];
        Print["cCI: "<> ToString[cCI]];
        eCITable = Table[
                          EuclideanDistance[Extract[futPossDistribArray, conceptFutIndexes[[vv]]],ucFutProbDist]*
                          Extract[futSmallAlphasArray, conceptFutIndexes[[vv]]],{vv, 1,Length[conceptFutIndexes], 1}];
        eCI = Total[eCITable];
        Print["eCI: "<> ToString[eCI]];
        Print["Number of concepts: " <> ToString[Length[conceptPastIndexes]]];
        (*BIG ALPHA*)
        pastConceptValues = Extract[pastSmallAlphasArray, conceptPastIndexes];
        distPastConceptsToUCProbDist = Extract[ciArray, conceptPastIndexes];
        futConceptValues = Extract[futSmallAlphasArray, conceptFutIndexes];
        distFutConceptsToUCProbDist = Extract[eiArray, conceptFutIndexes];
        conceptPartitions = Delete[Subsets[Range[Length[conceptPastIndexes]]], 1];
        bigAlphaArray = List[];
        Print["looping over concept partitions: (" <> ToString[Length[conceptPartitions]]<> ") elements"];
        For[vv = 1, vv <= Length[conceptPartitions], vv++,
                                                     partition = Part[conceptPartitions, vv];
                                                     oneBigAlpha = Min[Total[Table[(Part[distPastConceptsToUCProbDist, Part[partition, w]] +
                                                                                     Part[distFutConceptsToUCProbDist, Part[partition, w]])*
                                                                                     Part[pastConceptValues, Part[partition, w]], 
                                                                             {w, 1,Length[partition], 1}]
                                                                             ],
                                                                        Total[Table[(Part[distPastConceptsToUCProbDist,Part[partition, w]] +
                                                                                        Part[distFutConceptsToUCProbDist, Part[partition, w]])*
                                                                                        Part[futConceptValues, Part[partition, w]], 
                                                                                {w, 1,Length[partition], 1}]]
                                                                        ];
                                                     AppendTo[bigAlphaArray, oneBigAlpha];
         ];
        bigAlpha = Min[bigAlphaArray];
        (*Print["+++++++++++++++++++++++++++++++++++++++++++"];
        Print["CI: "];
        Print[ciArray];
        Print["EI: "];
        Print[eiArray];
        Print["CEI: "];
        Print[ceiArray];
        Print["+++++++++++++++++++++++++++++++++++++++++++"];*)
        <| 
         "CEIArray" -> ceiArray, "CIArray" -> ciArray, 
         "EIArray" -> eiArray, "cMIP" -> cMIP, "eMIP" -> eMIP, 
         "IndexCMIP" -> indexCMIP, "IndexEMIP" -> indexEMIP, 
         "cMICE" -> cMICE, "eMICE" -> eMICE, "IndexCMICE" -> indexCMICE, 
         "IndexEMICE" -> indexEMICE, 
         "PastPossDistribArray" -> pastPossDistribArray, 
         "FutPossDistribArray" -> futPossDistribArray, 
         "SmallAlpha" -> smallAlpha, 
         "PastSmallAlphasArray" -> pastSmallAlphasArray , 
         "ConceptPastIndexes" -> conceptPastIndexes, 
         "FutSmallAlphasArray" -> futSmallAlphasArray , 
         "ConceptFutIndexes" -> conceptFutIndexes, "CCI" -> cCI, 
         "ECI" -> eCI, "BigAlpha" -> bigAlpha|>
    ];
    
