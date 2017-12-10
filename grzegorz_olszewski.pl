
 :- module(grzegorz_olszewski, [resolve/4, prove/2]).

:- op(200, fx, ~).
:- op(500, xfy, v).

is_clause([]) :- !.
is_clause(C) :- is_non_empty_clause(C).

is_non_empty_clause(L) :- is_literal(L), !.
is_non_empty_clause(L v C) :-
  is_literal(L), is_non_empty_clause(C).

is_literal(X) :- is_variable(X), !.
is_literal(~X) :- is_variable(X).

is_variable([]) :- !, fail.
is_variable(X) :- atom(X).

clause_to_collection([],([],[])):-!.	

clause_to_collection(Clause,Collection):-
	clause_to_collection(Clause,Collection,[],[]).

clause_to_collection(L,([L|Pos],Neg),Pos,Neg):-
	is_variable(L).

clause_to_collection(~L,(Pos,[~L|Neg]),Pos,Neg):-
	is_variable(L).

clause_to_collection(L v C,(Pos,Neg),Pos1,Neg1):-
	is_variable(L),
	is_non_empty_clause(C),
	clause_to_collection(C,(Pos2,Neg2),[],[]),
	append([L|Pos1],Pos2,Pos3),
	sort(Pos3,Pos),
	append(Neg1,Neg2,Neg3),
	sort(Neg3,Neg).

clause_to_collection(~L v C,(Pos,Neg),Pos1,Neg1):-
	is_variable(L),
	is_non_empty_clause(C),
	clause_to_collection(C,(Pos2,Neg2),[],[]),
	append(Pos1,Pos2,Pos3),
	sort(Pos3,Pos),
	append([~L|Neg1],Neg2,Neg3),
	sort(Neg3, Neg).

conv(Clauses,Quadriples):-
	conv(Clauses,Quadriples,[],1).
conv([],Quad,L,_):-
	reverse(L,Quad),!.	
conv([C|Cs],Quad,NCs,Ind):-
	clause_to_collection(C,(Pos,Neg)), Ind1 is Ind + 1, conv(Cs,Quad,[[Ind,Pos,Neg,axiom]|NCs],Ind1).

resolve1(Lit,Cl1,Cl2,Res):-
	delete(Cl1,Lit,L1),
	delete(Cl2,~Lit,L2),
	append(L1,L2,Res).

resolve(Lit,Cl1,Cl2,Res):-
	clause_to_list(Cl1,L1),
	clause_to_list(Cl2,L2),
	resolve1(Lit,L1,L2,Res1),
	merge_to_clause2(Res1,Res),!.

resolve2(X,[Ind1,Pos1,Neg1,_],[Ind2,Pos2,Neg2,_],[Index,Pos,Neg,[X,Ind1,Ind2]],Index):- 
	delete(Pos1,X,Pos3),
	delete(Neg2,~X,Neg3),
	ord_union(Pos2,Pos3,Pos),
	ord_union(Neg1,Neg3,Neg).

clause_to_list(K, T):-
	clause_to_list(K, T, []).

clause_to_list(K,[K|T],T):-
	is_literal(K).

clause_to_list(L v C, F, K):-
	is_literal(L),
	is_non_empty_clause(C),
	clause_to_list(C, V, []),
	append(V,[L|K], F).

clause_to_list([],K,K).

merge_to_clause2([],[]).
merge_to_clause2([K],K):-
	is_literal(K).
merge_to_clause2([H|T],H v P):-
	merge_to_clause2(T, P),!.

res([Ind1,Pos,Neg,Origin1],Clause2,Resolvents,IndexTemp,IndexOut):-
	append(Pos,Neg,PosNeg),
	res([Ind1,Pos,Neg,Origin1],Clause2,PosNeg,IndexTemp,IndexOut,[],Resolvents).
res(_,_,[],Index,Index,ResTemp,Resolvents):-
	reverse(ResTemp,Resolvents). 
res(Clause1,[Ind,Pos,Neg,Origin],[H|T],Index,IndexOut,ResTemp,Resolvents):-
	is_variable(H), 
	member(~H,Neg),
	resolve2(H,Clause1,[Ind,Pos,Neg,Origin],Clause3,Index),
	Index1 is Index + 1,
	res(Clause1,[Ind,Pos,Neg,Origin],T,Index1,IndexOut,[Clause3|ResTemp],Resolvents).

res(Clause1,[Ind,Pos,Neg,Origin],[~H|T],Index,IndexOut,ResTemp,Resolvents):-
	is_variable(H),
	member(H,Pos),
	resolve2(H,[Ind,Pos,Neg,Origin],Clause1,Clause3,Index),
	Index1 is Index + 1,
	res(Clause1,[Ind,Pos,Neg,Origin],T,Index1,IndexOut,[Clause3|ResTemp],Resolvents).

res(Clause1,[Ind,Pos,Neg,Origin],[~H|T],Index,IndexOut,ResTemp,Resolvents):-
	is_variable(H),
	not(member(H,Pos)),
	res(Clause1,[Ind,Pos,Neg,Origin],T,Index,IndexOut,ResTemp,Resolvents).

res(Clause1,[Ind,Pos,Neg,Origin],[H|T],Index,IndexOut,ResTemp,Resolvents):-
	is_variable(H),
	not(member(~H,Neg)),
	res(Clause1,[Ind,Pos,Neg,Origin],T,Index,IndexOut,ResTemp,Resolvents).

intersec([_,Pos1,Neg1,_],[_,Pos2,Neg2,_],[_,Pos3,Neg3,_]):-
	intersection(Pos1,Pos2,Pos3),
	intersection(Neg1,Neg2,Neg3).
check(L1,L2,Res):-
	check1(L1,L2,L2,[],Res).

check1([],_,_,Temp,Res):-
	reverse(Temp,Res).
check1([H1|T1],[],Old,Temp,Res):-
	check1(T1,Old,Old,[H1|Temp],Res).
check1([H1|T1],[H2|_],Old,Temp,Res):-
	intersec(H2,H1,H2),
	check1(T1,Old,Old,Temp,Res).
check1([H1|T1],[H2|T2],Old,Temp,Res):-
	not(intersec(H2,H1,H2)),
	check1([H1|T1],T2,Old,Temp,Res).

to_tuple([_,Pos,Neg,axiom],(Clause,axiom)):-
	append(Pos,Neg,PosNeg),
	merge_to_clause2(PosNeg,Clause).
to_tuple([_,Pos,Neg,[X,Cl1,Cl2]],(Clause,X,Cl1,Cl2)):-
	append(Pos,Neg,PosNeg),
	merge_to_clause2(PosNeg,Clause).
to_tuples(List,Tuples):-
	maplist(to_tuple,List,Tuples).

prove(Clauses,[Proof]):-
	conv(Clauses,Collections),
	member([Ind,[],[],Origin],Collections),
	to_tuple([Ind,[],[],Origin],Proof).

prove(Clauses,Proof):-
	conv(Clauses,Collections),
	length(Collections,Len1),
	Index is Len1 + 1,
	prove(Collections,[],[],Proof,Index). 

prove([H|_],[H1|_],Old,Proof,Index):-
	res(H,H1,K,Index,_),
	member([_,[],[],_],K),
	reverse([H|Old],Pr1),
	append(Pr1,K,Res),
	to_tuples(Res,Proof),!.

prove([H|T],[H1|T1],Old,Proof,Index):-
	res(H,H1,K,Index,IndexOut),
	check(K,Old,ToAdd),
	check(ToAdd,T,ToAdd2),
	append([H|T],ToAdd2,New),
	prove(New,T1,Old,Proof,IndexOut).

prove([H|T],[],Old,Proof,Index):-
	prove(T,[H|Old],[H|Old],Proof,Index).



