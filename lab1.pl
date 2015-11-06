verify(InputFileName) :- % read file
        see(InputFileName),
        read(Prems), read(Goal), read(Proof),
        seen,
        valid_proof(Prems, Goal, Proof). % validate proof
 
valid_proof(Prems, Goal, Proof) :- % This is where we validate the proof, more rules can be added
        checkGoal(Goal, Proof), % Checks that last line in Proof == Goal
        checkPremise(Prems, Proof), % Checks that all of the defined premises are in the Proof.
				reverse(Proof, ReverseProof), 				
				checkProof(ReverseProof,Proof).

checkGoal(Goal, Proof) :-
        last(Proof, [_,Conclusion,_]), % Takes the snd of the last element/(line) from Proof.
        Conclusion == Goal. % Check if matching with Goal.

checkPremise(Prems, [[_,Statement,premise]|Tail]) :-
        member(Statement,Prems),!, % Trying to find Head in the Proof, defined as a premise.
        checkPremise(Prems, Tail),!. % Recursion with rest of list (that defines the premises).

%checkPremise(_, [[[]]|Tail]):-!.

checkPremise(Prems, [[[_,_,assumption]|BoxTail]|Tail]):- % Start of box, search through box and then rest of tail
				checkPremise(Prems, BoxTail),!, 
				checkPremise(Prems, Tail),!.

checkPremise(Prems, [[_,_,Rule]|Tail]) :-
				Rule \= premise,
				checkPremise(Prems, Tail), !.

checkPremise(_,[]). % Base case


iterateList(Line, [[Line,Statement,_]|_], Statement) :-!.
iterateList(Line, [[_,_,_]|Proof], Statement) :-
				iterateList(Line, Proof, Statement).
				 

checkProof([],_):- !.
checkProof([Head|Tail],Proof) :-
				checkRule(Head, Proof),
				checkProof(Tail, Proof),!.

%checkBoxProof([Head|Tail],Proof) :-
%				checkRule(Head, Proof),
%				checkProof(Tail, Proof),!.


checkRule([[Line, Statement, assumption]|Tail], Proof) :-
				reverse([[Line, Statement, premise]|Tail], ReverseBox),
				checkProof(ReverseBox, Proof).



checkRule([_, Statement, andel1(X)], Proof) :-
				iterateList(X, Proof, S),
				S = and(Statement,_).

checkRule([_, Statement, andel2(X)], Proof) :-
				iterateList(X, Proof, S),
				S = and(_,Statement).

checkRule([_, Statement, andint(X,Y)], Proof):-
				iterateList(X, Proof, S1),
				iterateList(Y, Proof, S2),
				Statement = and(S1,S2).

checkRule([_, Statement, orint1(X)], Proof):-
				iterateList(X, Proof, S),
				Statement = or(S,_).

checkRule([_, Statement, orint2(X)], Proof):-
				iterateList(X, Proof, S),
				Statement = or(_,S).

checkRule([_, Statement, impel(X,Y)], Proof):-
				iterateList(X, Proof, S1),
				iterateList(Y, Proof, S2),
				S2 = imp(S1,Statement).

checkRule([_, Statement, negel(X,Y)], Proof):-
				iterateList(X, Proof, S1),
				iterateList(Y, Proof, S2),
				S2 = neg(S1),
				Statement = cont.

checkRule([_, Statement, copy(X)], Proof):-
				iterateList(X, Proof, S),
				Statement = S.

checkRule([_, _, contel(X)], Proof):-
				iterateList(X, Proof, S),
				S = cont.

checkRule([_, Statement, negnegel(X)], Proof):-
				iterateList(X, Proof, S),
				S = neg(neg(Statement)).

checkRule([_, Statement, negnegint(X)], Proof):-
				iterateList(X, Proof, S),
				Statement = neg(neg(S)).			

checkRule([_, Statement, mt(X,Y)], Proof):-
				iterateList(X, Proof, S1),
				iterateList(Y, Proof, S2),
				S1 = imp(From, To),
				S2 = neg(To),
				Statement = neg(From).

checkRule([_, Statement, lem], _):-
				Statement = or(X, neg(X));
				Statement = or(neg(X), X).

% TODO:
% BOXAR:
% assumption
% orel(x,y,u,v,w)
% impint(x,y)
% negint(x,y)
% pbc(x,y)

checkRule([_, _, premise], _).



				
