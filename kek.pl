verify(InputFileName) :- % read file
see(InputFileName),
read(Prems), read(Goal), read(Proof),
seen,
valid_proof(Prems, Goal, Proof). % validate proof

valid_proof(Prems, Goal, Proof) :- % This is where we validate the proof, more rules can be added
checkGoal(Goal, Proof), % Checks that last line in Proof == Goal
	reverse(Proof, ReverseProof), %reverse order to search bottom up				
	checkProof(ReverseProof,Proof,Prems). %checks if each line is correct

checkGoal(Goal, Proof) :-
last(Proof, [_,Conclusion,_]), % Takes the snd of the last element/(line) from Proof.
Conclusion == Goal. % Check if matching with Goal.

/* Iterate through the given proof and checks if the given Line matches a Statement, if so, match Statement*/
iterateList(Line, [[Line,Statement,_]|_], Statement) :-!.
iterateList(Line, [[_,_,_]|Proof], Statement) :-
	iterateList(Line, Proof, Statement),!.
iterateList(Line, [[[_,_,_]|_]|Proof], Statement) :-
	iterateList(Line, Proof, Statement).
			 
checkProof([],_,_):- !. %basecase
checkProof([Head|Tail],Proof,Prems) :- % Takes the first element of the proof list and checks its rule.
	checkRule(Head, Proof,Prems), % Call check rule on Head
	checkProof(Tail, Proof,Prems),!. % Tail recursion

% If the rule is a box, in which the first rule is an assumption,
% append the reversed box on to the proof, and check the box as we would check a normal proof.
checkRule([[Line, Statement, assumption]|Tail], Proof,Prems) :- 
	% boxassumption replaces assumption to match a case in checkRule
	reverse([[Line, Statement, boxassumption]|Tail], ReverseBox), 
	append(ReverseBox, Proof, ParentProof), %Parentproof becomes the allowed reachable lines.
	checkProof(ReverseBox, ParentProof,Prems).

checkRule([Line, Statement, andel1(X)], Proof,_) :- % Check if andel1 is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	S = and(Statement,_). % Check if the rule is fulfilled

checkRule([Line, Statement, andel2(X)], Proof,_) :- % Check if andel2 is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	S = and(_,Statement). % Check if the rule is fulfilled

checkRule([Line, Statement, andint(X,Y)], Proof,_):- % Check if andint is correct
	Line > X, Line > Y, % Cant reach a line below
	iterateList(X, Proof, S1), % Get the statement from line X, match with S1
	iterateList(Y, Proof, S2), % Get the statement from line Y, match with S2
	Statement = and(S1,S2). % Check if the rule is fulfilled

checkRule([Line, Statement, orint1(X)], Proof,_):- % Check if orint1 is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	Statement = or(S,_). % Check if the rule is fulfilled

checkRule([Line, Statement, orint2(X)], Proof,_):- % Check if orint2 is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	Statement = or(_,S). % Check if the rule is fulfilled

checkRule([Line, Statement, impel(X,Y)], Proof,_):- % Check if impel is correct
	Line > X, Line > Y, % Cant reach a line below
	iterateList(X, Proof, S1), % Get the statement from line X, match with S1
	iterateList(Y, Proof, S2), % Get the statement from line Y, match with S2
	S2 = imp(S1,Statement). % Check if the rule is fulfilled

checkRule([Line, Statement, negel(X,Y)], Proof,_):- % Check if negel is correct
	Line > X, Line > Y, % Cant reach a line below
	iterateList(X, Proof, S1), % Get the statement from line X, match with S1
	iterateList(Y, Proof, S2), % Get the statement from line Y, match with S2
	% Check if the rule is fulfilled
	S2 = neg(S1), 
	Statement = cont. 

checkRule([Line, Statement, copy(X)], Proof,_):- % Check if copy is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	Statement = S. % Check if the rule is fulfilled

checkRule([Line, _, contel(X)], Proof,_):- % Check if contel is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	S = cont. % Check if the rule is fulfilled

checkRule([Line, Statement, negnegel(X)], Proof,_):- % Check if negnegel is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	S = neg(neg(Statement)). % Check if the rule is fulfilled

checkRule([Line, Statement, negnegint(X)], Proof,_):- % Check if negnegint is correct
	Line > X, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S
	Statement = neg(neg(S)).		 % Check if the rule is fulfilled	

checkRule([Line, Statement, mt(X,Y)], Proof,_):- % Check if mt is correct
	Line > X, Line > Y, % Cant reach a line below
	iterateList(X, Proof, S1), % Get the statement from line X, match with S1
	iterateList(Y, Proof, S2), % Get the statement from line Y, match with S2
	 % Check if the rule is fulfilled
	S1 = imp(From, To),
	S2 = neg(To),
	Statement = neg(From).

checkRule([_, Statement, lem], _,_):- % Check if lem is correct
	 % Check if the rule is fulfilled
	Statement = or(X, neg(X));
	Statement = or(neg(X), X).

checkRule([Line, Statement, impint(X,Y)], Proof,_) :- % Check if impint is correct
	Line > X, Line > Y, % Cant reach a line below
	getBox(X, Y, Box, Proof), %Get the Box from lines X to Y
	reverse(Box, ReverseBox),
	last(ReverseBox, First), %Last element from a reversed box equals the first.
	getStatement(First, FirstStatement), 
	last(Box, Last),
 	getStatement(Last, LastStatement), !,
	Statement = imp(FirstStatement, LastStatement). % Check if the rule is fulfilled

checkRule([Line, Statement, pbc(X,Y)], Proof,_) :- % Check if pbc is correct
	Line > X, Line > Y, % Cant reach a line below
	getBox(X, Y, Box, Proof), %Get the Box from lines X to Y
	reverse(Box, ReverseBox),
	last(ReverseBox, First),  %Last element from a reversed box equals the first.
	getStatement(First, FirstStatement), 
	last(Box, Last),
 	getStatement(Last, LastStatement), !, 
	 % Check if the rule is fulfilled
	FirstStatement = neg(Statement),
	LastStatement = cont.

checkRule([Line, Statement, negint(X,Y)], Proof,_) :- % Check if negint is correct
	Line > X, Line > Y, % Cant reach a line below
	getBox(X, Y, Box, Proof), %Get the Box from lines X to Y
	reverse(Box, ReverseBox),
	last(ReverseBox, First),  %Last element from a reversed box equals the first.
	getStatement(First, FirstStatement), 
	last(Box, Last),
 	getStatement(Last, LastStatement), !, 
	 % Check if the rule is fulfilled
	Statement = neg(FirstStatement),
	LastStatement = cont.

checkRule([Line, Statement, orel(X,Y,U,V,W)], Proof,_) :- % Check if orel is correct
	Line > X, Line > Y, Line > U, Line > V, Line > W, % Cant reach a line below
	iterateList(X, Proof, S), % Get the statement from line X, match with S

	getBox(Y, U, Box1, Proof), %Get the Box from lines Y to U
	reverse(Box1, ReverseBox1),
	last(ReverseBox1, First1),  %Last element from a reversed box equals the first.
	getStatement(First1, FirstStatement1), 
	last(Box1, Last1),
 	getStatement(Last1, LastStatement1), !, 

 	getBox(V, W, Box2, Proof), %Get the Box from lines V to W
	reverse(Box2, ReverseBox2),
	last(ReverseBox2, First2),   %Last element from a reversed box equals the first.
	getStatement(First2, FirstStatement2), 
	last(Box2, Last2),
 	getStatement(Last2, LastStatement2), !,

	% Check if the rule is fulfilled
 	S = or(FirstStatement1, FirstStatement2),
 	Statement = LastStatement1,
 	Statement = LastStatement2.

checkRule([_, Statement, premise], _,Prems) :- % Check if premise is correct
	member(Statement, Prems),!. % Premise needs to be defined in the premise list.

checkRule([_,_, boxassumption],_,_). % Case for searching through boxes 

/* Gets the box from line X to Y */
getBox(X, Y, Box, [[[X,Statement,assumption]|BoxRest]|_]) :- 
	getEndBox([[X,Statement,assumption]|BoxRest], Y, Box),!.
getBox(X, Y, Box, [_|Proof]) :- 
	getBox(X, Y, Box, Proof).


/* Help predicate to getBox */
getEndBox([],_,_):-!.
getEndBox([[X, Statement, Rule]|_], X, [[X, Statement, Rule]]) :- !.
getEndBox([[[X, Statement, Rule]|Rest]|BoxRest1], Y, [[[X, Statement, Rule]|Rest]|BoxRest2]) :-
	getEndBox(BoxRest1, Y, BoxRest2),!.
getEndBox([[X, Statement, Rule]|BoxRest1], Y, [[X, Statement, Rule]|BoxRest2]) :-
	getEndBox(BoxRest1, Y, BoxRest2).

getStatement([_,Statement,_], Statement). % Gets the Statement from the given triple


