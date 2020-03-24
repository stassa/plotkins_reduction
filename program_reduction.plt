:-use_module(examples).
:-use_module(program_reduction).

/* Tests for the implementation of Plotkin's program reduction.

Tests in this file use the example programs in examples.pl. These are
unfortunately not always very clear in their intention.

Some tests are blocked with the reason "Goes infinite". Such tests
result in an infinite recursion, unless tabling is used, in which case
most tests fail.
*/


:-begin_tests(program_reduction).

test(example_kin_a, [blocked('Goes infinite')
		    ,setup(test_settings(D1,R1,5,1000))
		    ,cleanup(reset_settings(D1,R1))
		    ,nondet]):-
	example(kin_a,P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(m(fm,parent))
	      ,(m(P1,X1,Y1) :- m(_Q1,Y1,X1), m(fm,P1))
	      ,(m(child,X2,Y2) :- m(father,Y2,X2))
	      ,(m(child,X3,Y3) :- m(mother,Y3,X3))
	      ]
	,permutation(R, R_)
	,D_ = [(m(P4,X4,Y4) :- m(_Q4,X4,Y4), m(fm,P4))
	      ,(m(parent,X5,Y5) :- m(father,X5,Y5))
	      ,(m(parent,X6,Y6) :- m(mother,X6,Y6))
	      ]
	,permutation(D, D_).

test(example_kin_b, [blocked('Goes infinite')
		    ,setup(test_settings(D1,R1,5,1000))
		    ,cleanup(reset_settings(D1,R1))
		    ,nondet
		    ]):-
	example(kin_b,P)
	,program_reduction(P, R, D)
	,R_ = [(m(fm,child))
	     ,(m(P1,X1,Y1) :- m(_Q,Y1,X1), m(fm,P1))
	     ,(m(parent,X2,Y2) :- m(father,X2,Y2))
	     ,(m(parent,X3,Y3) :- m(mother,X3,Y3))
	 ]
	,permutation(R, R_)
	,D_ = [(m(P4,X4,Y4) :- m(_Q4,X4,Y4), m(fm,P4))
	      ,(m(child,X5,Y5) :- m(father,Y5,X5))
	      ,(m(child,X6,Y6) :- m(mother,Y6,X6))
	 ]
	,permutation(D, D_).

test(example_0b1, []):-
	example('0b1',P)
	,program_reduction(P, R, D)
	,!
	,R = [(m(P1,X2,Y2) :- m(Q,Y2,X2))]
	,D = [(m(P1,X1,Y1) :- m(Q,X1,Y1))].

test(example_0b2, [blocked('Goes infinite')
		  ]):-
	example('0b2',P)
	,program_reduction(P, R, D)
	,!
	,R = [(m(P1,X2,Y2) :- m(Q,Y2,X2))]
	,D = [(m(P1,X1,Y1) :- m(Q,X1,Y1))].

test(example_1a1, [blocked('Needs definition of body goals')
		  ]):-
	example('1a1',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- q(X1))]
	,D = [(p(X2) :- q(X2), r(X2))].

test(example_1b1, [blocked('Needs definition of body goals')
		  ,nondet
		  ]):-
	example('1b1',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- q(X1))]
	,permutation(D, [(p(X3) :- q(X3), r(X3), r(X3))
			,(p(X2) :- q(X2), r(X2))
			]
		    ).

test(example_1b2, [nondet]):-
	example('1b2',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- q(X1))]
	,permutation(D, [(p(X2) :- q(X2), r(X2))
			,(p(X3) :- q(X3), r(X3), r(X3))
			]
		    ).

test(example_1c, [
	 blocked('No idea what''s the correct result.')
     ]):-
	example('1c',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(_A1):-q(_B1))
	     ,(p(_A2):-q(a3))
	     ,(p(_A3):-q(_B3),r(_C3))
	     ,(p(_A4):-q(a),r(_B4))
	     ,(p(_A5):-q(_B5),r(a12))
	     ,(p(_A6):-q(a15),r(b15))
	     ,(p(a10):-q(_A7),r(_B7))
	     ,(p(a13):-q(b13),r(_A8))
	     ,(p(a14):-q(_A9),r(b14))
	     ,(p(a16):-q(b16),r(c16))
	     ,(p(a2):-q(_A10))
	     ,(p(a4):-q(b4))
	     ,(p(a5):-q(a5))
	     ]
	,D = [(p(_A11):-q(B11),r(B11))
	     ,(p(A12):-q(_B12),r(A12))
	     ,(p(A13):-q(A13),r(A13))
	     ].

test(example_2a1, [nondet]):-
	example('2a1',P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(lessthan(X1,Y1) :- successor(X1,Y1))
	      ,(lessthan(X3,Y3) :- successor(X3,Z3), lessthan(Z3,Y3))
	      ]
	,permutation(R, R_)
	,D = [(lessthan(X2,Y2) :- successor(X2,Z2), successor(Z2,Y2))].

test(example_2a2, [nondet]):-
	example('2a2',P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(lessthan(X3,Y3) :- successor(X3,Z3), lessthan(Z3,Y3))
	      ,(lessthan(X1,Y1) :- successor(X1,Y1))
	     ]
	,permutation(R, R_)
	,D = [(lessthan(X2,Y2) :- successor(X2,Z2), successor(Z2,Y2))].

test(example_2a3, [nondet]):-
	example('2a3',P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(lessthan(X3,Y3) :- successor(X3,Z3), lessthan(Z3,Y3))
	      ,(lessthan(X1,Y1) :- successor(X1,Y1))
	     ]
	,permutation(R, R_)
	,D = [(lessthan(X2,Y2) :- successor(X2,Z2), successor(Z2,Y2))].

test(example_2a4, [nondet]):-
	example('2a4',P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(lessthan(X3,Y3) :- successor(X3,Z3), lessthan(Z3,Y3))
	      ,(lessthan(X1,Y1) :- successor(X1,Y1))
	     ]
	,permutation(R, R_)
	,D = [(lessthan(X2,Y2) :- successor(X2,Z2), successor(Z2,Y2))].

test(example_2a5, [nondet]):-
	example('2a5',P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(lessthan(X3,Y3) :- successor(X3,Z3), lessthan(Z3,Y3))
	      ,(lessthan(X1,Y1) :- successor(X1,Y1))
	     ]
	,permutation(R, R_)
	,D = [(lessthan(X2,Y2) :- successor(X2,Z2), successor(Z2,Y2))].

test(example_2a6, [nondet]):-
	example('2a6',P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(lessthan(X3,Y3) :- successor(X3,Z3), lessthan(Z3,Y3))
	      ,(lessthan(X1,Y1) :- successor(X1,Y1))
	     ]
	,permutation(R, R_)
	,D = [(lessthan(X2,Y2) :- successor(X2,Z2), successor(Z2,Y2))].

test(example_2c, [nondet]):-
	example('2c',P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(lessthan(X1,Y1) :- successor(X1,Y1))
			,(lessthan(X1,Y1) :- successor(Y1,X1))
			,(lessthan(X3,Y3) :- successor(X3,Z3), lessthan(Z3,Y3))
			]
		    )
	,permutation(D, [(lessthan(U,V) :-
			 successor(U,W), successor(W,X), successor(X,V))
			,(lessthan(X2,Y2) :- successor(X2,Z2), successor(Z2,Y2))
			]
		    ).

test(example_3, []):-
	example(3,P)
	,program_reduction(P, R, D)
	,!
	,R = [(q(X1) :- p(X1))]
	,D = [].

test(example_4, [blocked('Needs definition of body goals')
		,nondet
		]):-
	example(4,P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(q(X1) :- p(X1))
			,(q(X2) :- a(X2))
			]
		    )
	,D = [].

test(example_4a, [nondet]):-
	example('4a',P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(q(X2) :- a(X2))
			,(q(X1) :- p(X1))]
		    )
	,D = [].

test(example_5a, []):-
	example('5a',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- a(X1, _Y1))]
	,D = [(p(X2) :- a(X2, _Y2))].

test(example_5b, []):-
	example('5b',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X2) :- a(c,X2), a(d,X2))]
	,D = [(p(X1) :- a(d,X1),a(c,X1))].

test(example_5c1, [nondet]):-
	example('5c1',P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(p(X2,_Y2,Z2) :- gt(X2, Z2))
			,(p(X1,Y1,_Z1) :- gt(X1, Y1))
			]
		    )
	,D = [(p(X3,Y3,Z3) :- gt(X3, Y3), gt(X3, Z3))].

test(example_5c2, [nondet]):-
	example('5c2',P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(p(X1,Y1,_Z1) :- gt(X1, Y1))
			,(p(X2,_Y2,Z2) :- gt(X2, Z2))
			]
		    )
	,D = [(p(X3,Y3,Z3) :- gt(X3, Y3), gt(X3, Z3))].

test(example_5d1, [
	 blocked('Needs definition of body goals')
     ]):-
	example('5d1',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- gt(X1, 1))]
	,D = [(p(X2) :- lte(1, X2))].

test(example_5d2, [
	 blocked('Needs definition of body goals')
     ]):-
	example('5d2',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- gt(X1, 1))]
	,D = [(p(X2) :- lte(1, X2))].

test(example_5e1, [
	 blocked('Needs definition of body goals')
     ]):-
	example('5e1',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- gte(X1, 1), lte(X1, 1))]
	,D = [(p(X2) :- eq(1, X2))].

test(example_5e2, [
	 blocked('Needs definition of body goals')
     ]):-
	example('5e2',P)
	,program_reduction(P, R, D)
	,!
	,R = [(p(X1) :- gte(X1, 1), lte(X1, 1))]
	,D = [(p(X2) :- eq(1, X2))].

test(example_6, [blocked('Needs definition of body goals')
		,nondet
		]):-
% A bit pointless, this one (the program is an older version of
% program_reduction/4; should update to the latest one).
	example(6,P)
	,program_reduction(P, R, D)
	,!
	,R_ = [(pltkn([], _, R1, R1, Hr1, Hr1):- cut)
	      ,(pltkn([C2|Cs2], H02, Acc_H02, Bind_H02, Acc_Hr2, Bind_Hr2):-
	       slct(C2, H02, H02_)
	       ,gnrlis(H02_, C2)
	       ,cut
	       ,pltkn(Cs2, H02_, Acc_H02, Bind_H02, [C2|Acc_Hr2], Bind_Hr2)
	       )
	      ,(pltkn([C3|Cs3], H03, Acc_H03, Bind_H03, Acc_Hr3, Bind_Hr3):-
	       pltkin(Cs3, H03, [C3|Acc_H03], Bind_H03, Acc_Hr3, Bind_Hr3)
	       )]
	,permutation(R, R_)
	,D = [].

test(example_7, [nondet]):-
	example(7,P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(append([H|T],L2,[H|L3])  :-  append(T,L2,L3))
			,(append([],L1,L1))
			]
		    )
	,D = [].


test(example_8, [nondet]):-
	example(8,P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(reverse([X1|Y1],Z1,W1) :- reverse(Y1,[X1|Z1],W1))
			,(reverse([],X2,X2))
			]
		    )
	,D = [].

test(example_9, [nondet]):-
	example(9,P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(list_member(X2,[_Y|R2]) :- list_member(X2,R2))
			,(list_member(X1,[X1|_R]))
			]
		    )
	,D = [].

test(example_10, [nondet]):-
	example(10,P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(takeout(X2,[F|R2],[F|S]) :- takeout(X2,R2,S))
			,(takeout(X1,[X1|R1],R1))
			]
		    )
	,D = [].

test(example_11, [nondet]):-
	example(11,P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(perm([X|Y],Z) :- perm(Y,W), takeout(X,Z,W))
			,(perm([],[]))]
		    )
	,D = [].

test(example_12, [blocked('Needs definition of body goals')
		 ,nondet
		 ]):-
	example(12,P)
	,program_reduction(P, R, D)
	,!
	,permutation(R, [(set_intersection([X1|Y1],M1,[X1|Z1]):-
			 list_member(X1,M1)
			 ,set_intersection(Y1,M1,Z1))
			,(set_intersection([X2|Y2],M2,Z2):-
			 negation
			 ,list_member(X2,M2)
			 ,set_intersection(Y2,M2,Z2))
			,(set_intersection([],_M3,[]))]
		    )
	,D = [].

:-end_tests(program_reduction).

% Test template; won't run outside start/end_test/1 directives.

test(example_none, [blocked(reasons)]):-
	example('none',P)
	,program_reduction(P, R, D)
	,!
	,R = []
	,D = [].
