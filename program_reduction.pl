:-module(program_reduction, [example_report/1
			    ,reduction_report/3
			    ,reduction_report/1
			    ,program_reduction/3
			    ]).

:-use_module(examples).

/** <module> Implementation of Gordon Plotkin's program reduction algorithm.

Gordon Plotkin gives the following algorithm for reduction of a set of
(arbitrary) clauses:

==
Given a set of clauses H, find a reduction H' of H:
1) Set H' to H
2) Stop if every clause in H' is marked
3) Choose an unmarked clause, C, in H'
4) If H' \{C} =< {C}, change H' to H' \ {C}
   Otherwise, mark C
5) Repeat from (2)
==

The algorithm is described in Plotkin's doctoral thesis, "Automatic
methods of inductive inference" (thesis, The University of Edinburgh,
1972). It is listed as theorem 3.3.1.2 (on page 76 of the thesis).

This module implements Plotkin's algorithm restricted to Horn clauses.

See program_reduction/3 and subsumes/2 for implementation details.

Running tests
-------------

Tests accompanying this module are given in program_reduction.plt. Tests
can be loaded with:

==
?- ['program_reduction.plt'].
==

Once loaded, tests can be run with:

==
?- run_tests.
==

Consulting the file load.pl at the root of this directory will also load
the test suite.

*/


%!	program_module(?Name) is semidet.
%
%	Name of the module where program clauses are asserted.
%
program_module(program).


%!	example_report(+Example) is det.
%
%	Report the reduction of an Example program.
%
%	Example is the name of an example program in module examples.pl.
%
%	Example of use:
%	==
%	?- example_report('0b1').
%	Program clauses:
%	----------------
%	m(A,B,C):-m(D,B,C)
%	m(A,B,C):-m(D,C,B)
%
%	Program reduction:
%	------------------
%	m(A,B,C):-m(D,C,B)
%
%	Redundant clauses:
%	------------------
%	m(A,B,C):-m(D,B,C)
%
%	true.
%	==
%
example_report(E):-
	example(E,Ps)
	,reduction_report(Ps).



%!	reduction_report(+Program) is det.
%
%       Report on redundant clauses in Program.
%
%       Program is a set of clauses.
%
%       Top-level interface to program_reduction/3.
%
%       Example of use:
%
%       ==
%       ?- example('0b1', _Cs), reduction_report(_Cs).
%       Program clauses:
%       ----------------
%       m(A,B,C):-m(D,B,C)
%       m(A,B,C):-m(D,C,B)
%
%       Program reduction:
%       ------------------
%       m(A,B,C):-m(D,C,B)
%
%       Redundant clauses:
%       ------------------
%       m(A,B,C):-m(D,B,C)
%
%       true.
%       ==
%
reduction_report(Ps):-
	program_reduction(Ps,Rs,Ds)
	,reduction_report(Ps,Rs,Ds).



%!	reduction_report(+Program,+Reduction,+Redundant) is det.
%
%	Report on the Reduction of a Program.
%
%	Program is a list of clauses. Reduction is the program's
%	reduction and Redundant its redundant clauses.
%
%	This predicate is only used to print out a reduction report, not
%	to perform the actual reduction. Use program_reduction/3 for
%	that.
%
%	Example of use:
%	==
%	?- example('0b1',_Ps),program_reduction(_Ps,_Rs,_Ds),reduction_report(_Ps,_Rs,_Ds).
%	Program clauses:
%	----------------
%	m(A,B,C):-m(D,B,C)
%	m(A,B,C):-m(D,C,B)
%
%	Program reduction:
%	------------------
%	m(A,B,C):-m(D,C,B)
%
%	Redundant clauses:
%	------------------
%	m(A,B,C):-m(D,B,C)
%
%	true.
%	==
%
reduction_report(Ps,Rs,Ds):-
	writeln('Program clauses:')
	,writeln('----------------')
	,list_clauses(Ps)
	,nl
	,writeln('Program reduction:')
	,writeln('------------------')
        ,list_clauses(Rs)
	,nl
	,writeln('Redundant clauses:')
	,writeln('------------------')
        ,list_clauses(Ds)
	,nl.



%!	program_reduction(+Program,-Reduction,-Redundant) is det.
%
%	Calculates a Program's Reduction by Plotkin's algorithm.
%
%	This predicate is most easily used via the reduction_report/1
%	and reduction_report/3 interfaces. See those predicates for
%	example calls.
%
program_reduction(Ps, Rs, Ds):-
	program_module(M)
	,S = (assert_program(M,Ps)
	     %,table_program(M,Ps)
	     )
	,G = (program_reduction(M,Ps,[],Rs,[],Ds)
	     %,reduction_report(Ps,Rs,Ds)
	     )
	,C = (
	     %untable_program(M,Ps),
	     retract_program(M,Ps)
	 )
	,setup_call_cleanup(S,G,C).

%!	program_reduction(+Module,+Program,+Reduction,+Reduction,+Redundant,+Redundant)
%	is det.
%
%	Business end of program_reduction/3.
%
%	Implements Plotkin's program reduction algorithm:
%	Given a set of clauses H, find a reduction H' of H:
%	1) Set H' to H
%	2) Stop if every clause in H' is marked
%	3) Choose an unmarked clause, C, in H'
%	4a) If H' \{C} =< {C}, change H' to H' \ {C}
%	4b) Otherwise, mark C
%	5) Repeat from (2)
%
%	The '=<' relation is the subsumption relation. In the
%	implementation subsumption is tested by the predicate
%	subsumed/2.
%
%	The implementation doesn't "mark" clauses but instead goes
%	through a list of clauses and tests each in turn. In each
%	iteration of Plotkin's algorithm a clause can either be marked,
%	or deleted, so there's no chance that the same clause can be
%	chosen twice.
%
%	The implementation proceeds as follows:
%	a) A clause, C, is selected
%	b) C is retracted from the database.
%	c) C is passed to subsumed/2.
%	d) If subsumed/2 is true, C is added to the
%	redundancy accumulator.
%	e) Otherwise, C is re-asserted to the database.
%	f) When there are no more clauses, the list of clauses remaining
%	in the program and the list of redundant clauses are bound to
%	the outputs.
%
program_reduction(_M, [], Rs, Rs, Ds, Ds):-
	!.
program_reduction(M, [C|Cs], Rs_acc, Rs_bind, Ds_acc, Ds_bind):-
	once(retract(M:C))
	,subsumed(M, C)
	,!
	,program_reduction(M, Cs, Rs_acc, Rs_bind, [C|Ds_acc], Ds_bind).
program_reduction(M, [C|Cs], Rs_acc, Rs_bind, Ds_acc, Ds_bind):-
% C is not redundant: we add it back to the program (in the dynamic db).
	assert(M:C)
	,program_reduction(M, Cs, [C|Rs_acc], Rs_bind, Ds_acc, Ds_bind).



%!	subsumed(+Module, +Clause) is det.
%
%	True when Clause is subsumed by the program in Module.
%
%	Module is the name of the module specified in program_module/1.
%	The clauses of a program originally including Clause have been
%	asserted to that module by program_reduction/3. subsumed/2 is
%	true when Clause is entailed by the clauses in that program.
%
%	Entailment is determined as follows: first, Clause is skolemised
%	(by numbervars/1). Then, its skolemised body literals are
%	asserted to Module. Finally, its head literal is resolved with
%	the clauses in Module. If resolution succeeds, we decide that
%	Clause is entailed by the clauses in Module.
%
%	Historical notes
%	----------------
%
%	This method to test entailment was suggested by Stephen
%	Muggleton and follows the implementation of Plotkin's algorithm
%	in Progol (though I'm not sure of the version this was
%	originally implemented in). There has been some debate in ILP
%	circles regarding whether this method means that the
%	implementation is not "really" Plotkin's algorithm, or not.
%	Andrew Cropper has suggested the implementation should really be
%	called "derivation reduction" (rather than Plotkin's reduction).
%	It appears to work so I'm not very concerned about the naming.
%
subsumed(M,H:-B):-
% Clause is a non-unit clause.
	!
	,copy_term((H:-B),(H_:-B_))
	,numbervars((H_:-B_))
	,S = once(assert_goals(M,B_))
	,G = call(M:H_)
	,Cl = retract_goals(M, B)
	,setup_call_cleanup(S,G,Cl).
subsumed(M,A):-
% Clause is an atom.
	copy_term(A,A_)
	,numbervars(A_)
	,call(M:A_).



%================================================================================
% Tabling and untabling
%================================================================================

/* Predicates in this section are used to table predicates in a program so
that they can be evaluated without entering an infinite recursion.
Unfortunately, this causes some tests that previously passed, to fail.
*/

%!	table_program(+Module,+Program) is det.
%
%	Table predicates in a Program defined in a Module.
%
table_program(M,Ps):-
	forall(member(C,Ps)
	      ,table_clause(M,C)
	      ).

%!	table_clause(+Module,+Clause) is det.
%
%	Table the predicate of the head literal of Clause.
%
table_clause(M,H:-_B):-
	functor(H,F,A)
	%,writeln(tabling:F/A)
	,!
	,table(M:F/A as incremental).
table_clause(M,C):-
	functor(C,F,A)
	%,writeln(tabling:F/A)
	,table(M:F/A).



%!	untable_program(+Module,+Program) is det.
%
%	Untable predicates in a Program defined in a Module.
%
untable_program(M,Ps):-
	forall(member(C,Ps)
	      ,untable_clause(M,C)
	      ).

%!	untable_clause(+Module,+Clause) is det.
%
%	Untable the predicate of the head literal of Clause.
%
untable_clause(M,H:-_B):-
	functor(H,F,A)
	%,writeln(untabling:F/A)
	,!
	,untable(M:F/A).
untable_clause(M,C):-
	functor(C,F,A)
	%,writeln(untabling:F/A)
	,untable(M:F/A).




%================================================================================
% Database manipulation. Sigh.
%================================================================================

%!	assert_program(+Module, +Program) is det.
%
%	Assert a set of clauses into a Module.
%
assert_program(M,P):-
	forall(member(C, P)
	      ,assert(M:C)
	      ).



%!	retract_program(+Module,+Program) is det.
%
%	Retract	all clauses of a Program from a Module.
%
retract_program(M,P):-
	forall(member(C, P)
	      ,(( retract(M:C)
		; true
		)
	       )
	      ).



%!	assert_goals(+Module, +Goals) is det.
%
%	Add a set of Goals to a Module.
%
assert_goals(M,(Atom,Atoms)) :-
	(   built_in_or_library_predicate(M:Atom)
	->  true
	;   asserta(M:Atom)
	),
	assert_goals(M,Atoms).
assert_goals(M,Atom):-
	(   built_in_or_library_predicate(M:Atom)
	->  true
	;   asserta(M:Atom)
	).



%!	retract_goals(+Module, +Literals) is det.
%
%	Retract each of a clause's Literals from Module.
%
retract_goals(M,(Atom,Atoms)) :-
	(   built_in_or_library_predicate(M:Atom)
	->  true
	;   retract(M:Atom)
	),
	retract_goals(M,Atoms).
retract_goals(M,Atom):-
	(   built_in_or_library_predicate(M:Atom)
	->  true
	;   retract(M:Atom)
	).


%!	built_in_or_library_predicate(+Predicate) is det.
%
%	True for a built-in or autoloaded Predicate.
%
%	Thin wrapper around predicate_property/2. Used to decide what
%	programs to collect with closure/3 and what programs to
%	encapsulate.
%
built_in_or_library_predicate(H):-
	predicate_property(H, built_in)
	,!.
built_in_or_library_predicate(H):-
	predicate_property(H, autoload(_)).




%================================================================================
% Progam listing
%================================================================================

%!	list_clauses(+Clauses) is det.
%
%	Print out a list of Clauses.
%
%	Variables in Clauses are numbered with numbervar, for
%	legibility.
%
list_clauses(Cs):-
	forall(member(C, Cs)
	      ,(duplicate_term(C,C_)
	       ,numbervars((C_),0,_)
	       ,writeln(C_))
	      ).

