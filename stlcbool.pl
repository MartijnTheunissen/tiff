%prolog
term(tt).
term(ff).
term(if(T1, T2, T3)) :-
    term(T1),
    term(T2),
    term(T3).
term(variable(X)) :-
    atom(X).
term(app(Term1, Term2)) :-
    term(Term1),
    term(Term2).
term(abstr(X, Type, Term)) :- 
    X = variable(X2),
    atom(X2),
    type(Type),
    term(Term).

value(tt).
value(ff).
value(lam(X, Type, Term)) :-
    X = variable(X2),
    atom(X2),
    type(Type),
    term(Term).

type(tBool).
type(tFun(T1, T2)) :-
    type(T1),
    type(T2).

context([]).
context([(X,T)]) :-
    variable(X),
    type(T).
context([(X,T)|Tail]) :-
    variable(X),
    type(T),
    context(Tail).

welltyped(_, tt, tBool).
welltyped(_, ff, tBool).
welltyped(C, if(T1, T2, T3), T) :-
    welltyped(C, T1, tBool),
    welltyped(C, T2, T),
    welltyped(C, T3, T).
welltyped(C, variable(X), T) :-
    C = context(Clist),
    member((X, T), Clist).
welltyped(C, app(Term1, Term2), T12) :-
    welltyped(C, Term1, tFun(T11, T12)),
    welltyped(C, Term2, T11).
welltyped(C, abstr(variable(X), T1, Term), tFun(T1, T2)) :-
    C = context(Clist),
    append(Clist, [(X, T1)], C2),
    welltyped(context(C2), Term, T2).
