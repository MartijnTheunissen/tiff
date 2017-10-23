%prolog
% use run_tests.

:- consult(minc).
:- use_module(library(plunit)).

:- begin_tests(minc).

% oper+ ri, ry * c --> x := x oper+ (y * m).
% ri = long[]* x,
% ry = long y,
% c = 4
%  4 byte per long -> m = 1
test(rule1, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (xBB, y, 4)]), context([(x, pointer_type(array_type(long))), (y, long)]), _, ins(oper+(4, xAA, xBB, 4)), Assignment),
    Assignment == assn(variable(x), oper+(variable(x), y * 1)).

% oper+ ri, rj * c --> x:= x oper+ (y * c'). 
% ri = short x
% rj = short y
% c = 2
% x := x oper+ (y * 2)
test(rule2, [nondet]) :-
    dc_i(varmap([(xAA, x, 2), (xBB, y, 2)]), context([(x, short), (y, short)]), _, ins(oper+(2, xAA, xBB, 2)), Assignment),
    Assignment == assn(variable(x), oper+(variable(x), y*2)).
    
% oper+ ri, c --> x:= x oper+ m. 
% ri = long x
% c = 8
% x := x oper+ 2
test(rule3, [nondet]) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(array_type(long)))]), _, ins(oper+(4, xAA, 8)), Assignment),
    Assignment == assn(variable(x), oper+(variable(x), 2)).

% oper* ri, c --> x := x oper* c
% ri = long x
% c = 8
% x := x oper* 8
test(rule4, [nondet]) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, long)]), _, ins(oper*(4, xAA, 8)), Assignment),
    Assignment == assn(variable(x), oper*(variable(x), 8)).

% oper* ri, rj --> x := x oper* y
% ri = short x,
% rj = short y,
test(rule5, [nondet]) :-
    dc_i(varmap([(xAA, x, 2), (xBB, y, 2)]), context([(x, short), (y, short)]), _, ins(oper*(2, xAA, xBB)), Assignment),
    Assignment = assn(variable(x), oper*(variable(x), variable(y))).

% mov ri, c --> x := c
% ri = short x
% c = 7
% --> x := 8
test(mov_const, [nondet]) :-
    dc_i(varmap([(xAA, x, 2)]), context([(x, short)]), _, ins(mov1(2, xAA, 8)), Assignment),
    Assignment == assn(variable(x), 8).

% mov4 ri, 0 --> x := 0
% ri = short * x
test(mov_zero, [nondet]) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(short))]), _, ins(mov1(4, xAA, 0)), Assignment),
    Assignment == assn(variable(x), ptr(0)).
    
% mov4 ri, rj --> x := y
% ri = long x,
% rj = long y.
test(movrr, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, long)]), _, ins(mov4(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), variable(y)).

% movW ri, [rj] --> x := *y
% ri = long x,
% rj = long* y.
test(movri1, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(long))]), _, ins(mov2(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), ptr(variable(y))).
    
% movW ri, [rj] --> x := y[0]
% ri = long x,
% rj = long[]* y.
test(movri2, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(array_type(long)))]), _, ins(mov2(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), arr(variable(y), long(0))).

% movW ri, [rj] --> x := y -> 0
% ri = long x,
% rj = struc strucA * y = {_: long, _:long}.
test(movri3, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(struct_type(strucA)))]), strucmap([(strucA, [long, long])]), ins(mov2(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), fld(variable(y), long(0))).

% movW [ri], rj --> *x := y
% ri = long* x,
% rj = long y.
test(movir1, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, pointer_type(long)), (y, long)]), _, ins(mov5(4, xAA, yAA)), Assignment),
    Assignment == assn(ptr(variable(x)), variable(y)).
    
% movW [ri], rj --> x[0] := y
% ri = long[]* x,
% rj = long y.
test(movir2, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, pointer_type(array_type(long))), (y, long)]), _, ins(mov5(4, xAA, yAA)), Assignment),
    Assignment == assn(arr(variable(x), long(0)), variable(y)).

% movW [ri], rj --> x -> 0 := y
% ri = struc strucA * y = {_: long, _:long}.
% rj = long x,
test(movir3, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, pointer_type(struct_type(strucA))), (y, long)]), strucmap([(strucA, [long, long])]), ins(mov5(4, xAA, yAA)), Assignment),
    Assignment == assn(fld(variable(x), long(0)), variable(y)).

%movW ri, [rj + c] --> x := y[m]
test(movric1, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(array_type(long)))]), _, ins(mov3(4, xAA, yAA, 0)), Assignment),
    Assignment == assn(variable(x), arr(variable(y), long(0))).

%movW ri, [rj + c] --> x := y -> m
test(movric2, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(struct_type(strucA)))]), strucmap([(strucA, [long, long, short, long])]), ins(mov3(4, xAA, yAA, 4)), Assignment),
    Assignment == assn(variable(x), fld(variable(y), long(1))).

%movW [ri + c], rj --> x[m] := y
test(movirc1, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, pointer_type(array_type(long))), (y, long)]), _, ins(mov6(4, xAA, 0, yAA)), Assignment),
    Assignment == assn(arr(variable(x), short(0)), variable(y)).

%movW [ri + c], rj --> x -> m := y
test(movirc2, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, pointer_type(struct_type(strucA))), (y, long)]), strucmap([(strucA, [long, long, short, long])]), ins(mov6(4, xAA, 4, yAA)), Assignment),
    Assignment == assn(fld(variable(x), long(1)), variable(y)).

% alloc ri, 4 --> new X
% ri = long* x
test(alloc_rc1, [nondet]) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(long))]), _, ins(alloc1(xAA, 4)), Assignment),
    Assignment == assn(variable(x), new_compact(long)).

% alloc ri, 4 --> new X
% ri = long* x
test(alloc_rc2, [nondet]) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(struct_type(strucA)))]), strucmap([(strucA, [long, long, short, long])]), ins(alloc1(xAA, 14)), Assignment),
    Assignment == assn(variable(x), new_struct(strucA)).

% alloc ri, 4 --> new X[]
% ri = long[]* x
test(alloc_rc3, [nondet]) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(array_type(long)))]), _, ins(alloc1(xAA, 4)), Assignment),
    Assignment == assn(variable(x), new_arr(long, 1)).

% alloc ri, rj, 4 --> new X [y * m]
% ri = long[]* x,
% rj = long
test(alloc_rr, [nondet]) :-
    dc_i(varmap([(xAA, x, 4), (xBB, y, 4)]), context([(x, pointer_type(array_type(long))), (y, long)]), _, ins(alloc2(xAA, xBB, 4)), Assignment),
    Assignment == assn(variable(x), new_arr(long, y * 1)).

test(ifblock, [nondet]) :-
    dc_b(labelmap([(a, l)]), varmap([(xAA, x, 4)]), context([(x, long)]), _, seq(if(4, xAA, a), ret), Statement),
    Statement = seq(if(x, l), return).
    
% mov_2 ri, c ; ret --> x := c ; return
test(seqinstr, [nondet]) :-
    dc_b(_, varmap([(xAA, x, 2)]), context([(x, short)]), _, seq(ins(mov1(2, xAA, 8)), ret), Statement),
    Statement = seq(assn(variable(x), 8), return).

:- end_tests(minc).

