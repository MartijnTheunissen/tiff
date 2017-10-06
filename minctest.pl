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
test(rule1) :-
    dc_i(varmap([(xAA, x, 4), (xBB, y, 4)]), context([(x, pointer_type(array_type(long))), (y, long)]), _, ins(oper+(4, xAA, xBB, 4)), Assignment),
    Assignment == assn(variable(x), oper+(variable(x), y * 1)).

% oper+ ri, rj * c --> x:= x oper+ (y * c'). 
% ri = short x
% rj = short y
% c = 2
% x := x oper+ (y * 2)
test(rule2) :-
    dc_i(varmap([(xAA, x, 2), (xBB, y, 2)]), context([(x, short), (y, short)]), _, ins(oper+(2, xAA, xBB, 2)), Assignment),
    Assignment == assn(variable(x), oper+(variable(x), y*2)).
    
% oper+ ri, c --> x:= x oper+ m. 
% ri = long x
% c = 8
% x := x oper+ 2
test(rule3) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(array_type(long)))]), _, ins(oper+(4, xAA, 8)), Assignment),
    Assignment == assn(variable(x), oper+(variable(x), 2)).

% oper* ri, c --> x := x oper* c
% ri = long x
% c = 8
% x := x oper* 8
test(rule4) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, long)]), _, ins(oper*(4, xAA, 8)), Assignment),
    Assignment == assn(variable(x), oper*(variable(x), 8)).

% oper* ri, rj --> x := x oper* y
% ri = short x,
% rj = short y,
test(rule5) :-
    dc_i(varmap([(xAA, x, 2), (xBB, y, 2)]), context([(x, short), (y, short)]), _, ins(oper*(2, xAA, xBB)), Assignment),
    Assignment = assn(variable(x), oper*(variable(x), variable(y))).

% mov ri, c --> x := c
% ri = short x
% c = 7
% --> x := 8
test(mov_const) :-
    dc_i(varmap([(xAA, x, 2)]), context([(x, short)]), _, ins(mov1(2, xAA, 8)), Assignment),
    Assignment == assn(variable(x), 8).

% mov4 ri, 0 --> x := 0
% ri = short * x
test(mov_zero) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(short))]), _, ins(mov1(4, xAA, 0)), Assignment),
    Assignment == assn(variable(x), ptr(0)).
    
% mov4 ri, rj --> x := y
% ri = long x,
% rj = long y.
test(movrr) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, long)]), _, ins(mov4(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), variable(y)).

% movW ri, [rj] --> x := *y
% ri = long x,
% rj = long* y.
test(movri1) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(long))]), _, ins(mov2(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), ptr(variable(y))).
    
% movW ri, [rj] --> x := y[0]
% ri = long x,
% rj = long[]* y.
test(movri2) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(array_type(long)))]), _, ins(mov2(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), arr(variable(y), long(0))).

% movW ri, [rj] --> x := y -> 0
% ri = long x,
% rj = struc strucA * y = {_: long, _:long}.
test(movri2) :-
    dc_i(varmap([(xAA, x, 4), (yAA, y, 4)]), context([(x, long), (y, pointer_type(struct_type(strucA)))]), strucmap([(strucA, [long, long])]), ins(mov2(4, xAA, yAA)), Assignment),
    Assignment == assn(variable(x), fld(variable(y), long(0))).

% alloc ri, 4 --> new X
% ri = long* x
test(alloc_rc1) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(long))]), _, ins(alloc1(xAA, 4)), Assignment),
    Assignment == assn(variable(x), new_compact(long)).

% alloc ri, 4 --> new X[]
% ri = long[]* x
test(alloc_rc3) :-
    dc_i(varmap([(xAA, x, 4)]), context([(x, pointer_type(array_type(long)))]), _, ins(alloc1(xAA, 4)), Assignment),
    Assignment == assn(variable(x), new_arr(long, 1)).

% alloc ri, rj, 4 --> new X [y * m]
% ri = long[]* x,
% rj = long
test(alloc_rr) :-
    dc_i(varmap([(xAA, x, 4), (xBB, y, 4)]), context([(x, pointer_type(array_type(long))), (y, long)]), _, ins(alloc2(xAA, xBB, 4)), Assignment),
    Assignment == assn(variable(x), new_arr(long, y * 1)).

test(ifblock) :-
    dc_b(labelmap([(a, l)]), varmap([(xAA, x, 4)]), context([(x, long)]), _, seq(if(4, xAA, a), ret), Statement),
    Statement = seq(if(x, l), return).
    
% mov_2 ri, c ; ret --> x := c ; return
test(seqinstr) :-
    dc_b(_, varmap([(xAA, x, 2)]), context([(x, short)]), _, seq(ins(mov1(2, xAA, 8)), ret), Statement),
    Statement = seq(assn(variable(x), 8), return).

:- end_tests(minc).

