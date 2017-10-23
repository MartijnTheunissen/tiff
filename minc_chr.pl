%prolog

:- use_module(library(aggregate)).
:- use_module(library(chr)).

:- chr_constraint dc_i/5.
:- chr_constraint bound/3.
:- chr_constraint done/0.

%MinC types
primitive_type(short).
primitive_type(long).

compact_type(T) :-
    primitive_type(T).
compact_type(pointer_type(array_type(T))) :-
    primitive_type(T).
compact_type(pointer_type(struct_type(T))) :-
    atom(T).
compact_type(pointer_type(T)) :-
    compact_type(T).

compact_type(T, _) :- 
    primitive_type(T).
compact_type(pointer_type(array_type(T)), _) :-
    primitive_type(T).
compact_type(pointer_type(struct_type(T)), _) :-
    atom(T).
compact_type(pointer_type(T), _) :-
    primitive_type(T).
compact_type(pointer_type(T), N) :- 
    N2 is N - 1,
    N2 >= 0,
    compact_type(T, N2).

general_type(T) :-
    compact_type(T).
general_type(T) :-
    array_type(T).
general_type(T) :-
    struct_type(T).


type(T) :-
    primitive_type(T).
type(T) :-
    compact_type(T).
type(T) :-
    general_type(T).

label(L) :-
    atom(L).

%MinC statements
statement(return).
statement(goto(Label)) :-
    label(Label).
statement(seq(if(Expr, Label), Statement)) :-
    expression(Expr),
    label(Label), 
    statement(Statement).
statement(seq(assn(Lval, Expr), Statement)) :-
    lvalue(Lval),
    expression(Expr),
    statement(Statement).

%MinC lvalues
lvalue(variable(X)) :-
    atom(X).
lvalue(ptr(X)) :-
    atom(X).
lvalue(fld(X, C)) :- 
    atom(X),
    integer(C).
lvalue(arr(X, E)) :-
    atom(X),
    atom(E).

%MinC expressions
expression(L) :-
    lvalue(L).
expression(long(L)) :- 
    integer(L).
expression(short(S)) :- 
    integer(S).
expression(amp(X)) :-
    X = variable(Y),
    atom(Y).
expression(func(Name, Args)) :-
    atom(Name),
    is_list(Args).
expression(new_compact(Compact)) :-
    compact_type(Compact).
expression(new_arr(Expr, Arr)) :-
    array_type(Arr),
    expression(Expr).
expression(new_struct(N)) :-
    struct_type(N).
expresssion(oper+(E1, E2)) :-
    expression(E1),
    expression(E2).
expresssion(oper*(E1, E2)) :-
    expression(E1),
    expression(E2).

%Context
context([]).
context([(X, T)]) :-
    variable(X),
    type(T).
context([(X, T) |Tail]) :-
    variable(X),
    type(T),
    context(Tail).

sizeof(short, 2).
sizeof(long, 4).
sizeof(pointer_type(_), 4).

funcdefs([]).
funcdefs([(Name, Def)]) :-
    atom(Name),
    Def = func(_, _, _, _, _).
funcdefs([(Name, Def) | Tail]) :-
    atom(Name),
    Def = func(_, _, _, _, _),
    funcdefs(Tail).

%Struc map
strucmap([]).
strucmap([(Name, FieldTypeVec)]) :-
    atom(Name),
    is_list(FieldTypeVec).
strucmap([(Name, FieldTypeVec)] |Tail) :-
    atom(Name),
    is_list(FieldTypeVec),
    strucmap(Tail).

% wt_d(StrucMap, Function).

wt_d(strucmap(S), func(Args, Locals, Label, LS, Index)) :-
   append(Args, Locals, ContextList),
   member((Label, _), LS),
   nth0(Index, Locals, _),
   foreach(member((_, Statement), LS), wt_s(context(ContextList), strucMap(S), Statement)).


%wt_sub(StrucMap, Type, Type)

wt_sub(_, O, O). %sub-refl

wt_sub(StrucMap, pointer_type(array_type(O1)), pointer_type(array_type(O2))) :- %sub-arr
    wt_sub(StrucMap, O1, O2).

wt_sub(StrucMap, pointer_type(O1), pointer_type(O2)) :- %sub-ptr
    wt_sub(StrucMap, O1, O2).

wt_sub(_, pointer_type(array_type(O)), pointer_type(O)). % sub-elm

wt_sub(strucmap(S), pointer_type(struct_type(Name)), pointer_type(O0)) :- %sub-fld
    member((Name, FieldTypeVec), S),
    nth0(0, FieldTypeVec, O0).

% wt_sub(StrucMap, O1, O3) :- %sub-trans 
%     compact_type(O2),
%     wt_sub(StrucMap, O1, O2),
%     wt_sub(StrucMap, O2, O3).


%wt_s(Context, StrucMap, Sentence)

wt_s(_, _, return). %t-ret

wt_s(_, _, goto(L)) :- label(L). %t-goto

wt_s(Context, StrucMap, if(Expr, _, Statmt)) :- %t-if
    wt_s(Context, StrucMap, Statmt),
    wt_le(Context, StrucMap, Expr, _).

wt_s(Context, StrucMap, assn(Lval, Expr, Statmt)) :- %t-assn
    wt_le(Context, StrucMap, Lval, T1),
    wt_sub(StrucMap, T2, T1),
    wt_le(Context, StrucMap, Expr, T2),
    wt_s(Context, StrucMap, Statmt).

%wt_le(Context, StrucMap, Lvalue/expression, Type)

wt_le(context(Clist), _, variable(X), T) :- %t-var
   member((X, T), Clist).

wt_le(Context, StrucMap, ptr(X), T) :- % t-ptr
    wt_le(Context, StrucMap, X, pointer_type(T)).

wt_le(Context, StrucMap, arr(X, Expr), O) :- %t-arr
    wt_le(Context, StrucMap, Expr, T),
    primitive_type(T),
    wt_le(Context, StrucMap, X, pointer_type(array_type(O))),
    compact_type(O).

wt_le(Context, struc_map(S), fld(Expr, Index), Oi) :- %t-fld
    wt_le(Context, struc_map(S), Expr, pointer_type(struct_type(Name))),
    member((Name, FieldTypeVec), S),
    nth0(Index, FieldTypeVec, Oi).

wt_le(Context, StrucMap, amp(Y), pointer_type(T)) :- %t-amp
    wt_le(Context, StrucMap, Y, T).

wt_le(_, _, long(_), long). %t-l
wt_le(_, _, short(_), short). %t-s
wt_le(_, _, ptr(0), pointer_type(_)). %t-null
wt_le(_, _, new_compact(O), pointer_type(O)). %t-new
wt_le(_, _, new_struct(_), pointer_type(struct_type(_))). %t-str

wt_le(Context, StrucMap, new_arr(E, T), pointer_type(array_type(T))) :- %t-arr
    wt_le(Context, StrucMap, E, T),
    primitive_type(T).

wt_le(Context, StrucMap, oper*(E1, E2), T) :- %t-oper*
    wt_le(Context, StrucMap, E1, T),
    wt_le(Context, StrucMap, E2, T),
    primitive_type(T).

wt_le(Context, StrucMap, oper+(E1, E2), pointer_type(array_type(O))) :- %t-ptr-oper+
    wt_le(Context, StrucMap, E1, pointer_type(array_type(O))),
    compact_type(O),
    wt_le(Context, StrucMap, E2, T),
    primitive_type(T).

wt_le(Context, StrucMap, oper+(E1, E2), pointer_type(array_type(O))) :- %t-oper+-ptr
    wt_le(Context, StrucMap, E1, T),
    primitive_type(T),
    wt_le(Context, StrucMap, E2, pointer_type(array_type(O))),
    compact_type(O).

wt_le(Context, StrucMap, func(Name, Args), Oj) :-
    member((Name, func(Locals, Args, _, _, J)), funcdefs),
    foreach(member((E, O), Args), wt_le(Context, StrucMap, E, O)),
    nth0(J, Args, (_, Oj)),
    nth0(J, Locals, (_, O2)),
    wt_sub(O2, Oj).



% width defenition
width(1). 
width(2).
width(4).

ins(mov1(W, R, C)) :- % MinX instructions
    width(W),
    atom(R),
    number(C).
ins(mov2(W, Ri, IndRj)) :-
    width(W),
    atom(Ri),
    atom(IndRj).
ins(mov3(W, Ri, IndRj, C)) :-
    width(W),
    atom(Ri),
    atom(IndRj),
    number(C).
ins(mov4(W, Ri, Rj)) :-
    width(W),
    atom(Ri),
    atom(Rj).
ins(mov5(W, IndRi, Rj)) :-
    width(W),
    atom(IndRi),
    atom(Rj).
ins(mov6(W, IndRi, C, Rj)) :-
    width(W),
    atom(IndRi),
    number(C),
    atom(Rj).
ins(eq(W, Ri, Rj, Rk)) :-
    width(W),
    atom(Ri),
    atom(Rj),
    atom(Rk).
ins(oper+(W, Ri, Rj, C)) :-
    width(W),
    atom(Ri),
    atom(Rj),
    number(C).
ins(oper+(W, Ri, C)) :- % Not in instruction list, but needed for tr-oper+-rc rule page9
    width(W),
    atom(Ri),
    number(C).
ins(oper*(W, Ri, Rj)) :-
    width(W),
    atom(Ri),
    atom(Rj).
ins(oper*(W, Ri, C)) :-
    width(W),
    atom(Ri),
    number(C).
ins(alloc1(Ri, C)) :-
    atom(Ri),
    number(C).
ins(alloc2(Ri, Rj, C)) :-
    atom(Ri),
    atom(Rj),
    number(C).
ins(icall(Ru, A, _)) :- % call(Ru, Ra, [Rv])
    atom(Ru),
    atom(A).

block(seq(I, B)) :- % blocks
    ins(I),
    block(B).
block(if(W, _, _, B)) :-
    width(W),
    block(B).
block(goto(_)).
block(ret).

fdef(Rargs, Rret, Rlocs, ABMap, A0) :-
    is_list(Rargs),
    atom(Rret),
    is_list(Rlocs),
    is_list(ABMap),
    atom(A0).



%varmap
varmap([]).
varmap([(R, V, W)]) :-
    width(W),
    atom(R), % MinX Register
    atom(V). % MinC Variable
varmap([(R, V, W) |Tail]) :-
    width(W),
    atom(R),
    atom(V),
    varmap(Tail).

%labelmap
labelmap([]).
labelmap([(XL, CL)]) :-
    atom(XL), % MinX Label
    atom(CL). % MinC Label
labelmap([(XL, CL) |Tail]) :-
    atom(XL),
    atom(CL),
    varmap(Tail).

sizeofall([], 0).
sizeofall([X | Tail], C) :-
    sizeof(X, C2),
    sizeofall(Tail, C3),
    C is C2 + C3.

sizeof_to_m([_ | _], 0, 0).
sizeof_to_m([X | _], 1, C) :-
    sizeof(X, C).
sizeof_to_m([X | Tail], M, C) :-
    sizeof(X, C2),
    C3 is C - C2,
    C3 >= 0,
    sizeof_to_m(Tail, M2, C3),
    M is M2 + 1.


tag(short, S, T) :-
    T = short(S).
tag(long, L, T) :-
    T = long(L).

%dc_i(VarMap, TypeEnv, StructDefs, Instruction, assign(L, E)).

% tr-oper+-r*1
bound(context(Context), X, pointer_type(array_type(O))) \
dc_i(varmap(VM), context(Context), StructDefs, ins(oper+(4, Ri, Rj, C)), Assn) <=> member((Ri, X, 4), VM), member((Rj, Y, 4), VM) |
    member((X, pointer_type(array_type(O))), Context),
    compact_type(O),
    member((Y, long), Context),
    sizeof(O, Size),
    tag(long, M, TaggedVal),
    wt_le(context(Context), StructDefs, TaggedVal, long),
    number(C),
    M is C / Size,
    Assn = oper+(variable(X), Y * M).

bound(context(Context), X, pointer_type(array_type(O))) \
dc_i(varmap(VM), context(Context), StructDefs, ins(oper+(4, Ri, Rj, C)), Assn) <=> member((Ri, X, 4), VM), member((Rj, Y, 4), VM) |
    member((X, pointer_type(array_type(O))), Context),
    compact_type(O),
    member((Y, long), Context),
    sizeof(O, Size),
    tag(long, M, TaggedVal),
    wt_le(context(Context), StructDefs, TaggedVal, long),
    number(C),
    M is C / Size,
    Assn = assn(variable(X), oper+(variable(X), Y * M)).

% tr-oper+-r*2
bound(context(Context), X, T), 
bound(context(Context), Y, T) \
dc_i(varmap(VM), context(Context), StructDefs, ins(oper+(W, Ri, Rj, C)), Assn) <=> member((Ri, X, W), VM), member((Rj, Y, W), VM), primitive_type(T) |
    member((X, T), Context),
    member((Y, T), Context),
    tag(T, C, TaggedC),
    wt_le(context(Context), StructDefs, TaggedC, T),
    number(C),
    Res = Y * C,
    Assn = assn(variable(X), oper+(variable(X), Res)).

% tr-oper+-rc
bound(context(Context), X, pointer_type(array_type(O))) \
dc_i(varmap(VM), context(Context), StructDefs, ins(oper+(4, Ri, C)), Assn) <=> member((Ri, X, 4), VM) |
    member((X, pointer_type(array_type(O))), Context),
    compact_type(O),
    primitive_type(T),
    sizeof(O, Size),
    number(C),
    M is C / Size,
    tag(T, M, TaggedVal),
    wt_le(context(Context), StructDefs, TaggedVal, T),
    Assn = assn(variable(X), oper+(variable(X), M)).

% tr-oper*-rc
bound(context(Context), X, T) \
dc_i(varmap(VM), context(Context), StructDefs, ins(oper*(W, Ri, C)), Assn) <=> member((Ri, X, W), VM), primitive_type(T) |
    member((X, T), Context),
    sizeof(T, W),
    number(C),
    tag(T, C, TaggedC),
    wt_le(context(Context), StructDefs, TaggedC, T),
    Assn = assn(variable(X), oper*(variable(X), C)).

% tr-oper*-rr
bound(context(Context), X, T), 
bound(context(Context), Y, T) \ 
dc_i(varmap(VM), context(Context), _, ins(oper*(W, Ri, Rj)), Assn) <=> member((Ri, X, W), VM), member((Rj, Y, W), VM), primitive_type(T) |
    primitive_type(T),
    sizeof(T, W),
    Assn = assn(variable(X), oper*(variable(X), variable(Y))).

% tr-mov-r0
bound(context(Context), X, pointer_type(O)) \
dc_i(varmap(VM), context(Context), _, ins(mov1(4, Ri, 0)), Assn) <=> member((Ri, X, 4), VM) |
    member((X, pointer_type(O)), Context),
    Assn = assn(variable(X), ptr(0)).

% tr-mov-rc
bound(context(Context), X, T) \ 
dc_i(varmap(VM), context(Context), StructDefs, ins(mov1(W, Ri, C)), Assn) <=> member((Ri, X, W), VM), primitive_type(T) |
    member((X, T), Context),
    sizeof(T, W),
    number(C),
    tag(T, C, TaggedC),
    wt_le(context(Context), StructDefs, TaggedC, T),
    Assn = assn(variable(X), C).

% tr-mov-rr
bound(context(Context), X, O1), 
bound(context(Context), Y, O2) \
dc_i(varmap(VM), context(Context), StrucMap, ins(mov4(W, Ri, Rj)), Assn) <=> member((Ri, X, W), VM), member((Rj, Y, W), VM) |
    member((X, O1), Context),
    member((Y, O2), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    Assn = assn(variable(X), variable(Y)).

% tr-mov-ri2
bound(context(Context), X, O1), 
bound(context(Context), Y, pointer_type(array_type(O2))) \
dc_i(varmap(VM), context(Context), StrucMap, ins(mov2(W, Ri, IndRj)), Assn) <=> member((Ri, X, W), VM), member((IndRj, Y, 4), VM) |
    member((X, O1), Context),
    member((Y, pointer_type(array_type(O2))), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    Assn = assn(variable(X), arr(variable(Y), long(0))).

% tr-mov-ri3
bound(context(Context), X, O), 
bound(context(Context), Y, pointer_type(struct_type(Name))) \
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov2(W, Ri, IndRj)), Assn) <=> member((Ri, X, W), VM), member((IndRj, Y, 4), VM) |
    member((X, O), Context),
    member((Y, pointer_type(struct_type(Name))), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    nth0(0, FieldTypeVec, O0),
    sizeof(O, W),
    sizeof(O0, W),
    wt_sub(strucmap(S), O0, O),
    Assn = assn(variable(X), fld(variable(Y), long(0))).

% tr-mov-ri1
bound(context(Context), X, O1), 
bound(context(Context), Y, pointer_type(O2)) \
dc_i(varmap(VM), context(Context), StrucMap, ins(mov2(W, Ri, IndRj)), Assn) <=> member((Ri, X, W), VM), member((IndRj, Y, 4), VM) |
    member((X, O1), Context),
    member((Y, pointer_type(O2)), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    Assn = assn(variable(X), ptr(variable(Y))).


% tr-mov-ir2
bound(context(Context), X, pointer_type(array_type(O3))), 
bound(context(Context), Y, O2) \ 
dc_i(varmap(VM), context(Context), StrucMap, ins(mov5(W, IndRi, Rj)), Assn) <=> member((IndRi, X, 4), VM), member((Rj, Y, W), VM) |
    member((X, pointer_type(array_type(O3))), Context),
    member((Y, O2), Context),
    O1 = pointer_type(array_type(O3)),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O3),
    Assn = assn(arr(variable(X), long(0)), variable(Y)).

% tr-mov-ir3
bound(context(Context), X, pointer_type(struct_type(Name))), 
bound(context(Context), Y, O) \ 
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov5(W, IndRi, Rj)), Assn) <=> member((IndRi, X, 4), VM), member((Rj, Y, W), VM) |
    member((X, pointer_type(struct_type(Name))), Context),
    member((Y, O), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    nth0(0, FieldTypeVec, O0),
    sizeof(O, W),
    wt_sub(strucmap(S), O0, O),
    Assn = assn(fld(variable(X), long(0)), variable(Y)).

% tr-mov-ir1
bound(context(Context), X, pointer_type(O3)), 
bound(context(Context), Y, O2) \ 
dc_i(varmap(VM), context(Context), StrucMap, ins(mov5(W, IndRi, Rj)), Assn) <=> member((IndRi, X, 4), VM), member((Rj, Y, W), VM) |
    member((X, pointer_type(O3)), Context),
    member((Y, O2), Context),
    O1 = pointer_type(O3),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O3),
    Assn = assn(ptr(variable(X)), variable(Y)).

% tr-mov-ri+1
bound(context(Context), X, O1), 
bound(context(Context), Y, pointer_type(array_type(O2))) \ 
dc_i(varmap(VM), context(Context), StrucMap, ins(mov3(W, Ri, IndRj, C)), Assn) <=> member((Ri, X, W), VM), member((IndRj, Y, 4), VM) |
    member((X, O1), Context),
    member((Y, pointer_type(array_type(O2))), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W), 
    wt_sub(StrucMap, O2, O1),
    primitive_type(T),
    number(C),
    M is C / W,
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T),
    Assn = assn(variable(X), arr(variable(Y), TaggedM)).

% tr-mov-ri+2
bound(context(Context), X, O), 
bound(context(Context), Y, pointer_type(struct_type(Name))) \
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov3(W, Ri, IndRj, C)), Assn) <=> member((Ri, X, W), VM), member((IndRj, Y, 4), VM) |
    member((X, O), Context),
    member((Y, pointer_type(struct_type(Name))), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    sizeof_to_m(FieldTypeVec, M, C),
    sizeof(O, W),
    nth0(0, FieldTypeVec, O0),
    sizeof(O0, W),
    wt_sub(strucmap(S), O0, O),
    Assn = fld(variable(Y), long(M)).

% tr-mov-i+r1
bound(context(Context), X, pointer_type(array_type(O1))), 
bound(context(Context), Y, O2) \
dc_i(varmap(VM), context(Context), StrucMap, ins(mov6(W, IndRi, C, Rj)), Assn) <=> member((IndRi, X, 4), VM), member((Rj, Y, W), VM) |
    member((X, pointer_type(array_type(O1))), Context),
    member((Y, O2), Context),
    compact_type(O1),
    compact_type(O2),
    primitive_type(T),
    sizeof(T, Size),
    M is C / Size,
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T),
    sizeof(O1, W), 
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    Assn = assn(arr(variable(X), TaggedM), variable(Y)).

% tr-mov-i+r2
bound(context(Context), X, pointer_type(struct_type(Name))), 
bound(context(Context), Y, O) \
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov6(W, IndRi, C, Rj)), Assn) <=> member((IndRi, X, 4), VM), member((Rj, Y, W), VM) |
    member((X, pointer_type(struct_type(Name))), Context),
    member((Y, O), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    sizeof_to_m(FieldTypeVec, M, C),
    sizeof(O, W),
    nth0(0, FieldTypeVec, O0),
    wt_sub(strucmap(S), O0, O),
    Assn = assn(fld(variable(X), long(M)), variable(Y)).

%tr-alloc-r*
bound(context(Context), X, pointer_type(array_type(O))), 
bound(context(Context), Y, T) \
dc_i(varmap(VM), context(Context), StrucMap, ins(alloc2(Ri, Rj, C)), Assn) <=> member((Ri, X, 4), VM), member((Rj, Y, ST), VM), primitive_type(T) |
    member((X, pointer_type(array_type(O))), Context),
    member((Y, T), Context),
    sizeof(T, ST),
    sizeof(O, W),
    number(C),
    M is C / W,
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T),
    Res = Y * M,
    Assn = assn(variable(X), new_arr(O, Res)).


%tr-alloc-rc2
bound(context(Context), X, pointer_type(struct_type(Name))) \
dc_i(varmap(VM), context(Context), strucmap(S), ins(alloc1(Ri, C)), Assn) <=>  member((Ri, X, 4), VM) |
    member((X, pointer_type(struct_type(Name))), Context),
    member((Name, FieldTypeVec), S),
    sizeofall(FieldTypeVec, C),
    Assn = assn(variable(X), new_struct(Name)).

%tr-alloc-rc3
bound(context(Context), X, pointer_type(array_type(O))) \
dc_i(varmap(VM), context(Context), StrucMap, ins(alloc1(Ri, C)), Assn) <=> member((Ri, X, 4), VM) |
    member((X, pointer_type(array_type(O))), Context),
    sizeof(O, Size),
    number(C),
    M is C / Size,
    T = long,
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T),
    Assn = assn(variable(X), new_arr(O, M)).

%tr-alloc-rc1
bound(context(Context), X, pointer_type(O)) \
dc_i(varmap(VM), context(Context), _, ins(alloc1(Ri, C)), Assn) <=> member((Ri, X, 4), VM) |
    member((X, pointer_type(O)), Context),
    sizeof(O, C),
    Assn = assn(variable(X), new_compact(O)).

    
%dc_b(LabelMap, VarMap, Context, StrucMap, Block, Statement).
dc_b(_, _, _, _, ret, return). % tr-ret

dc_b(labelmap(ULam), _, _, _, goto(A), goto(L)) :- % tr-goto
    member((A, L), ULam).

dc_b(LabelMap, VarMap, Context, StrucMap, seq(ins(Ins), Block), seq(assn(L, E), Stmt)) :- %tr-instr
    dc_i(VarMap, Context, StrucMap, ins(Ins), assn(L, E)),
    dc_b(LabelMap, VarMap, Context, StrucMap, Block, Stmt).

dc_b(labelmap(LM), varmap(VM), context(C), SM, seq(if(W, Ri, A), B), seq(if(X, L), S)) :- %tr-if
    member((A, L), LM),
    member((Ri, X, _), VM),
    member((X, O), C),
    compact_type(O),
    sizeof(O, W),
    dc_b(labelmap(LM), varmap(VM), context(C), SM, B, S).

dc_d(StrucMap, fdef(Rargs, Rlocs, Rret, ABMap, Index), func(Args, Locals, Label, LS, Index)) :-
    nth0(Index, Rlocs, _),
    Xs = Rargs,
    Ys = Rlocs,
    comb(ABMap, LS, LabelMap),
    zip(Xs, _TypeXs, Args),
    zip(Ys, _TypeYs, Locals),
    zip3(Rargs, Xs, _ArgSizes, VM1),
    zip3(Rlocs, Ys, _LocalSizes, VM2),
    append(VM1, VM2, VarMap),
    member((Rret, Label), LabelMap),
    append(Args, Locals, Context),
    member((Rret, _), ABMap),
    member((A1, L1), LabelMap), 
    member((A1, Block), ABMap), 
    member((L1, Stmt), LS), 
    dc_b(labelmap(LabelMap), varmap(VarMap), context(Context), StrucMap, Block, Stmt),
    !,
    %Context = [(rx, pointer_type(pointer_type(long))), (ry, pointer_type(long))],
    labelingV(VarMap),
    labelingC(context(Context), context(Context)).

labelingV([]).
labelingV([(_, _, W) | Tail]) :-
    member(W, [4]),
    labelingV(Tail).

labelingC(_, context([])) :- done.
labelingC(Original, context([(X, T) | Tail])) :-
    compact_type(T, 1),
    bound(Original, X, T),
    labelingC(Original, context(Tail)).

done, dc_i(_, _, _, _, _) <=> true | fail.
done \ bound(context(C), X, T) <=> true | nonvar(X), nonvar(T), member((X, T), C). 
bound(context([]), _, _) <=> true | fail.
done <=> true | true.

%comb(ABMap, LS, LabelMap) :-
comb([], [], []).
comb([(X, _) |T1], [(Y, _) |T2], [(X, Y) | S]) :-
    comb(T1, T2, S). 


zip([], [], []).
zip([X |T1], [Y |T2], [(X, Y) | T3]) :-
    zip(T1, T2, T3).

zip3([], [], [], []).
zip3([X |T1], [Y |T2], [Z |T3], [(X, Y, Z) | T4]) :-
    zip3(T1, T2, T3, T4).
