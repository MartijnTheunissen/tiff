%prolog

%MinC types
primitive_type(short).
primitive_type(long).

compact_type(T) :-
    primitive_type(T).
compact_type(T) :-
    pointer_type(T).

pointer_type(T) :-
    atom(T).
array_type(T) :-
    atom(T).
struct_type(Name) :-
    atom(Name).

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
expression(func(Args, Locals, Label, LS, Index)) :-
    is_list(Args),
    is_list(Locals),
    label(Label),
    is_list(LS),
    number(Index).
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

%Struc map
strucmap([]).
strucmap([(Name, FieldTypeVec)]) :-
    atom(Name),
    is_list(FieldTypeVec).
strucmap([(Name, FieldTypeVec)] |Tail) :-
    atom(Name),
    is_list(FieldTypeVec),
    strucmap(Tail).

%wt_d(StrucMap, Def)
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

wt_sub(StrucMap, O1, O3) :- %sub-trans --> Problematic introduction of O2?
    compact_type(O2),
    wt_sub(StrucMap, O1, O2),
    wt_sub(StrucMap, O2, O3).



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
    nth(Index, FieldTypeVec, Oi).

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
    simple_type(T).

wt_le(Context, StrucMap, oper+(E1, E2), pointer_type(array_type(O))) :- %t-ptr-oper+
    wt_le(Context, StrucMap, E1, pointer_type(array_type(O))),
    compact_type(O),
    wt_le(Context, StrucMap, E2, T),
    simple_type(T).

wt_le(Context, StrucMap, oper+(E1, E2), pointer_type(array_type(O))) :- %t-oper+-ptr
    wt_le(Context, StrucMap, E1, T),
    simple_type(T),
    wt_le(Context, StrucMap, E2, pointer_type(array_type(O))),
    compact_type(O).

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

tag(short, S, T) :-
    T = short(S).
tag(long, L, T) :-
    T = long(L).

%dc_i(VarMap, TypeEnv, StructDefs, Instruction, assign(L, E)).

% tr-oper+-r*1
dc_i(varmap(VM), context(Context), StructDefs, ins(oper+(4, Ri, Rj, C)), assn(variable(X), oper+(variable(X), Y * M))) :-
    member((Ri, X, 4), VM),
    member((Rj, Y, 4), VM),
    member((X, pointer_type(array_type(O))), Context),
    compact_type(O),
    member((Y, long), Context),
    sizeof(O, Size),
    tag(long, M, TaggedVal),
    wt_le(context(Context), StructDefs, TaggedVal, long),
    number(C),
    M is C / Size,
    !.

% tr-oper+-r*2
dc_i(varmap(VM), context(Context), StructDefs, ins(oper+(W, Ri, Rj, C)), assn(variable(X), oper+(variable(X), Res))) :-
    member((Ri, X, W), VM),
    member((Rj, Y, W), VM),
    member((X, T), Context),
    member((Y, T), Context),
    primitive_type(T),
    tag(T, C, TaggedC),
    wt_le(context(Context), StructDefs, TaggedC, T),
    number(C),
    !,
    Res = Y * C.

% tr-oper+-rc
dc_i(varmap(VM), context(Context), StructDefs, ins(oper+(4, Ri, C)), assn(variable(X), oper+(variable(X), M))) :-
    member((Ri, X, 4), VM),
    member((X, pointer_type(array_type(O))), Context),
    compact_type(O),
    primitive_type(T),
    sizeof(O, Size),
    number(C),
    M is C / Size,
    tag(T, M, TaggedVal),
    wt_le(context(Context), StructDefs, TaggedVal, T),
    !.

% tr-oper*-rc
dc_i(varmap(VM), context(Context), StructDefs, ins(oper*(W, Ri, C)), assn(variable(X), oper*(variable(X), C))) :-
    member((Ri, X, W), VM),
    member((X, T), Context),
    primitive_type(T),
    sizeof(T, W),
    number(C),
    tag(T, C, TaggedC),
    wt_le(context(Context), StructDefs, TaggedC, T),
    !.

% tr-oper*-rr
dc_i(varmap(VM), context(Context), _, ins(oper*(W, Ri, Rj)), assn(variable(X), oper*(variable(X), variable(Y)))) :-
    member((Ri, X, W), VM),
    member((Rj, Y, W), VM),
    member((X, T), Context),
    member((Y, T), Context),
    primitive_type(T),
    sizeof(T, W),
    !.

% tr-mov-rc
dc_i(varmap(VM), context(Context), StructDefs, ins(mov1(W, Ri, C)), assn(variable(X), C)) :-
    member((Ri, X, W), VM),
    member((X, T), Context),
    primitive_type(T),
    sizeof(T, W),
    number(C),
    tag(T, C, TaggedC),
    wt_le(context(Context), StructDefs, TaggedC, T),
    !.

% tr-mov-r0
dc_i(varmap(VM), context(Context), _, ins(mov1(4, Ri, 0)), assn(variable(X), ptr(0))) :-
    member((Ri, X, 4), VM),
    member((X, pointer_type(_)), Context),
    !.

% tr-mov-rr
dc_i(varmap(VM), context(Context), StrucMap, ins(mov4(W, Ri, Rj)), assn(variable(X), variable(Y))) :-
    member((Ri, X, W), VM),
    member((Rj, Y, W), VM),
    member((X, O1), Context),
    member((Y, O2), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1), % --> introduces problems.
    !.

% tr-mov-ri1
dc_i(varmap(VM), context(Context), StrucMap, ins(mov2(W, Ri, IndRj)), assn(variable(X), ptr(variable(Y)))) :-
    member((Ri, X, W), VM),
    member((IndRj, Y, 4), VM),
    member((X, O1), Context),
    member((Y, pointer_type(O2)), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    !.

% tr-mov-ri2
dc_i(varmap(VM), context(Context), StrucMap, ins(mov2(W, Ri, IndRj)), assn(variable(X), arr(variable(Y), long(0)))) :-
    member((Ri, X, W), VM),
    member((IndRj, Y, 4), VM),
    member((X, O1), Context),
    member((Y, pointer_type(array_type(O2))), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    !.

% tr-mov-ri3
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov2(W, Ri, IndRj)), assn(variable(X), fld(variable(Y), long(0)))) :-
    member((Ri, X, W), VM),
    member((IndRj, Y, 4), VM),
    member((X, O), Context),
    member((Y, pointer_type(struct_type(Name))), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    nth0(0, FieldTypeVec, O0),
    sizeof(O, W),
    sizeof(O0, W),
    wt_sub(strucmap(S), O0, O),
    !.

% tr-mov-ir1
dc_i(varmap(VM), context(Context), StrucMap, ins(mov5(W, IndRi, Rj)), assn(ptr(variable(X)), variable(Y))) :-
    member((IndRi, X, 4), VM),
    member((Rj, Y, W), VM),
    member((X, pointer_type(O1)), Context),
    member((Y, O2), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    !.

% tr-mov-ir2
dc_i(varmap(VM), context(Context), StrucMap, ins(mov5(W, IndRi, Rj)), assn(arr(variable(X), long(0)), variable(Y))) :-
    member((IndRi, X, 4), VM),
    member((Rj, Y, W), VM),
    member((X, pointer_type(array_type(O1))), Context),
    member((Y, O2), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    !.
%
% tr-mov-ir3
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov5(W, IndRi, Rj)), assn(fld(variable(X), long(0)), variable(Y))) :-
    member((IndRi, X, 4), VM),
    member((Rj, Y, W), VM),
    member((X, pointer_type(struct_type(Name))), Context),
    member((Y, O), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    nth0(0, FieldTypeVec, O0),
    sizeof(O, W),
    wt_sub(strucmap(S), O0, O),
    !.

% tr-mov-ri+1
dc_i(varmap(VM), context(Context), StrucMap, ins(mov3(W, Ri, IndRj, C)), assn(variable(X), arr(variable(Y), M))) :-
    member((Ri, X, W), VM),
    member((IndRj, Y, 4), VM),
    member((X, O1), Context),
    member((Y, pointer_type(array_type(O2))), Context),
    compact_type(O1),
    compact_type(O2),
    sizeof(O1, W),
    sizeof(O2, W), 
    wt_sub(StrucMap, O2, O1),
    simple_type(T),
    number(C),
    M is C / W,
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T);
    !.

% tr-mov-ri+2
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov3(W, Ri, IndRj, C)), assn(variable(X), fld(variable(Y), _))) :-
    member((Ri, X, W), VM),
    member((IndRj, Y, 4), VM),
    member((X, O), Context),
    member((Y, pointer_type(struct_type(Name))), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    sizeofall(FieldTypeVec, C),
    sizeof(O, W),
    nth0(0, FieldTypeVec, O0),
    sizeof(O0, W),
    wt_sub(strucmap(S), O0, O),
    !.

% tr-mov-i+r1
dc_i(varmap(VM), context(Context), StrucMap, ins(mov6(W, IndRi, C, Rj)), assn(arr(variable(X), M), variable(y))) :-
    member((IndRi, X, 4), VM),
    member((Rj, Y, W), VM),
    member((X, pointer_type(array_type(O1))), Context),
    member((Y, O2), Context),
    compact_type(O1),
    compact_type(O2),
    simple_type(T),
    sizeof(T, Size),
    M is C / Size,
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T),
    sizeof(O1, W), 
    sizeof(O2, W),
    wt_sub(StrucMap, O2, O1),
    !.

% tr-mov-i+r2
dc_i(varmap(VM), context(Context), strucmap(S), ins(mov6(W, IndRi, C, Rj)), assn(fld(variable(X), _), variable(Y))) :-
    member((IndRi, X, 4), VM),
    member((Rj, Y, W), VM),
    member((X, pointer_type(struct_type(Name))), Context),
    member((Y, O), Context),
    compact_type(O),
    member((Name, FieldTypeVec), S),
    sizeofall(FieldTypeVec, C),
    sizeof(O, W),
    nth0(0, FieldTypeVec, O0),
    wt_sub(strucmap(S), O0, O),
    !.

%tr-alloc-r*
dc_i(varmap(VM), context(Context), StrucMap, ins(alloc2(Ri, Rj, C)), assn(variable(X), new_arr(O, Res))) :-
    member((Ri, X, 4), VM),
    member((Rj, Y, ST), VM),
    member((X, pointer_type(array_type(O))), Context),
    member((Y, T), Context),
    sizeof(T, ST),
    primitive_type(T),
    sizeof(O, W),
    number(C),
    M is C / W,
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T),
    Res = Y * M,
    !.

%tr-alloc-rc1
dc_i(varmap(VM), context(Context), _, ins(alloc1(Ri, C)), assn(variable(X), new_compact(O))) :-
    member((Ri, X, 4), VM),
    member((X, pointer_type(O)), Context),
    sizeof(O, C),
    !.

%tr-alloc-rc2
dc_i(varmap(VM), context(Context), _, ins(alloc1(Ri, C)), assn(variable(X), new_struct(Name))) :-
    member((Ri, X, 4), VM),
    member((X, pointer_type(struct_type(Name))), Context),
    sizeof(Name, C), % <--- sizeof(Name) ????
    !.

%tr-alloc-rc3
dc_i(varmap(VM), context(Context), StrucMap, ins(alloc1(Ri, C)), assn(variable(X), new_arr(O, M))) :-
    member((Ri, X, 4), VM),
    member((X, pointer_type(array_type(O))), Context),
    sizeof(O, Size),
    number(C),
    M is C / Size,
    primitive_type(T),
    tag(T, M, TaggedM),
    wt_le(context(Context), StrucMap, TaggedM, T),
    !.

%dc_b(LabelMap, VarMap, Context, StrucMap, Block, Statement).
dc_b(_, _, _, _, ret, return). % tr-ret

dc_b(labelmap(ULam), _, _, _, goto(A), goto(L)) :- % tr-goto
    member((A, L), ULam).

dc_b(LabelMap, VarMap, Context, StrucMap, seq(ins(Ins), Block), seq(assn(L, E), Stmt)) :- %tr-instr
    dc_i(VarMap, Context, StrucMap, ins(Ins), assn(L, E)),
    dc_b(LabelMap, VarMap, Context, StrucMap, Block, Stmt),
    !.

dc_b(labelmap(LM), varmap(VM), context(C), SM, seq(if(W, Ri, A), B), seq(if(X, L), S)) :- %tr-if
    member((A, L), LM),
    member((Ri, X, _), VM),
    member((X, O), C),
    compact_type(O),
    sizeof(O, W),
    dc_b(labelmap(LM), varmap(VM), context(C), SM, B, S),
    !.

