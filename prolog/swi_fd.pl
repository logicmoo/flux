
:- module(fd,[local/1,op(1150,fx,(export)),op(700, xfx, '::'),op(710, xfx, '..'),
  op(750, fy, '#\\+' ),op(700, xfx, '##'),op(700, xfx, '#=' ),op(760, yfx, '#/\\' ),
  op(770, yfx, '#\\/' ),op(780, yfx, '#=>' ),op(790, yfx, '#<=>' ),op(800, xfx, isd),
  op(400, yfx, ('*`')),op(750, fy, local), op(1190,xfy,(do)),getval/2,setval/2,('::'/2),(do/2)]).

:- meta_predicate(local(:)).
local(Call) :- call(Call).
:-  op(750, fy, local).

'::'([L|ST],G):-!, in(L,G), ('::'(ST,G)).
'::'([],_).

:- op(1150,fx,(export)).
:- op(1190,xfy,(do)).
:- reexport(library('clp/clpfd')).

:-  op(750, fy, '#\\+' ).
:-  op(700, xfx, '##').
:-  op(700, xfx, '#=' ).
:-  op(760, yfx, '#/\\' ).
:-  op(770, yfx, '#\\/' ).
:-  op(780, yfx, '#=>' ).
:-  op(790, yfx, '#<=>' ).
:-  op(800, xfx, isd).
:-  op(400, yfx, ('*`')). 


reference(Var):-nb_setval(Var,[]).
variable(Var):-nb_setval(Var,[]).
variable(Var,VAL):-nb_setval(Var,VAL).
setval(Var,VAL):-nb_setval(Var,VAL).
getval(Var,VAL):-nb_getval(Var,VAL).

do(Param,Body):- Param =.. [param|_],!,forall(Body,true).
do(foreach(Clause,Clauses),Body):- forall(member(Clause,Clauses),Body).
do(Head,Body):- throw(not_impl(do(Head,Body))).

% summary:"Succeeds if Term is a domain variable.
is_domain(T):-clpfd:fd_get(T, Dom, _), !, T in Dom.

setval(X):-trace,nb_setval(X,[]).

% copy_term_vars(?Vars, ?OldTerm, -NewTerm)
copy_term_vars(Vars,OldTerm,NewTerm):-copy_term(OldTerm,NewTerm),term_variables(NewTerm,Vars).

system:'#\\+'(C):- '#\\'(C).

is_predicate(F/A):-current_predicate(F/A), functor(P,F,A),predicate_property(P, visible).

nonground(X):- \+ ground(X).

:- fixup_exports.
