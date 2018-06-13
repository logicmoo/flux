:-module(flux).

%% Choose a Wumpus World

%% :-use_module(wumpus_world_small).
:-use_module(wumpus_world_big).

:-export execute/1.
:-export holds/1.
:-export init/0.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% FLUX
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Libraries
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%
%% finite domain constraint solver (Eclipse library)
%%
:- lib(fd).

:- lib(chr).

%%
%% FLUX constraint handling rules
%%
%% :- chr('fluent').
:-['fluent.pl'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% State Specifications and Update
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%
%% holds(F,Z)
%%
%% asserts that fluent F holds in state Z
%%
holds(F, [F|_]).
holds(F, Z) :- nonvar(Z), Z=[F1|Z1], F\==F1, holds(F, Z1).

%%
%% holds(F,Z,Zp)
%%
%% asserts that fluent F holds in state Z
%%
%% state Zp is Z without F.
%%
holds(F, [F|Z], Z).
holds(F, Z, [F1|Zp]) :- nonvar(Z), Z=[F1|Z1], F\==F1, holds(F, Z1, Zp).

%%
%% cancel(F,Z1,Z2)
%%
%% state Z2 is state Z1 with all (positive, negative, disjunctive)
%% knowledge of fluent F canceled
%%
cancel(F,Z1,Z2) :-
   var(Z1)    -> cancel(F,Z1), cancelled(F,Z1), Z2=Z1 ;
   Z1 = [G|Z] -> ( F\=G -> cancel(F,Z,Z3), Z2=[G|Z3]
                         ; cancel(F,Z,Z2) ) ;
   Z1 = []    -> Z2 = [].

%%
%% minus(Z1,ThetaN,Z2)
%%
%% state Z2 is state Z1 minus the fluents in list ThetaN
%%
minus_(Z, [], Z).
minus_(Z, [F|Fs], Zp) :-
   ( \+ not_holds(F, Z) -> holds(F, Z, Z1) ;
     \+ holds(F, Z)     -> Z1 = Z
                         ; cancel(F, Z, Z1), not_holds(F, Z1) ),
   minus_(Z1, Fs, Zp).

%%
%% plus(Z1,ThetaP,Z2)
%%
%% state Z2 is state Z1 plus the fluents in list ThetaP
%%
plus_(Z, [], Z).
plus_(Z, [F|Fs], Zp) :-
   ( \+ holds(F, Z)     -> Z1=[F|Z] ;
     \+ not_holds(F, Z) -> Z1=Z
                         ; cancel(F, Z, Z2), not_holds(F, Z2), Z1=[F|Z2] ),
   plus_(Z1, Fs, Zp).

%%
%% update(Z1,ThetaP,ThetaN,Z2)
%%
%% state Z2 is state Z1 minus the fluents in list ThetaN
%% plus the fluents in list ThetaP
%%
update(Z1, ThetaP, ThetaN, Z2) :-
   minus_(Z1, ThetaN, Z), plus_(Z, ThetaP, Z2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% State Knowledge
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%
%% knows(F,Z)
%% 
%% ground fluent F is known to hold in state Z
%%
knows(F, Z) :- \+ not_holds(F, Z).

%%
%% knows_not(F,Z)
%% 
%% ground fluent F is known not to hold in state Z
%%
knows_not(F, Z) :- \+ holds(F, Z).

%%
%% knows_val(X,F,Z)
%% 
%% there is an instance of the variables in X for which
%% non-ground fluent F is known to hold in state Z
%%
%% Example:
%%
%% ?- knows_val([X], f(X,Y), [f(1,3),f(2,U),f(V,2)|_])
%%
%% X=1 More?
%% X=2 More?
%% No
%%
knows_val(X, F, Z) :- k_holds(F, Z), knows_val(X).

k_holds(F, Z) :- nonvar(Z), Z=[F1|Z1],
                 ( instance(F1, F), F=F1 ; k_holds(F, Z1) ).

:-local variable(known_val).
:-setval(known_val,nil).

knows_val(X) :- dom(X), \+ nonground(X), ambiguous(X) -> false.
knows_val(X) :- getval(known_val,X), X \== nil, setval(known_val, nil).

dom([]).
dom([X|Xs]) :- dom(Xs), ( is_domain(X) -> indomain(X)
                                        ; true ).

ambiguous(X) :- 
   ( getval(known_val, Val), 
     Val \== nil -> setval(known_val, nil)
   ;
                    setval(known_val, X), 
                    false
   ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% ALPprolog to FLUX
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Initialize
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init :-
        initial_state(S),
        normalize_formula(S,S1),
        initial_to_flux_state(S1,S2),
        setval(actions,0),
        set_state(S2),
        set_sit(s0).

normalize_formula(FormulaIn,FormulaOut) :-
        split_clauses(FormulaIn,Units,Clauses),
        ( foreach(Clause,Clauses),
          foreach(Clause1,Clauses1) do
            sort(Clause,Clause1) ),
        sort(Clauses1,Clauses2),
        sort(Units,Units1),
        append(Units1,Clauses2,FormulaOut).

split_clauses([El|Rest],[El|Units],Clauses) :-
        El \= .(_,_),
        !,
        split_clauses(Rest,Units,Clauses).
split_clauses([],[],[]) :-
        !.
split_clauses([El|Rest],[],[El|Rest]) :-
        El = .(_,_).

initial_to_flux_state(ABox,State) :-
        ( foreach(El,ABox),
          param(State) do
            ( El = neg(Atom) ->
                not_holds(Atom,State)
            ;
                holds(El,State) ) ),
        duplicate_free(State).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Store States and Situations
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-local reference(state).
:-local variable(sit).

state(State) :-
        getval(state,State).

set_state(NewState) :-
        setval(state,NewState).

sit(Sit) :-
        getval(sit,Sit).

set_sit(Action) :-
        getval(sit,Sit),
        setval(sit,did(Action,Sit)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  Execute an Action
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

execute(Action) :-
        action(Action,Pre,Eff),
        holds(Pre),
        update(Eff),
        set_sit(Action).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  Update the FLUX state
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

update(Update) :-
        getval(state,State),
        flux_update(State,Update,State1),
        !,
        setval(state,State1).

flux_update(StateIn,Update,StateOut) :-
        ( foreach(El,Update),
          fromto([],InP,OutP,Plus),
          fromto([],InM,OutM,Minus) do
            ( El = neg(Atom) ->
                InP = OutP,
                [Atom|InM] = OutM
            ;
                InM = OutM,
                [El|InP] = OutP ) ),
        update(StateIn,Plus,Minus,StateOut).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  Holds To FLUX
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Assume Formula does not contain a(X), a(Y) with diff. vars

holds(Formula) :-
        ( Formula = [Lit],
          sensor(Lit) ->
            sense(Lit)
        ;
            getval(state,State),
            ( foreach(El,Formula),
              param(State) do
                ( El = .(_,_) ->
                    flux_holds(State,El)
                ;
                    ( aux1(El) ->
                        call(El)
                    ;
                        flux_holds(State,[El]) ) ) ) ).


flux_holds(State,Query) :-
        ( foreach(El,Query),
          param(State) do
            ( ground(El) ->
                ( El = neg(Atom) ->
                    knows_not(Atom,State)
                ;
                    knows(El,State) )
            ;
                term_variables(El,Vars),
                knows_val(Vars,El,State) ) ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  Identify Query Types
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


aux1(Lit) :-
        Lit =.. [P|_],
        aux(Aux),
        memberchk(P,Aux).

sensor(Lit) :-
        sensors(Sensors),
        Lit =.. [P|_],
        memberchk(P,Sensors).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  Sensing
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sense(Lit) :-
        sensor_axiom(Lit,Vals),
        sense_val(Lit,Assig),
        memberchk(Assig-Index-Meaning,Vals),
        holds(Index),
        getval(state,State),
        ( Meaning = [[H|T]] ->
            or_holds([H|T],State)
        ;
            flux_update(State,Meaning,State1),
            setval(state,State1)).

sense_val(Lit,Assig) :-
        real_world(World),
        ( Lit = glitter(X) ->
            holds([at(agent,Y)]),
            ( memberchk(at(gold,Y),World) ->
                Assig = [X-true]
            ;
                Assig = [X-false] )
        ;
            ( Lit = breeze(X) ->
                holds([at(agent,Y)]),
                ( adjacent(Y,Z),
                  memberchk(pit(Z),World) ->
                    Assig = [X-true]
                ;
                    Assig = [X-false] )
            ;
                Lit = stench(X),
                holds([at(agent,Y)]),
                ( adjacent(Y,Z),
                  memberchk(at(wumpus,Z),World) ->
                    Assig = [X-true]
                ;
                    Assig = [X-false] ) ) ).




