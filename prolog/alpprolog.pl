:-module(alpprolog,[]).

:- expects_dialect(eclipse).

%% Choose a Wumpus World

%% :-use_module(wumpus_world_small).
:- use_module(wumpus_world_big).

%:-lib(lists).

:-export execute/1.
:-export holds/1.
:-export init/0.
:-export state/1.

:- local(variable(current_units)).
:- local(variable(current_clauses)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Initialize                                                %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init :-
        initial_state(S),
        normalize_formula(S,S1),
        setval(actions,0),
        set_state(S1),
        set_sit(s0).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Store States and Situations                               %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Static Handling of Propositional Formulas                 %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Normalizing a Propositional Formula                       %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

normalize_formula(FormulaIn,FormulaOut) :-
        split_clauses(FormulaIn,Units,Clauses),
        ( foreach(Clause,Clauses),
          foreach(Clause1,Clauses1) do
            sort(Clause,Clause1) ),
        sort(Clauses1,Clauses2),
        sort(Units,Units1),
        append(Units1,Clauses2,FormulaOut).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Negate Literal                                            %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

negate_literal(Lit,Neg) :-
        ( Lit = neg(Atom) ->
            Neg = Atom
        ;
            Neg = neg(Lit) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Tautological Clauses                                      %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

tautology(Clause) :-
        ( restmember(Lit,Clause,Rest),
          negate_literal(Lit,Neg),
          omemberchk(Neg,Rest) ->
            true
        ;
            fail ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Transform Clause Set to Prime Implicates                  %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

primpls_to_primpls(PI1,PI2,PI) :-
        
        split_clauses(PI1,U1,C1),
        split_clauses(PI2,U2,C2),
        
        append(U1,U2,U3),
        sort(U3,U),
        setval(current_units,U),
        
        remove_clauses_subsumed_by_units(C1,U2,C3),
        remove_clauses_subsumed_by_units(C2,U1,C4),
        
        append(C3,C4,C5),
        sort(C5,C),
        setval(current_clauses,C),
        
        resolve_units_clauses(U2,C3,NU1,NC1),
        resolve_units_clauses(U1,C4,NU2,NC2),

        append(NU1,NU2,NU3),
        append(NU3,U,U4),
        sort(U4,NU),
        setval(current_units,NU),
        
        remove_clauses_subsumed_by_units(NC1,NU,NC3),
        remove_clauses_subsumed_by_units(NC2,NU,NC4),
        
        remove_subsumed_clauses(NC3,NC4,NC5),
        getval(current_clauses,NC6),
        append(NC5,NC6,NC7),
        sort(NC7,NC),
        
        clause_set_to_prime_implicates(NU,NC,PI).



clause_set_to_prime_implicates([],[],PIs) :-
        !,
        getval(current_units,Units),
        getval(current_clauses,Clauses),
        append(Units,Clauses,PIs).
        

clause_set_to_prime_implicates(Units,Clauses,PIs) :-
        
        getval(current_clauses,Clauses1),
        
        resolve_units_clauses(Units,Clauses,NU1,NC1),

        resolve_units_clauses(Units,Clauses1,NU2,NC2),
        
        resolve_all_clauses(Clauses,NU3,NC3),
        
        resolve_all_clauses(Clauses,Clauses1,NU4,NC4),
        
        append(NU1,NU2,NU5),
        append(NU3,NU4,NU6),
        append(NU5,NU6,NU),
        
        append(NC1,NC2,NC5),
        append(NC3,NC4,NC6),
        append(NC5,NC6,NC),
        
        clause_set_to_prime_implicates(NU,NC,PIs).


        


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Remove Subsumed Clauses from Clause Set                   %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove_subsumed_clauses(C1,C2,C) :-
       ( foreach(C,C1),
         fromto(C3,Out,In,[]),
         param(C2) do
           ( member(D,C2),
             subset(D,C) ->
               Out = In
           ;
               Out = [C|In] ) ),
       
       ( foreach(E,C2),
         fromto(C4,Out,In,[]),
         param(C3) do
           ( member(F,C3),
             subset(F,E) ->
               Out = In
           ;
               Out = [E|In] ) ),
       
       append(C3,C4,C5),
       sort(C5,C).
       


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Resolve with Unit Clauses                                 %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

resolve_units_clauses([],_Clauses,[],[]) :-
        !.

resolve_units_clauses(_Units,[],[],[]) :-
        !.

resolve_units_clauses(Units,Clauses,NewUnits,NewClauses) :-
        resolve_units_clauses1(Units,Clauses,[],NewUnits1,NewClauses1),
        sort(NewUnits1,NewUnits),
        sort(NewClauses1,NewClauses).


resolve_units_clauses1([Unit],Clauses,KeptUnits,NewUnits,NewClauses) :-
        !,
        ( foreach(Clause,Clauses),
          fromto(NewUnits1,Out1,In1,[]),
          fromto(NewClauses,Out2,In2,[]),
          param(Unit) do
            ( resolve_unit_clause(Unit,Clause,NewClause) ->
                ( NewClause = [Single] ->
                    Out1 = [Single|In1],
                    Out2 = In2
                ;
                    Out1 = In1,
                    Out2 = [NewClause|In2] )
            ;
                Out1 = In1,
                Out2 = [Clause|In2] ) ),
        append(NewUnits1,KeptUnits,NewUnits).


resolve_units_clauses1([Unit|Units],Clauses,KeptUnits,NewUnits,NewClauses) :-
        ( foreach(Clause,Clauses),
          fromto(NewUnits1,Out1,In1,[]),
          fromto(NewClauses1,Out2,In2,[]),
          param(Unit) do
            ( resolve_unit_clause(Unit,Clause,NewClause) ->
                ( NewClause = [Single] ->
                    Out1 = [Single|In1],
                    Out2 = In2
                ;
                    Out1 = In1,
                    Out2 = [NewClause|In2] )
            ;
                Out1 = In1,
                Out2 = [Clause|In2] ) ),
        append(NewUnits1,KeptUnits,KeptUnits1),
        resolve_units_clauses1(Units,NewClauses1,KeptUnits1,NewUnits,NewClauses).


resolve_unit_clause(Unit,Clause,NewClause) :-
        negate_literal(Unit,Neg),
        orestmemberchk(Neg,Clause,NewClause1),
        
        reduce(NewClause1,NewClause2),
        
        ( NewClause2 = [] ->
            fail
        ;
            NewClause2 = NewClause ).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Reduce Accumulated Clause Set                             %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


reduce(C1,C2) :-
        
        getval(current_units,U),
        getval(current_clauses,C),
        
        ( C1 = [Single] ->
            ( memberchk(Single,U) ->
                C2 = []
            ;
                remove_clauses_subsumed_by_units(C,C1,NC),
                append(C1,U,NU1),
                sort(NU1,NU),
                setval(current_units,NU),
                setval(current_clauses,NC),
                C2 = C1)
        ;
            ( tautology(C1) ->
                C2 = []
            ;
                append(U,C,Cs),
                ( holds(Cs,[C1]) ->
                    C2 = []
                ;
                    ( foreach(D,C),
                      fromto(NC,Out,In,[]),
                      param(C1) do
                        ( subset(C1,D) ->
                            Out = In
                        ;
                            Out = [D|In] ) ),
                    append([C1],NC,NC1),
                    sort(NC1,NC2),
                    setval(current_clauses,NC2),
                    C2 = C1 ) ) ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Resolve Clauses                                           %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Between two sets

resolve_all_clauses([],_Clauses,[],[]) :-
        !.

resolve_all_clauses(_Clauses,[],[],[]) :-
        !.

resolve_all_clauses(ClauseSet1,ClauseSet2,NewUnits,NewClauses) :-
        cartesian(ClauseSet1,ClauseSet2,Pairs),
        ( foreach(Clause1-Clause2,Pairs),
          fromto([],In1,Out1,NewUnits2),
          fromto([],In2,Out2,NewClauses2) do
            resolve_all_clauses([Clause1,Clause2],NewUnits1,
                                NewClauses1),
            append(NewUnits1,In1,Out1),
            append(NewClauses1,In2,Out2) ),
        sort(NewUnits2,NewUnits),
        sort(NewClauses2,NewClauses).


%% In one set

resolve_all_clauses([],[],[]) :-
        !.

resolve_all_clauses([_Single],[],[]) :-
        !.

resolve_all_clauses([Clause1,Clause2],NewUnits,NewClauses) :-
        !,
        resolve_clause_all_clauses(Clause1,[Clause2],NewUnits,NewClauses).

resolve_all_clauses(Clauses,NewUnits,NewClauses) :-
        restmemberchk(Clause,Clauses,Rest),
        resolve_clause_all_clauses(Clause,Rest,NewUnits1,NewClauses1),
        resolve_all_clauses(Rest,NewUnits2,NewClauses2),
        append(NewUnits1,NewUnits2,NewUnits),
        append(NewClauses1,NewClauses2,NewClauses).

resolve_clause_all_clauses(Clause1,[Clause2],NewUnits,NewClauses) :-
        
        !,
        
        ( resolve_clauses(Clause1,Clause2,Resolvent) ->
        
            ( Resolvent = [_Single] ->
                NewUnits = Resolvent,
                NewClauses = []
            ;
                NewUnits = [],
                NewClauses = [Resolvent] )
        
        ;
            
            NewUnits = [],
            NewClauses = [] ).
        

resolve_clause_all_clauses(Clause1,[Clause2|Clauses],NewUnits,NewClauses) :-
        
        ( resolve_clauses(Clause1,Clause2,Resolvent) ->
        
            ( Resolvent = [Single] ->
                NewUnits = [Single|NewUnits1],
                NewClauses = NewClauses1
            ;
                NewUnits = NewUnits1,
                NewClauses = [Resolvent|NewClauses1] )
        ;
            NewUnits = NewUnits1,
            NewClauses = NewClauses1 ),
        
        resolve_clause_all_clauses(Clause1,Clauses,NewUnits1,NewClauses1).

resolve_clauses(Clause1,Clause2,NewClause) :-
        restmember(Lit1,Clause1,Rest1),
        negate_literal(Lit1,Neg),
        restmember(Neg,Clause2,Rest2),
        append(Rest1,Rest2,NewClause1),
        sort(NewClause1,NewClause2),
        reduce(NewClause2,NewClause3),
        ( NewClause3 = [] ->
            fail
        ;
            NewClause = NewClause2 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Remove Clauses Subsumed by Unit Clauses                   %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove_clauses_subsumed_by_units([Clause|Clauses],Units,Clauses1) :-
        member(Lit,Clause),
        omemberchk(Lit,Units),
        !,
        remove_clauses_subsumed_by_units(Clauses,Units,Clauses1).


remove_clauses_subsumed_by_units([Clause|Clauses],Units,[Clause|Clauses1]) :-
        !,
        remove_clauses_subsumed_by_units(Clauses,Units,Clauses1).

remove_clauses_subsumed_by_units([],_,[]).

%% test(1) :-
%%         remove_clauses_subsumed_by_units([[e,f],[a,b],[c,d],[g,h]],[a,b,c],C),
%%         writeln(C).



split_clauses([El|Rest],[El|Units],Clauses) :-
        El \= .(_,_),
        !,
        split_clauses(Rest,Units,Clauses).

split_clauses([],[],[]) :-
        !.

split_clauses([El|Rest],[],[El|Rest]) :-
        El = .(_,_).

        

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Update                                                    %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Interface                                                %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

execute(Action) :-
        action(Action,Pre,Eff),
        holds(Pre),
        update(Eff),
        set_sit(Action).

update(Update) :-
        state(State),
        update(State,Update,NewState),
        !,
        set_state(NewState).

update(State,Update,NewState) :-
        ( foreach(El,State),
          fromto(NewState1,Out,In,[]),
          param(Update) do
            ( El = .(_,_) ->
                ( affected_clause(El,Update) ->
                    Out = In
                ;
                    Out = [El|In] )
            ;
                ( affected_literal(El,Update) ->
                    Out = In
                ;
                    Out = [El|In] ) ) ),
        append(Update,NewState1,NewState2),
        normalize_formula(NewState2,NewState).
                
                
affected_literal(El,Update) :-
        ( memberchk(El,Update) ->
            true
        ;
            ( negate_literal(El,Neg),
              memberchk(Neg,Update) ->
                true
            ;
                false ) ).

affected_clause(Clause,Update) :-
        ( member(El,Clause),
          affected_literal(El,Update) ->
            true
        ;
            false ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Logical Consequence                                      %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Interface                                                %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

holds(Formula) :-
        ( Formula = [Lit],
          sensor(Lit) ->
            sense(Lit)
        ;
            state(State),
            normalize_formula(Formula,Formula1),
            holds(State,Formula1) ).

holds(State,Formula) :-
        ( ground(Formula) ->
            ground_holds(State,Formula)
        ;
            instantiate(State,Formula) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Ground Case                                              %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ground_holds(State,Formula) :-
        ( foreach(El,Formula),
          param(State) do
            ( El = .(_,_) ->
                ground_holds_clause(State,El)
            ;
                ground_holds_literal(State,El) ) ).

ground_holds_literal(State,Lit) :-
        ( aux1(Lit) ->
            Lit
        ;
            memberchk(Lit,State) ).

ground_holds_clause(State,Clause) :-
        aux_fluent(Clause,Aux,Fluent),
        ( member(Lit,Aux),
          Lit ->
            true
        ;
            ( member(Lit,Fluent),
              omemberchk(Lit,State) ->
                true
            ;
                ( member(El,State),
                  El = .(_,_),
                  subset(Fluent,El) ->
                    true
                ;
                    false ) ) ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Non-Ground Case                                          %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% ?- holds([[e(c), e(d)]], [e(X)]).
%% No (0.00s cpu)

instantiate(State,Formula) :-
        ( foreach(El,Formula),
          param(State) do
            ( El = .(_,_) ->
                instantiate_clause(State,El)
            ;
                instantiate_literal(State,El) ) ).

instantiate_literal(State,Lit) :-
        ( aux1(Lit) ->
            Lit
        ;
            member(Lit,State) ).

instantiate_clause(State,Clause) :-
        aux_fluent(Clause,Aux,Fluent),
        i1(Aux,Fluent,State).

i1(Aux,_Fluent,_State) :-
        member(Lit,Aux),
        Lit.

i1(_Aux,Fluent,State) :-
        member(Lit,Fluent),
        member(Lit,State).
        
i1(_Aux,Fluent,State) :-
        member(El,State),
        El = .(_,_),
        subset(Fluent,El).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Split Clause in Aux and Fluent                           %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

aux_fluent(Clause,Aux,Fluent) :-
        ( foreach(Lit,Clause),
          fromto(Aux,Out1,In1,[]),
          fromto(Fluent,Out2,In2,[]) do
            ( aux1(Lit) ->
                Out1 = [Lit|In1],
                Out2 = In2
            ;
                Out1 = In1,
                Out2 = [Lit|In2] ) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Identify Query Types                                     %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


aux1(Lit) :-
        Lit =.. [P|_],
        aux(Aux),
        memberchk(P,Aux).

sensor(Lit) :-
        sensors(Sensors),
        Lit =.. [P|_],
        memberchk(P,Sensors).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%% Sensing                                                   %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Interface                                                %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sense(Lit) :-
        sensor_axiom(Lit,Vals),
        sense_val(Lit,Assig),
        memberchk(Assig-Index-Meaning,Vals),
        ( Index = [] ->
            ( foreach(Var-Val,Assig) do
                Var = Val ),
            state(State),
            primpls_to_primpls(State,Meaning,PIs),
            set_state(PIs)
        ;
            holds(Index),
            ( foreach(Var-Val,Assig) do
                Var = Val ),
            state(State),
            primpls_to_primpls(State,Meaning,PIs),
            !,
            set_state(PIs) ).
        

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Utilities                                                %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%    Restmembers                                            %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

restmemberchk(H,[H|T],T) :- !.
restmemberchk(H,[H1|T],[H1|T1]) :-
        restmemberchk(H,T,T1).

restmember(H,[H|T],T) :-
        (T = [] ->
            !
        ;
            true ).
restmember(H,[H1|T],[H1|T1]) :-
        restmember(H,T,T1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%    Ordered Restmembers                                    %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

orestmemberchk(H,[H|T],T) :- !.
orestmemberchk(H,[H1|T],[H1|T1]) :-
        ( H1 @< H ->
            orestmemberchk(H,T,T1)
        ;
            fail ).

orestmember(H,[H|T],T) :-
        !.
orestmember(H,[H1|T],[H1|T1]) :-
        ground(H),
        !,
        ( H1 @< H ->
            orestmember(H,T,T1)
        ;
            fail).
orestmember(in(X,CR1),[in(Is,CR2)|T],[in(Is,CR2)|T1]) :-
        ( CR2 @< CR1 ->
            orestmember(in(X,CR1),T,T1)
        ;
            fail ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%    Ordered Members                                        %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

omemberchk(H,[H|_T]) :- !.
omemberchk(H,[H1|T]) :-
        ( H1 @< H ->
            omemberchk(H,T)
        ;
            fail ).

omember(H,[H|_T]) :-
        !.
omember(H,[H1|T]) :-
        ground(H),
        !,
        ( H1 @< H ->
            omember(H,T)
        ;
            fail).
omember(in(X,CR1),[in(_Is,CR2)|T]) :-
        ( CR2 @< CR1 ->
            omember(in(X,CR1),T)
        ;
            fail ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%    Cartesian                                              %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cartesian(L,K,Res):-
        (foreach(X,L),
         fromto([],In,Out,Res),
         param(K) do
            (foreach(Y,K),
             fromto(In,In1,[X-Y|In1],Out),
             param(X) do
                true )).


