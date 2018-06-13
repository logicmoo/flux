:-module(wumpus_world_small).

:-lib(fd).

:-export neighbours/2.
:-export connected/2.
:-export adjacent/2.
:-export initial_state/1.
:-export real_world/1.
:-export action/3.
:-export aux/1.
:-export sensors/1.
:-export sensor_axiom/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Declare Auxiliary Predicates                             %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

aux([neighbours,connected]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Declare Sensor Fluents                                   %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sensors([breeze,glitter,stench]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Declare Size of Wumpus World                             %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dimension(4).
%% dimension(8).
%% dimension(16).
%% dimension(32).


real_world(W) :-
        dimension(Dim),
        real_world(Dim,W).

initial_state(State) :-
        dimension(Dim),
        initial_state(Dim,State).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Actions                                                  %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Grab gold

action(grab,
       [at(gold,Cell),at(agent,Cell)],
       [carries(agent,gold),neg(at(gold,Cell))]).

%% Go to next cell

action(go(Cell1,Cell2),
       [at(agent,Cell1),
        connected(Cell1,Cell2)],
       [neg(at(agent,Cell1)),
        at(agent,Cell2)]).

%% Shoot the Wumpus

action(shoot,
       [carries(agent,arrow),
        at(wumpus,Cell1),
        at(agent,Cell2),
        connected(Cell2,Cell1)],
       [neg(carries(agent,arrow)),
        neg(alive(wumpus))]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Sensor Axioms                                            %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sensor_axiom(breeze(X),[ [X-true] -
                         [at(agent,Y),neighbours(Y,[Cell1,Cell2,Cell3,Cell4])] -
                         [[ pit(Cell1),pit(Cell2),pit(Cell3),pit(Cell4)]],
                       
                         [X-false] -
                         [at(agent,Y),neighbours(Y,[Cell1,Cell2,Cell3,Cell4])] -
                         [neg(pit(Cell1)),neg(pit(Cell2)),neg(pit(Cell3)),neg(pit(Cell4))]
                       ]).

sensor_axiom(glitter(X),[ [X-true] -
                          [at(agent,Y)] -
                          [at(gold,Y)],
                          
                          [X-false] -
                          [at(agent,Y)]-
                          [neg(at(gold,Y))]
                        ]).

sensor_axiom(stench(X),[ [X-true] -
                         [at(agent,Y),neighbours(Y,[Cell1,Cell2,Cell3,Cell4])]-
                         [[ at(wumpus,Cell1),at(wumpus,Cell2),at(wumpus,Cell3),at(wumpus,Cell4)]],

                         [X-false] -
                         [at(agent,Y),neighbours(Y,[Cell1,Cell2,Cell3,Cell4])]-
                         [neg(at(wumpus,Cell1)),neg(at(wumpus,Cell2)),neg(at(wumpus,Cell3)),neg(at(wumpus,Cell4))]
                       ]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Auxiliary Axioms                                         %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

connected(X,Y) :-
        adjacent(X,Y).

adjacent(cell(X,Y),cell(X1,Y1)) :-
        dimension(Dim),
        [X,Y,X1,Y1]::1..Dim,
        (X1#=X) #/\ (Y1#=Y+1)
        #\/ (X1#=X) #/\ (Y1#=Y-1)
        #\/ (X1#=X+1) #/\ (Y1#=Y)
        #\/ (X1#=X-1) #/\ (Y1#=Y),
        labeling([X,Y,X1,Y1]).

neighbours(cell(X,Y),
           [cell(X,Y1),cell(X,Y2),cell(X1,Y),cell(X2,Y)]) :-
        Y1 is Y + 1,
        Y2 is Y - 1,
        X1 is X + 1,
        X2 is X - 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  The real world                                           %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% ... comes in four different sizes

real_world(4,[at(wumpus,cell(2,4)),
            pit(cell(4,2)),
            at(gold,cell(4,4))]).

real_world(8,[at(wumpus,cell(6,6)),
            at(gold,cell(7,6)),
            pit(cell(7,3)),
            pit(cell(5,3)),
            pit(cell(4,3)),
            pit(cell(5,7)),
            pit(cell(3,4))]).

real_world(16,[at(wumpus,cell(9,6)),
               at(gold,cell(11,13)),
               pit(cell(2,3)),
               pit(cell(2,10)),
               pit(cell(5,4)),
               pit(cell(3,5)),
               pit(cell(8,6)),
               pit(cell(9,8)),
               pit(cell(13,8)),
               pit(cell(5,10)),
               pit(cell(11,11)),
               pit(cell(7,13))]).

real_world(32,[at(wumpus,cell(8,13)),
               at(gold,cell(26,30)),
               pit(cell(4,1)),
               pit(cell(10,3)),
               pit(cell(18,3)),
               pit(cell(24,4)),
               pit(cell(6,5)),
               pit(cell(12,6)),
               pit(cell(28,6)),
               pit(cell(21,7)),
               pit(cell(21,8)),
               pit(cell(16,9)),
               pit(cell(5,10)),
               pit(cell(12,12)),
               pit(cell(21,12)),
               pit(cell(26,12)),
               pit(cell(4,13)),
               pit(cell(6,13)),
               pit(cell(10,13)),
               pit(cell(13,14)),
               pit(cell(6,15)),
               pit(cell(10,15)),
               pit(cell(29,15)),
               pit(cell(19,16)),
               pit(cell(23,16)),
               pit(cell(8,19)),
               pit(cell(15,19)),
               pit(cell(21,20)),
               pit(cell(25,20)),
               pit(cell(12,21)),
               pit(cell(6,22)),
               pit(cell(15,24)),
               pit(cell(21,24)),
               pit(cell(8,25)),
               pit(cell(28,25)),
               pit(cell(30,25)),
               pit(cell(25,26)),
               pit(cell(5,27)),
               pit(cell(12,28)),
               pit(cell(23,28)),
               pit(cell(8,30)),
               pit(cell(17,30))
              ]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Initial State as Fact                                    %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initial_state(4,State) :-

        State = [
                    
%% No Wumpus or pits on the boundary
                    
                    neg(at(wumpus, cell(0, 1))),
                    neg(at(wumpus, cell(0, 2))),
                    neg(at(wumpus, cell(0, 3))),
                    neg(at(wumpus, cell(0, 4))),
                    neg(at(wumpus, cell(5, 1))),
                    neg(at(wumpus, cell(5, 2))),
                    neg(at(wumpus, cell(5, 3))),
                    neg(at(wumpus, cell(5, 4))),
                    neg(at(wumpus, cell(1, 0))),
                    neg(at(wumpus, cell(2, 0))),
                    neg(at(wumpus, cell(3, 0))),
                    neg(at(wumpus, cell(4, 0))),
                    neg(at(wumpus, cell(1, 5))),
                    neg(at(wumpus, cell(2, 5))),
                    neg(at(wumpus, cell(3, 5))),
                    neg(at(wumpus, cell(4, 5))),
                    neg(pit(cell(0, 1))),
                    neg(pit(cell(0, 2))),
                    neg(pit(cell(0, 3))),
                    neg(pit(cell(0, 4))),
                    neg(pit(cell(5, 1))),
                    neg(pit(cell(5, 2))),
                    neg(pit(cell(5, 3))),
                    neg(pit(cell(5, 4))),
                    neg(pit(cell(1, 0))),
                    neg(pit(cell(2, 0))),
                    neg(pit(cell(3, 0))),
                    neg(pit(cell(4, 0))),
                    neg(pit(cell(1, 5))),
                    neg(pit(cell(2, 5))),
                    neg(pit(cell(3, 5))),
                    neg(pit(cell(4, 5))),
                    
%% Agent is armed
                    
                    carries(agent, arrow),
                    
%% Agent is in the lower left corner
                    
                    at(agent, cell(1, 1)),
                    
%% The Wumpus is out there
                    
                    alive(wumpus) 
                ].


initial_state(8,State) :-
        State = [
                    neg(at(wumpus, cell(0, 1))),
                    neg(at(wumpus, cell(0, 2))),
                    neg(at(wumpus, cell(0, 3))),
                    neg(at(wumpus, cell(0, 4))),
                    neg(at(wumpus, cell(0, 5))),
                    neg(at(wumpus, cell(0, 6))),
                    neg(at(wumpus, cell(0, 7))),
                    neg(at(wumpus, cell(0, 8))),
                    neg(at(wumpus, cell(9, 1))),
                    neg(at(wumpus, cell(9, 2))),
                    neg(at(wumpus, cell(9, 3))),
                    neg(at(wumpus, cell(9, 4))),
                    neg(at(wumpus, cell(9, 5))),
                    neg(at(wumpus, cell(9, 6))),
                    neg(at(wumpus, cell(9, 7))),
                    neg(at(wumpus, cell(9, 8))),
                    neg(at(wumpus, cell(1, 0))),
                    neg(at(wumpus, cell(2, 0))),
                    neg(at(wumpus, cell(3, 0))),
                    neg(at(wumpus, cell(4, 0))),
                    neg(at(wumpus, cell(5, 0))),
                    neg(at(wumpus, cell(6, 0))),
                    neg(at(wumpus, cell(7, 0))),
                    neg(at(wumpus, cell(8, 0))),
                    neg(at(wumpus, cell(1, 9))),
                    neg(at(wumpus, cell(2, 9))),
                    neg(at(wumpus, cell(3, 9))),
                    neg(at(wumpus, cell(4, 9))),
                    neg(at(wumpus, cell(5, 9))),
                    neg(at(wumpus, cell(6, 9))),
                    neg(at(wumpus, cell(7, 9))),
                    neg(at(wumpus, cell(8, 9))),
                    neg(pit(cell(0, 1))),
                    neg(pit(cell(0, 2))),
                    neg(pit(cell(0, 3))),
                    neg(pit(cell(0, 4))),
                    neg(pit(cell(0, 5))),
                    neg(pit(cell(0, 6))),
                    neg(pit(cell(0, 7))),
                    neg(pit(cell(0, 8))),
                    neg(pit(cell(9, 1))),
                    neg(pit(cell(9, 2))),
                    neg(pit(cell(9, 3))),
                    neg(pit(cell(9, 4))),
                    neg(pit(cell(9, 5))),
                    neg(pit(cell(9, 6))),
                    neg(pit(cell(9, 7))),
                    neg(pit(cell(9, 8))),
                    neg(pit(cell(1, 0))),
                    neg(pit(cell(2, 0))),
                    neg(pit(cell(3, 0))),
                    neg(pit(cell(4, 0))),
                    neg(pit(cell(5, 0))),
                    neg(pit(cell(6, 0))),
                    neg(pit(cell(7, 0))),
                    neg(pit(cell(8, 0))),
                    neg(pit(cell(1, 9))),
                    neg(pit(cell(2, 9))),
                    neg(pit(cell(3, 9))),
                    neg(pit(cell(4, 9))),
                    neg(pit(cell(5, 9))),
                    neg(pit(cell(6, 9))),
                    neg(pit(cell(7, 9))),
                    neg(pit(cell(8, 9))),
                    carries(agent, arrow),
                    at(agent, cell(1, 1)),
                    alive(wumpus)
                ].






initial_state(16,State) :-
        State = [
                    neg(at(wumpus, cell(0, 1))),
                    neg(at(wumpus, cell(0, 2))),
                    neg(at(wumpus, cell(0, 3))),
                    neg(at(wumpus, cell(0, 4))),
                    neg(at(wumpus, cell(0, 5))),
                    neg(at(wumpus, cell(0, 6))),
                    neg(at(wumpus, cell(0, 7))),
                    neg(at(wumpus, cell(0, 8))),
                    neg(at(wumpus, cell(0, 9))),
                    neg(at(wumpus, cell(0, 10))),
                    neg(at(wumpus, cell(0, 11))),
                    neg(at(wumpus, cell(0, 12))),
                    neg(at(wumpus, cell(0, 13))),
                    neg(at(wumpus, cell(0, 14))),
                    neg(at(wumpus, cell(0, 15))),
                    neg(at(wumpus, cell(0, 16))),
                    neg(at(wumpus, cell(17, 1))),
                    neg(at(wumpus, cell(17, 2))),
                    neg(at(wumpus, cell(17, 3))),
                    neg(at(wumpus, cell(17, 4))),
                    neg(at(wumpus, cell(17, 5))),
                    neg(at(wumpus, cell(17, 6))),
                    neg(at(wumpus, cell(17, 7))),
                    neg(at(wumpus, cell(17, 8))),
                    neg(at(wumpus, cell(17, 9))),
                    neg(at(wumpus, cell(17, 10))),
                    neg(at(wumpus, cell(17, 11))),
                    neg(at(wumpus, cell(17, 12))),
                    neg(at(wumpus, cell(17, 13))),
                    neg(at(wumpus, cell(17, 14))),
                    neg(at(wumpus, cell(17, 15))),
                    neg(at(wumpus, cell(17, 16))),
                    neg(at(wumpus, cell(1, 0))),
                    neg(at(wumpus, cell(2, 0))),
                    neg(at(wumpus, cell(3, 0))),
                    neg(at(wumpus, cell(4, 0))),
                    neg(at(wumpus, cell(5, 0))),
                    neg(at(wumpus, cell(6, 0))),
                    neg(at(wumpus, cell(7, 0))),
                    neg(at(wumpus, cell(8, 0))),
                    neg(at(wumpus, cell(9, 0))),
                    neg(at(wumpus, cell(10, 0))),
                    neg(at(wumpus, cell(11, 0))),
                    neg(at(wumpus, cell(12, 0))),
                    neg(at(wumpus, cell(13, 0))),
                    neg(at(wumpus, cell(14, 0))),
                    neg(at(wumpus, cell(15, 0))),
                    neg(at(wumpus, cell(16, 0))),
                    neg(at(wumpus, cell(1, 17))),
                    neg(at(wumpus, cell(2, 17))),
                    neg(at(wumpus, cell(3, 17))),
                    neg(at(wumpus, cell(4, 17))),
                    neg(at(wumpus, cell(5, 17))),
                    neg(at(wumpus, cell(6, 17))),
                    neg(at(wumpus, cell(7, 17))),
                    neg(at(wumpus, cell(8, 17))),
                    neg(at(wumpus, cell(9, 17))),
                    neg(at(wumpus, cell(10, 17))),
                    neg(at(wumpus, cell(11, 17))),
                    neg(at(wumpus, cell(12, 17))),
                    neg(at(wumpus, cell(13, 17))),
                    neg(at(wumpus, cell(14, 17))),
                    neg(at(wumpus, cell(15, 17))),
                    neg(at(wumpus, cell(16, 17))),
                    neg(pit(cell(0, 1))),
                    neg(pit(cell(0, 2))),
                    neg(pit(cell(0, 3))),
                    neg(pit(cell(0, 4))),
                    neg(pit(cell(0, 5))),
                    neg(pit(cell(0, 6))),
                    neg(pit(cell(0, 7))),
                    neg(pit(cell(0, 8))),
                    neg(pit(cell(0, 9))),
                    neg(pit(cell(0, 10))),
                    neg(pit(cell(0, 11))),
                    neg(pit(cell(0, 12))),
                    neg(pit(cell(0, 13))),
                    neg(pit(cell(0, 14))),
                    neg(pit(cell(0, 15))),
                    neg(pit(cell(0, 16))),
                    neg(pit(cell(17, 1))),
                    neg(pit(cell(17, 2))),
                    neg(pit(cell(17, 3))),
                    neg(pit(cell(17, 4))),
                    neg(pit(cell(17, 5))),
                    neg(pit(cell(17, 6))),
                    neg(pit(cell(17, 7))),
                    neg(pit(cell(17, 8))),
                    neg(pit(cell(17, 9))),
                    neg(pit(cell(17, 10))),
                    neg(pit(cell(17, 11))),
                    neg(pit(cell(17, 12))),
                    neg(pit(cell(17, 13))),
                    neg(pit(cell(17, 14))),
                    neg(pit(cell(17, 15))),
                    neg(pit(cell(17, 16))),
                    neg(pit(cell(1, 0))),
                    neg(pit(cell(2, 0))),
                    neg(pit(cell(3, 0))),
                    neg(pit(cell(4, 0))),
                    neg(pit(cell(5, 0))),
                    neg(pit(cell(6, 0))),
                    neg(pit(cell(7, 0))),
                    neg(pit(cell(8, 0))),
                    neg(pit(cell(9, 0))),
                    neg(pit(cell(10, 0))),
                    neg(pit(cell(11, 0))),
                    neg(pit(cell(12, 0))),
                    neg(pit(cell(13, 0))),
                    neg(pit(cell(14, 0))),
                    neg(pit(cell(15, 0))),
                    neg(pit(cell(16, 0))),
                    neg(pit(cell(1, 17))),
                    neg(pit(cell(2, 17))),
                    neg(pit(cell(3, 17))),
                    neg(pit(cell(4, 17))),
                    neg(pit(cell(5, 17))),
                    neg(pit(cell(6, 17))),
                    neg(pit(cell(7, 17))),
                    neg(pit(cell(8, 17))),
                    neg(pit(cell(9, 17))),
                    neg(pit(cell(10, 17))),
                    neg(pit(cell(11, 17))),
                    neg(pit(cell(12, 17))),
                    neg(pit(cell(13, 17))),
                    neg(pit(cell(14, 17))),
                    neg(pit(cell(15, 17))),
                    neg(pit(cell(16, 17))),
                    carries(agent, arrow),
                    at(agent, cell(1, 1)),
                    alive(wumpus) 
                ].






initial_state(32,State) :- 
        State = [
                    neg(at(wumpus, cell(0, 1))),
                    neg(at(wumpus, cell(0, 2))),
                    neg(at(wumpus, cell(0, 3))),
                    neg(at(wumpus, cell(0, 4))),
                    neg(at(wumpus, cell(0, 5))),
                    neg(at(wumpus, cell(0, 6))),
                    neg(at(wumpus, cell(0, 7))),
                    neg(at(wumpus, cell(0, 8))),
                    neg(at(wumpus, cell(0, 9))),
                    neg(at(wumpus, cell(0, 10))),
                    neg(at(wumpus, cell(0, 11))),
                    neg(at(wumpus, cell(0, 12))),
                    neg(at(wumpus, cell(0, 13))),
                    neg(at(wumpus, cell(0, 14))),
                    neg(at(wumpus, cell(0, 15))),
                    neg(at(wumpus, cell(0, 16))),
                    neg(at(wumpus, cell(0, 17))),
                    neg(at(wumpus, cell(0, 18))),
                    neg(at(wumpus, cell(0, 19))),
                    neg(at(wumpus, cell(0, 20))),
                    neg(at(wumpus, cell(0, 21))),
                    neg(at(wumpus, cell(0, 22))),
                    neg(at(wumpus, cell(0, 23))),
                    neg(at(wumpus, cell(0, 24))),
                    neg(at(wumpus, cell(0, 25))),
                    neg(at(wumpus, cell(0, 26))),
                    neg(at(wumpus, cell(0, 27))),
                    neg(at(wumpus, cell(0, 28))),
                    neg(at(wumpus, cell(0, 29))),
                    neg(at(wumpus, cell(0, 30))),
                    neg(at(wumpus, cell(0, 31))),
                    neg(at(wumpus, cell(0, 32))),
                    neg(at(wumpus, cell(33, 1))),
                    neg(at(wumpus, cell(33, 2))),
                    neg(at(wumpus, cell(33, 3))),
                    neg(at(wumpus, cell(33, 4))),
                    neg(at(wumpus, cell(33, 5))),
                    neg(at(wumpus, cell(33, 6))),
                    neg(at(wumpus, cell(33, 7))),
                    neg(at(wumpus, cell(33, 8))),
                    neg(at(wumpus, cell(33, 9))),
                    neg(at(wumpus, cell(33, 10))),
                    neg(at(wumpus, cell(33, 11))),
                    neg(at(wumpus, cell(33, 12))),
                    neg(at(wumpus, cell(33, 13))),
                    neg(at(wumpus, cell(33, 14))),
                    neg(at(wumpus, cell(33, 15))),
                    neg(at(wumpus, cell(33, 16))),
                    neg(at(wumpus, cell(33, 17))),
                    neg(at(wumpus, cell(33, 18))),
                    neg(at(wumpus, cell(33, 19))),
                    neg(at(wumpus, cell(33, 20))),
                    neg(at(wumpus, cell(33, 21))),
                    neg(at(wumpus, cell(33, 22))),
                    neg(at(wumpus, cell(33, 23))),
                    neg(at(wumpus, cell(33, 24))),
                    neg(at(wumpus, cell(33, 25))),
                    neg(at(wumpus, cell(33, 26))),
                    neg(at(wumpus, cell(33, 27))),
                    neg(at(wumpus, cell(33, 28))),
                    neg(at(wumpus, cell(33, 29))),
                    neg(at(wumpus, cell(33, 30))),
                    neg(at(wumpus, cell(33, 31))),
                    neg(at(wumpus, cell(33, 32))),
                    neg(at(wumpus, cell(1, 0))),
                    neg(at(wumpus, cell(2, 0))),
                    neg(at(wumpus, cell(3, 0))),
                    neg(at(wumpus, cell(4, 0))),
                    neg(at(wumpus, cell(5, 0))),
                    neg(at(wumpus, cell(6, 0))),
                    neg(at(wumpus, cell(7, 0))),
                    neg(at(wumpus, cell(8, 0))),
                    neg(at(wumpus, cell(9, 0))),
                    neg(at(wumpus, cell(10, 0))),
                    neg(at(wumpus, cell(11, 0))),
                    neg(at(wumpus, cell(12, 0))),
                    neg(at(wumpus, cell(13, 0))),
                    neg(at(wumpus, cell(14, 0))),
                    neg(at(wumpus, cell(15, 0))),
                    neg(at(wumpus, cell(16, 0))),
                    neg(at(wumpus, cell(17, 0))),
                    neg(at(wumpus, cell(18, 0))),
                    neg(at(wumpus, cell(19, 0))),
                    neg(at(wumpus, cell(20, 0))),
                    neg(at(wumpus, cell(21, 0))),
                    neg(at(wumpus, cell(22, 0))),
                    neg(at(wumpus, cell(23, 0))),
                    neg(at(wumpus, cell(24, 0))),
                    neg(at(wumpus, cell(25, 0))),
                    neg(at(wumpus, cell(26, 0))),
                    neg(at(wumpus, cell(27, 0))),
                    neg(at(wumpus, cell(28, 0))),
                    neg(at(wumpus, cell(29, 0))),
                    neg(at(wumpus, cell(30, 0))),
                    neg(at(wumpus, cell(31, 0))),
                    neg(at(wumpus, cell(32, 0))),
                    neg(at(wumpus, cell(1, 33))),
                    neg(at(wumpus, cell(2, 33))),
                    neg(at(wumpus, cell(3, 33))),
                    neg(at(wumpus, cell(4, 33))),
                    neg(at(wumpus, cell(5, 33))),
                    neg(at(wumpus, cell(6, 33))),
                    neg(at(wumpus, cell(7, 33))),
                    neg(at(wumpus, cell(8, 33))),
                    neg(at(wumpus, cell(9, 33))),
                    neg(at(wumpus, cell(10, 33))),
                    neg(at(wumpus, cell(11, 33))),
                    neg(at(wumpus, cell(12, 33))),
                    neg(at(wumpus, cell(13, 33))),
                    neg(at(wumpus, cell(14, 33))),
                    neg(at(wumpus, cell(15, 33))),
                    neg(at(wumpus, cell(16, 33))),
                    neg(at(wumpus, cell(17, 33))),
                    neg(at(wumpus, cell(18, 33))),
                    neg(at(wumpus, cell(19, 33))),
                    neg(at(wumpus, cell(20, 33))),
                    neg(at(wumpus, cell(21, 33))),
                    neg(at(wumpus, cell(22, 33))),
                    neg(at(wumpus, cell(23, 33))),
                    neg(at(wumpus, cell(24, 33))),
                    neg(at(wumpus, cell(25, 33))),
                    neg(at(wumpus, cell(26, 33))),
                    neg(at(wumpus, cell(27, 33))),
                    neg(at(wumpus, cell(28, 33))),
                    neg(at(wumpus, cell(29, 33))),
                    neg(at(wumpus, cell(30, 33))),
                    neg(at(wumpus, cell(31, 33))),
                    neg(at(wumpus, cell(32, 33))),
                    neg(pit(cell(0, 1))),
                    neg(pit(cell(0, 2))),
                    neg(pit(cell(0, 3))),
                    neg(pit(cell(0, 4))),
                    neg(pit(cell(0, 5))),
                    neg(pit(cell(0, 6))),
                    neg(pit(cell(0, 7))),
                    neg(pit(cell(0, 8))),
                    neg(pit(cell(0, 9))),
                    neg(pit(cell(0, 10))),
                    neg(pit(cell(0, 11))),
                    neg(pit(cell(0, 12))),
                    neg(pit(cell(0, 13))),
                    neg(pit(cell(0, 14))),
                    neg(pit(cell(0, 15))),
                    neg(pit(cell(0, 16))),
                    neg(pit(cell(0, 17))),
                    neg(pit(cell(0, 18))),
                    neg(pit(cell(0, 19))),
                    neg(pit(cell(0, 20))),
                    neg(pit(cell(0, 21))),
                    neg(pit(cell(0, 22))),
                    neg(pit(cell(0, 23))),
                    neg(pit(cell(0, 24))),
                    neg(pit(cell(0, 25))),
                    neg(pit(cell(0, 26))),
                    neg(pit(cell(0, 27))),
                    neg(pit(cell(0, 28))),
                    neg(pit(cell(0, 29))),
                    neg(pit(cell(0, 30))),
                    neg(pit(cell(0, 31))),
                    neg(pit(cell(0, 32))),
                    neg(pit(cell(33, 1))),
                    neg(pit(cell(33, 2))),
                    neg(pit(cell(33, 3))),
                    neg(pit(cell(33, 4))),
                    neg(pit(cell(33, 5))),
                    neg(pit(cell(33, 6))),
                    neg(pit(cell(33, 7))),
                    neg(pit(cell(33, 8))),
                    neg(pit(cell(33, 9))),
                    neg(pit(cell(33, 10))),
                    neg(pit(cell(33, 11))),
                    neg(pit(cell(33, 12))),
                    neg(pit(cell(33, 13))),
                    neg(pit(cell(33, 14))),
                    neg(pit(cell(33, 15))),
                    neg(pit(cell(33, 16))),
                    neg(pit(cell(33, 17))),
                    neg(pit(cell(33, 18))),
                    neg(pit(cell(33, 19))),
                    neg(pit(cell(33, 20))),
                    neg(pit(cell(33, 21))),
                    neg(pit(cell(33, 22))),
                    neg(pit(cell(33, 23))),
                    neg(pit(cell(33, 24))),
                    neg(pit(cell(33, 25))),
                    neg(pit(cell(33, 26))),
                    neg(pit(cell(33, 27))),
                    neg(pit(cell(33, 28))),
                    neg(pit(cell(33, 29))),
                    neg(pit(cell(33, 30))),
                    neg(pit(cell(33, 31))),
                    neg(pit(cell(33, 32))),
                    neg(pit(cell(1, 0))),
                    neg(pit(cell(2, 0))),
                    neg(pit(cell(3, 0))),
                    neg(pit(cell(4, 0))),
                    neg(pit(cell(5, 0))),
                    neg(pit(cell(6, 0))),
                    neg(pit(cell(7, 0))),
                    neg(pit(cell(8, 0))),
                    neg(pit(cell(9, 0))),
                    neg(pit(cell(10, 0))),
                    neg(pit(cell(11, 0))),
                    neg(pit(cell(12, 0))),
                    neg(pit(cell(13, 0))),
                    neg(pit(cell(14, 0))),
                    neg(pit(cell(15, 0))),
                    neg(pit(cell(16, 0))),
                    neg(pit(cell(17, 0))),
                    neg(pit(cell(18, 0))),
                    neg(pit(cell(19, 0))),
                    neg(pit(cell(20, 0))),
                    neg(pit(cell(21, 0))),
                    neg(pit(cell(22, 0))),
                    neg(pit(cell(23, 0))),
                    neg(pit(cell(24, 0))),
                    neg(pit(cell(25, 0))),
                    neg(pit(cell(26, 0))),
                    neg(pit(cell(27, 0))),
                    neg(pit(cell(28, 0))),
                    neg(pit(cell(29, 0))),
                    neg(pit(cell(30, 0))),
                    neg(pit(cell(31, 0))),
                    neg(pit(cell(32, 0))),
                    neg(pit(cell(1, 33))),
                    neg(pit(cell(2, 33))),
                    neg(pit(cell(3, 33))),
                    neg(pit(cell(4, 33))),
                    neg(pit(cell(5, 33))),
                    neg(pit(cell(6, 33))),
                    neg(pit(cell(7, 33))),
                    neg(pit(cell(8, 33))),
                    neg(pit(cell(9, 33))),
                    neg(pit(cell(10, 33))),
                    neg(pit(cell(11, 33))),
                    neg(pit(cell(12, 33))),
                    neg(pit(cell(13, 33))),
                    neg(pit(cell(14, 33))),
                    neg(pit(cell(15, 33))),
                    neg(pit(cell(16, 33))),
                    neg(pit(cell(17, 33))),
                    neg(pit(cell(18, 33))),
                    neg(pit(cell(19, 33))),
                    neg(pit(cell(20, 33))),
                    neg(pit(cell(21, 33))),
                    neg(pit(cell(22, 33))),
                    neg(pit(cell(23, 33))),
                    neg(pit(cell(24, 33))),
                    neg(pit(cell(25, 33))),
                    neg(pit(cell(26, 33))),
                    neg(pit(cell(27, 33))),
                    neg(pit(cell(28, 33))),
                    neg(pit(cell(29, 33))),
                    neg(pit(cell(30, 33))),
                    neg(pit(cell(31, 33))),
                    neg(pit(cell(32, 33))),
                    carries(agent, arrow),
                    at(agent, cell(1, 1)),
                    alive(wumpus)
                ].

                                       

