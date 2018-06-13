:- dynamic current_state/1.

init_simulator :- init_scenario,
                  retract_all(current_state(_)), assert(current_state([])).

:- dynamic wumpus/2,pit/2,gold/2.

init_scenario :-

        retract_all(wumpus(_,_)), retract_all(pit(_,_)),retract_all(gold(_,_)), 
        
        dimension(Dim),
        
        real_world(Dim,World),
        
        ( foreach(Element,World) do
            ( Element = at(wumpus,cell(X,Y)) ->
                assert(wumpus(X,Y))
            ;
                ( Element = at(gold,cell(X,Y)) ->
                    assert(gold(X,Y))
                ;
                    Element = pit(cell(X,Y)),
                    assert(pit(X,Y)) ) ) ).
        
        
        

%% init_scenario :-
%% 
%%    retract_all(wumpus(_,_)), retract_all(pit(_,_)), retract_all(gold(_,_)),
%% 
%%    xdim(XD), ydim(YD),
%% 
%%    random(N1), random(N2), XW is N1 mod XD + 1, YW is N2 mod YD + 1,
%%    ( XW=1, YW=1 -> true ; assert(wumpus(XW,YW)), writeln(wumpus(XW,YW)) ),
%% 
%%    random(N3), random(N4), XG is N3 mod XD + 1, YG is N4 mod YD + 1,
%%    assert(gold(XG,YG)), writeln(gold(XG,YG)),
%% 
%%    no_of_random_pits(P), create_pits(P).
%% 
%% create_pits(0) :- !.
%% create_pits(M) :-
%%    xdim(XD), ydim(YD),
%%    random(N1), random(N2), XP is N1 mod XD + 1, YP is N2 mod YD + 1,
%%    ( XP+YP < 4 -> create_pits(M) ; assert(pit(XP,YP)), writeln(pit(XP,YP)) ),
%%    M1 is M-1, create_pits(M1).



















perform(turn, []) :-
	write('turn'), nl,
	current_state([at(X,Y),facing(D)]),
	retract(current_state([at(X,Y),facing(D)])),
	( D < 4 -> D1 is D+1 ; D1 is 1 ),
	assert(current_state([at(X,Y),facing(D1)])).

perform(enter, [Breeze,Stench,Glitter]) :-
	write('enter'), nl,
	current_state(Z),
	retract(current_state(Z)),
	assert(current_state([at(1,1),facing(1)])),
	( gold(1,1) -> Glitter = true ; Glitter = false ),
	( (wumpus(1,2) ; wumpus(2,1)) -> Stench = true ;
	    Stench = false ),
	( (pit(2,1) ; pit(1,2)) -> Breeze = true ;
	    Breeze = false ).

perform(exit, []) :-
	write('exit'), nl,
	current_state([at(X,Y),facing(D)]),
	retract(current_state([at(X,Y),facing(D)])),
	assert(current_state([])).

perform(grab, []) :-
	write('grab'), nl.

perform(shoot, [Scream]) :-
	write('shoot'), nl,
	current_state([at(X,Y),facing(D)]),
	wumpus(WX, WY),
	( in_direction(X, Y, D, WX, WY), Scream = true ; Scream = false ).

perform(go, [Breeze,Stench,Glitter]) :-
	write('go'), nl,
	current_state([at(X,Y),facing(D)]),
	retract(current_state([at(X,Y),facing(D)])),
	( D = 1 -> X1 is X, Y1 is Y+1 ;
	  D = 3 -> X1 is X, Y1 is Y-1 ;
	  D = 2 -> X1 is X+1, Y1 is Y ;
	  D = 4 -> X1 is X-1, Y1 is Y ),
	assert(current_state([at(X1,Y1),facing(D)])),
	( gold(X1,Y1) -> Glitter = true ; Glitter = false ),
	X_east is X1+1, X_west is X1-1, Y_north is Y1+1, Y_south is Y1-1,
	( (wumpus(X_east,Y1) ; wumpus(X1,Y_north) ;
           wumpus(X_west,Y1) ; wumpus(X1,Y_south)) -> Stench = true ;
	    Stench = false ),
	( (pit(X_east,Y1) ; pit(X1,Y_north) ;
           pit(X_west,Y1) ; pit(X1,Y_south)) -> Breeze = true ;
	    Breeze = false ).



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