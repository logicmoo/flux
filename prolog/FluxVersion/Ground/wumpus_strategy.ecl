:-use_module(flux).

%% Choose a Wumpus World

%% :-use_module(wumpus_world_small).
:-use_module(wumpus_world_big).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                           %%
%%  Main Loop                                                %%
%%                                                           %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main :-
        init,
        holds([at(agent,Cell)]),
        sense,
        !,
	main_loop([Cell],[Cell]).

main_loop(Visited,Wayback) :-
        ( holds([at(agent,Cell),at(gold,Cell)]) ->
            execute(grab),
            writeln(grab),
            go_home(Wayback)
        ;
            ( execute(shoot) -> 
                writeln(shoot),
                main_loop(Visited,Wayback)
            ;
                ( explore(Visited,Cell2) ->
                    holds([at(agent,Cell1)]),
                    execute(go(Cell1,Cell2)),
                    writeln(Cell1-Cell2),
                    sense,
                    main_loop([Cell2|Visited],[Cell2|Wayback])
                ;
                    go_back(Wayback,NewWayback),
                    main_loop(Visited,NewWayback) ) ) ).


%% Go back one step

go_back(Wayback,NewWayback) :-
        Wayback = [Cell1,Cell2|Rest],
        execute(go(Cell1,Cell2)),
        NewWayback = [Cell2|Rest].

%% Go back where you came from

go_home(Wayback) :-
            ( fromto(Wayback,In,Out,[_InitialCell]) do
                In = [Cell1,Cell2|Rest],
                execute(go(Cell1,Cell2)),
                Out = [Cell2|Rest] ).

%% Find a safe cell you have not visited yet

explore(Visited,Cell2) :-
        
%% Cell2 is safe, wumpus not there, or dead:
        
        ( holds([
                    at(agent,Cell1),
                    connected(Cell1,Cell2),
                    neg(pit(Cell2)),
                    neg(at(wumpus,Cell2))])
        ;
          holds([
                    at(agent,Cell1),
                    connected(Cell1,Cell2),
                    neg(pit(Cell2)),
                    neg(alive(wumpus))]) ),

        \+ member(Cell2,Visited).

%% Sensing

sense :-
        holds([breeze(_)]),
        holds([glitter(_)]),
        holds([stench(_)]).
        

