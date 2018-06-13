
%%% The following code has been produced by the CHR compiler


:- ( current_module(chr) -> true ; use_module(library(chr)) ).

:- get_flag(variable_names, Val), setval(variable_names_flag, Val), set_flag(variable_names, off).
eq(_25428, _25431, _25434) :- functor(_25428, _25446, _25449), functor(_25431, _25461, _25464), (_25446 = _25461, _25449 = _25464 -> _25428 =.. [_25487|_25489], _25431 =.. [_25496|_25498], and_eq(_25489, _25498, _25434) ; _25434 = (0 #\= 0)).
neq(_25973, _25976) :- or_neq(exists, _25973, _25976).
neq(_26004, _26007, _26010) :- or_neq_c(exists, _26004, _26007, _26010).
neq_all(_26042, _26045) :- or_neq(forall, _26042, _26045).
neq_all(_26073, _26076, _26079) :- or_neq_c(forall, _26073, _26076, _26079).
or_neq(_26111, _26114, _26117) :- functor(_26114, _26129, _26132), functor(_26117, _26144, _26147), (_26129 = _26144, _26132 = _26147 -> _26114 =.. [_26170|_26172], _26117 =.. [_26179|_26181], or_neq(_26111, _26172, _26181, _26193), call(_26193) ; true).
or_neq_c(_26658, _26661, _26664, _26667) :- functor(_26661, _26680, _26683), functor(_26664, _26695, _26698), (_26680 = _26695, _26683 = _26698 -> _26661 =.. [_26721|_26723], _26664 =.. [_26730|_26732], or_neq(_26658, _26723, _26732, _26667) ; _26667 = (0 #= 0)).
or_neq(_27236, [], [], 0 #\= 0).
or_neq(_27324, [_27329|_27330], [_27335|_27336], _27339) :- or_neq(_27324, _27330, _27336, _27356), (_27324 = forall, var(_27329), \+ is_domain(_27329) -> (binding(_27329, _27330, _27336, _27395) -> _27339 = #\/(_27335 #\= _27395, _27356) ; _27339 = _27356) ; _27339 = #\/(_27329 #\= _27335, _27356)).
binding(_27952, [_27957|_27958], [_27963|_27964], _27967) :- _27952 == _27957 -> _27967 = _27963 ; binding(_27952, _27958, _27964, _27967).
and_eq([], [], 0 #= 0).
and_eq([_28101|_28102], [_28107|_28108], _28111) :- and_eq(_28102, _28108, _28125), _28111 = #/\(_28101 #= _28107, _28125).
or_and_eq([], 0 #\= 0).
or_and_eq([_28427|_28428], #\/(_28431, _28435)) :- (_28427 = eq(_28447, _28450) -> and_eq(_28447, _28450, _28431) ; _28427 = neq(_28447, _28450), or_neq(exists, _28447, _28450, _28431)), or_and_eq(_28428, _28435).
inst(_28848, _28851) :- \+ (term_variables(_28848, _28864), term_variables(_28851, _28875), bound_free(_28875, _28864, _28888, _28891), copy_term_vars(_28891, _28851, _28906), \+ no_global_bindings(_28848 = _28906, _28888)).
copy_fluent(_29230, _29233, _29236, _29239) :- term_variables(_29230, _29252), bound_free(_29252, [], _29271, _29267), copy_term_vars(_29267, [_29230, _29233], [_29236, _29239]).
bound_free([], _29577, _29577, []).
bound_free([_29600|_29601], _29604, _29607, _29610) :- bound_free(_29601, _29604, _29625, _29628), (is_domain(_29600) -> _29607 = [_29600|_29625], _29610 = _29628 ; _29607 = _29625, _29610 = [_29600|_29628]).
member(_30026, [_30026|_30031], _30031).
member(_30049, [_30054|_30055], [_30054|_30060]) :- member(_30049, _30055, _30060).
not_holds(A, B) :-
	'CHRgen_num'(C),
	coca(add_one_constraint(C, not_holds(A, B))),
	'CHRnot_holds_2'(not_holds(A, B), D, E, C).



%%% Rules handling for not_holds / 2

'CHRnot_holds_2'(not_holds(A, B), C, D, E) :-
	(
	    'CHRnonvar'(C)
	;
	    'CHRalready_in'('CHRnot_holds_2'(not_holds(A, B), C, D, E)),
	    coca(already_in)
	),
	!.
'CHRnot_holds_2'(not_holds(A, [B|C]), D, E, F) ?-
	coca(try_rule(F, not_holds(A, [B|C]), anonymous("0"), not_holds(G, [H|I]), replacement, true, (neq(G, H), not_holds(G, I)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("0"))),
	neq(A, B),
	not_holds(A, C).
'CHRnot_holds_2'(not_holds(A, []), B, C, D) ?-
	coca(try_rule(D, not_holds(A, []), anonymous("1"), not_holds(E, []), replacement, true, true)),
	!,
	'CHRkill'(B),
	coca(fired_rule(anonymous("1"))).
'CHRnot_holds_2'(not_holds(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRnot_holds_2__46'(F, [B], [G, H], I),
	coca(try_double(E, not_holds(A, B), I, all_not_holds(H, G, B), not_holds(J, K), all_not_holds(L, M, K), keep_second, (copy_fluent(L, M, N, O), N = J, \+ call(#\+(O))), true, anonymous("13"))),
	no_delayed_goals((copy_fluent(H, G, P, Q), P = A, \+ call(#\+(Q)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("13"))).
'CHRnot_holds_2'(not_holds(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRnot_holds_2__47'(F, [B], [G], H),
	coca(try_double(E, not_holds(A, B), H, cancel(G, B), not_holds(I, J), cancel(K, J), keep_second, \+ K \= I, true, anonymous("39"))),
	no_delayed_goals(\+ G \= A),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("39"))).
'CHRnot_holds_2'(not_holds(A, B), C, D, E) :-
	'CHRnot_holds_2__45'(not_holds(A, B), C, D, E).
'CHRnot_holds_2__46'(['CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRnot_holds_2__46'([A|B], C, D, E) :-
	'CHRnot_holds_2__46'(B, C, D, E).
:- set_flag('CHRnot_holds_2__46' / 4, leash, notrace).
'CHRnot_holds_2__47'(['CHRcancel_2'(cancel(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRnot_holds_2__47'([A|B], C, D, E) :-
	'CHRnot_holds_2__47'(B, C, D, E).
:- set_flag('CHRnot_holds_2__47' / 4, leash, notrace).
:- set_flag('CHRnot_holds_2' / 4, leash, notrace).
:- current_macro('CHRnot_holds_2' / 4, _31937, _31938, _31939) -> true ; define_macro('CHRnot_holds_2' / 4, tr_chr / 2, [write]).
'CHRnot_holds_2__45'(A, B, C, D) :-
	'CHRnot_holds_2__48'(A, B, C, D).
:- set_flag('CHRnot_holds_2__45' / 4, leash, notrace).
'CHRnot_holds_2__48'(not_holds(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRnot_holds_2__48__49'(F, C, not_holds(A, B), D, E).
'CHRnot_holds_2__48'(not_holds(A, B), C, D, E) :-
	'CHRnot_holds_2__48__50'(not_holds(A, B), C, D, E).
:- set_flag('CHRnot_holds_2__48' / 4, leash, notrace).
'CHRnot_holds_2__48__49'(['CHRor_holds_2'(or_holds(A, B), C, D, E)|F], G, not_holds(H, B), I, J) ?-
	'CHRvar'(C),
	coca(try_double(J, not_holds(H, B), E, or_holds(A, B), not_holds(K, L), or_holds(M, L), keep_first, (member(N, M, O), K == N), or_holds(O, L), anonymous("28"))),
	no_delayed_goals((member(P, A, Q), H == P)),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("28"))),
	'CHRnot_holds_2__48__49'(F, G, not_holds(H, B), I, J),
	or_holds(Q, B).
'CHRnot_holds_2__48__49'([A|B], C, D, E, F) :-
	'CHRnot_holds_2__48__49'(B, C, D, E, F).
'CHRnot_holds_2__48__49'([], A, B, C, D) :-
	'CHRnot_holds_2__48__50'(B, A, C, D).
:- set_flag('CHRnot_holds_2__48__49' / 5, leash, notrace).
'CHRnot_holds_2__48__50'(not_holds(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRnot_holds_2__48__50__51'(F, C, not_holds(A, B), D, E).
'CHRnot_holds_2__48__50'(not_holds(A, B), C, D, E) :-
	'CHRnot_holds_2__48__50__52'(not_holds(A, B), C, D, E).
:- set_flag('CHRnot_holds_2__48__50' / 4, leash, notrace).
'CHRnot_holds_2__48__50__51'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, not_holds(I, C), J, K) ?-
	'CHRvar'(D),
	coca(try_double(K, not_holds(I, C), F, if_then_or_holds(A, B, C), not_holds(L, M), if_then_or_holds(N, O, M), keep_first, L == N, true, anonymous("37"))),
	no_delayed_goals(I == A),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("37"))),
	'CHRnot_holds_2__48__50__51'(G, H, not_holds(I, C), J, K).
'CHRnot_holds_2__48__50__51'([A|B], C, D, E, F) :-
	'CHRnot_holds_2__48__50__51'(B, C, D, E, F).
'CHRnot_holds_2__48__50__51'([], A, B, C, D) :-
	'CHRnot_holds_2__48__50__52'(B, A, C, D).
:- set_flag('CHRnot_holds_2__48__50__51' / 5, leash, notrace).
'CHRnot_holds_2__48__50__52'(not_holds(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRnot_holds_2__48__50__52__53'(F, C, not_holds(A, B), D, E).
'CHRnot_holds_2__48__50__52'(not_holds(A, B), C, D, E) :-
	'CHRnot_holds_2__48__50__52__54'(not_holds(A, B), C, D, E).
:- set_flag('CHRnot_holds_2__48__50__52' / 4, leash, notrace).
'CHRnot_holds_2__48__50__52__53'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, not_holds(I, C), J, K) ?-
	'CHRvar'(D),
	coca(try_double(K, not_holds(I, C), F, if_then_or_holds(A, B, C), not_holds(L, M), if_then_or_holds(N, O, M), keep_first, (member(P, O, Q), L == P), if_then_or_holds(N, Q, M), anonymous("38"))),
	no_delayed_goals((member(R, B, S), I == R)),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("38"))),
	'CHRnot_holds_2__48__50__52__53'(G, H, not_holds(I, C), J, K),
	if_then_or_holds(A, S, C).
'CHRnot_holds_2__48__50__52__53'([A|B], C, D, E, F) :-
	'CHRnot_holds_2__48__50__52__53'(B, C, D, E, F).
'CHRnot_holds_2__48__50__52__53'([], A, B, C, D) :-
	'CHRnot_holds_2__48__50__52__54'(B, A, C, D).
:- set_flag('CHRnot_holds_2__48__50__52__53' / 5, leash, notrace).
'CHRnot_holds_2__48__50__52__54'(not_holds(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRnot_holds_2__48__50__52__54__55'(F, C, not_holds(A, B), D, E).
'CHRnot_holds_2__48__50__52__54'(not_holds(A, B), C, D, E) :-
	'CHRnot_holds_2__48__50__52__54__56'(not_holds(A, B), C, D, E).
:- set_flag('CHRnot_holds_2__48__50__52__54' / 4, leash, notrace).
'CHRnot_holds_2__48__50__52__54__55'(['CHRall_holds_3'(all_holds(A, B, C), D, E, F)|G], H, not_holds(I, C), J, K) ?-
	'CHRvar'(D),
	'CHRcheck_and_mark_applied'(anonymous("6"), H, D, J, E),
	coca(try_double(K, not_holds(I, C), F, all_holds(A, B, C), not_holds(L, M), all_holds(N, O, M), augmentation, copy_fluent(N, O, P, Q), (P = L, call(#\+(Q))), anonymous("6"))),
	no_delayed_goals(copy_fluent(A, B, R, S)),
	!,
	coca(fired_rule(anonymous("6"))),
	'CHRnot_holds_2__48__50__52__54__55'(G, H, not_holds(I, C), J, K),
	R = I,
	call(#\+(S)).
'CHRnot_holds_2__48__50__52__54__55'([A|B], C, D, E, F) :-
	'CHRnot_holds_2__48__50__52__54__55'(B, C, D, E, F).
'CHRnot_holds_2__48__50__52__54__55'([], A, B, C, D) :-
	'CHRnot_holds_2__48__50__52__54__56'(B, A, C, D).
:- set_flag('CHRnot_holds_2__48__50__52__54__55' / 5, leash, notrace).
'CHRnot_holds_2__48__50__52__54__56'(not_holds(A, B), C, D, E) :-
	(
	    'CHRvar'(C)
	->
	    'CHRdelay'([C, not_holds(A, B)], 'CHRnot_holds_2'(not_holds(A, B), C, D, E))
	;
	    true
	).
:- set_flag('CHRnot_holds_2__48__50__52__54__56' / 4, leash, notrace).
not_holds_all(A, B) :-
	'CHRgen_num'(C),
	coca(add_one_constraint(C, not_holds_all(A, B))),
	'CHRnot_holds_all_2'(not_holds_all(A, B), D, E, C).



%%% Rules handling for not_holds_all / 2

'CHRnot_holds_all_2'(not_holds_all(A, B), C, D, E) :-
	(
	    'CHRnonvar'(C)
	;
	    'CHRalready_in'('CHRnot_holds_all_2'(not_holds_all(A, B), C, D, E)),
	    coca(already_in)
	),
	!.
'CHRnot_holds_all_2'(not_holds_all(A, B), C, D, E) ?-
	coca(try_rule(E, not_holds_all(A, B), anonymous("11"), not_holds_all(F, G), replacement, true, all_not_holds(F, 0 #= 0, G))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("11"))),
	all_not_holds(A, 0 #= 0, B).
'CHRnot_holds_all_2'(not_holds_all(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRnot_holds_all_2__58'(F, [B], [G], H),
	coca(try_double(E, not_holds_all(A, B), H, cancel(G, B), not_holds_all(I, J), cancel(K, J), keep_second, \+ K \= I, true, anonymous("40"))),
	no_delayed_goals(\+ G \= A),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("40"))).
'CHRnot_holds_all_2'(not_holds_all(A, B), C, D, E) :-
	'CHRnot_holds_all_2__57'(not_holds_all(A, B), C, D, E).
'CHRnot_holds_all_2__58'(['CHRcancel_2'(cancel(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRnot_holds_all_2__58'([A|B], C, D, E) :-
	'CHRnot_holds_all_2__58'(B, C, D, E).
:- set_flag('CHRnot_holds_all_2__58' / 4, leash, notrace).
:- set_flag('CHRnot_holds_all_2' / 4, leash, notrace).
:- current_macro('CHRnot_holds_all_2' / 4, _35272, _35273, _35274) -> true ; define_macro('CHRnot_holds_all_2' / 4, tr_chr / 2, [write]).
'CHRnot_holds_all_2__57'(A, B, C, D) :-
	'CHRnot_holds_all_2__59'(A, B, C, D).
:- set_flag('CHRnot_holds_all_2__57' / 4, leash, notrace).
'CHRnot_holds_all_2__59'(not_holds_all(A, B), C, D, E) :-
	(
	    'CHRvar'(C)
	->
	    'CHRdelay'([C, not_holds_all(A, B)], 'CHRnot_holds_all_2'(not_holds_all(A, B), C, D, E))
	;
	    true
	).
:- set_flag('CHRnot_holds_all_2__59' / 4, leash, notrace).
duplicate_free(A) :-
	'CHRgen_num'(B),
	coca(add_one_constraint(B, duplicate_free(A))),
	'CHRduplicate_free_1'(duplicate_free(A), C, D, B).



%%% Rules handling for duplicate_free / 1

'CHRduplicate_free_1'(duplicate_free(A), B, C, D) :-
	(
	    'CHRnonvar'(B)
	;
	    'CHRalready_in'('CHRduplicate_free_1'(duplicate_free(A), B, C, D)),
	    coca(already_in)
	),
	!.
'CHRduplicate_free_1'(duplicate_free([A|B]), C, D, E) ?-
	coca(try_rule(E, duplicate_free([A|B]), anonymous("2"), duplicate_free([F|G]), replacement, true, (not_holds(F, G), duplicate_free(G)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("2"))),
	not_holds(A, B),
	duplicate_free(B).
'CHRduplicate_free_1'(duplicate_free([]), A, B, C) ?-
	coca(try_rule(C, duplicate_free([]), anonymous("3"), duplicate_free([]), replacement, true, true)),
	!,
	'CHRkill'(A),
	coca(fired_rule(anonymous("3"))).
'CHRduplicate_free_1'(duplicate_free(A), B, C, D) :-
	'CHRduplicate_free_1__60'(duplicate_free(A), B, C, D).
:- set_flag('CHRduplicate_free_1' / 4, leash, notrace).
:- current_macro('CHRduplicate_free_1' / 4, _36069, _36070, _36071) -> true ; define_macro('CHRduplicate_free_1' / 4, tr_chr / 2, [write]).
'CHRduplicate_free_1__60'(A, B, C, D) :-
	'CHRduplicate_free_1__61'(A, B, C, D).
:- set_flag('CHRduplicate_free_1__60' / 4, leash, notrace).
'CHRduplicate_free_1__61'(duplicate_free(A), B, C, D) :-
	(
	    'CHRvar'(B)
	->
	    'CHRdelay'([B, duplicate_free(A)], 'CHRduplicate_free_1'(duplicate_free(A), B, C, D))
	;
	    true
	).
:- set_flag('CHRduplicate_free_1__61' / 4, leash, notrace).
or_holds(A, B) :-
	'CHRgen_num'(C),
	coca(add_one_constraint(C, or_holds(A, B))),
	'CHRor_holds_2'(or_holds(A, B), D, E, C).



%%% Rules handling for or_holds / 2

'CHRor_holds_2'(or_holds(A, B), C, D, E) :-
	(
	    'CHRnonvar'(C)
	;
	    'CHRalready_in'('CHRor_holds_2'(or_holds(A, B), C, D, E)),
	    coca(already_in)
	),
	!.
'CHRor_holds_2'(or_holds([A], B), C, D, E) ?-
	coca(try_rule(E, or_holds([A], B), anonymous("18"), or_holds([F], G), replacement, (F \= eq(H, I), F \= neq(J, K)), holds(F, G))),
	no_delayed_goals((A \= eq(L, M), A \= neq(N, O))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("18"))),
	holds(A, B).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	coca(try_rule(E, or_holds(A, B), anonymous("19"), or_holds(F, G), replacement, \+ (member(H, F), H \= eq(I, J), H \= neq(K, L)), (or_and_eq(F, M), call(M)))),
	no_delayed_goals(\+ (member(N, A), N \= eq(O, P), N \= neq(Q, R))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("19"))),
	or_and_eq(A, S),
	call(S).
'CHRor_holds_2'(or_holds(A, []), B, C, D) ?-
	coca(try_rule(D, or_holds(A, []), anonymous("20"), or_holds(E, []), replacement, (member(F, E, G), F \= eq(H, I), F \= neq(J, K)), or_holds(G, []))),
	no_delayed_goals((member(L, A, M), L \= eq(N, O), L \= neq(P, Q))),
	!,
	'CHRkill'(B),
	coca(fired_rule(anonymous("20"))),
	or_holds(M, []).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	coca(try_rule(E, or_holds(A, B), anonymous("21"), or_holds(F, G), replacement, (member(eq(H, I), F), or_neq(exists, H, I, J), \+ call(J)), true)),
	no_delayed_goals((member(eq(K, L), A), or_neq(exists, K, L, M), \+ call(M))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("21"))).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	coca(try_rule(E, or_holds(A, B), anonymous("22"), or_holds(F, G), replacement, (member(neq(H, I), F), and_eq(H, I, J), \+ call(J)), true)),
	no_delayed_goals((member(neq(K, L), A), and_eq(K, L, M), \+ call(M))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("22"))).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	coca(try_rule(E, or_holds(A, B), anonymous("23"), or_holds(F, G), replacement, (member(eq(H, I), F, J), \+ (and_eq(H, I, K), call(K))), or_holds(J, G))),
	no_delayed_goals((member(eq(L, M), A, N), \+ (and_eq(L, M, O), call(O)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("23"))),
	or_holds(N, B).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	coca(try_rule(E, or_holds(A, B), anonymous("24"), or_holds(F, G), replacement, (member(neq(H, I), F, J), \+ (or_neq(exists, H, I, K), call(K))), or_holds(J, G))),
	no_delayed_goals((member(neq(L, M), A, N), \+ (or_neq(exists, L, M, O), call(O)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("24"))),
	or_holds(N, B).
'CHRor_holds_2'(or_holds(A, [B|C]), D, E, F) ?-
	coca(try_rule(F, or_holds(A, [B|C]), anonymous("25"), or_holds(G, [H|I]), replacement, true, or_holds(G, [], [H|I]))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("25"))),
	or_holds(A, [], [B|C]).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRor_holds_2__63'(F, [B], [G, H], I),
	coca(try_double(E, or_holds(A, B), I, all_holds(H, G, B), or_holds(J, K), all_holds(L, M, K), keep_second, (member(N, J), copy_fluent(L, M, O, P), O = N, \+ call(#\+(P))), true, anonymous("8"))),
	no_delayed_goals((member(Q, A), copy_fluent(H, G, R, S), R = Q, \+ call(#\+(S)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("8"))).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRor_holds_2__64'(F, [B], [G, H], I),
	coca(try_double(E, or_holds(A, B), I, all_not_holds(H, G, B), or_holds(J, K), all_not_holds(L, M, K), keep_second, (member(N, J, O), copy_fluent(L, M, P, Q), P = N, \+ call(#\+(Q))), or_holds(O, K), anonymous("14"))),
	no_delayed_goals((member(R, A, S), copy_fluent(H, G, T, U), T = R, \+ call(#\+(U)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("14"))),
	or_holds(S, B).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRor_holds_2__65'(F, [B], [G], H),
	coca(try_double(E, or_holds(A, B), H, not_holds(G, B), or_holds(I, J), not_holds(K, J), keep_second, (member(L, I, M), K == L), or_holds(M, J), anonymous("28"))),
	no_delayed_goals((member(N, A, O), G == N)),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("28"))),
	or_holds(O, B).
'CHRor_holds_2'(or_holds(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRor_holds_2__66'(F, [B], [G], H),
	coca(try_double(E, or_holds(A, B), H, cancel(G, B), or_holds(I, J), cancel(K, J), keep_second, (member(L, I), \+ K \= L), true, anonymous("41"))),
	no_delayed_goals((member(M, A), \+ G \= M)),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("41"))).
'CHRor_holds_2'(or_holds(A, B), C, D, E) :-
	'CHRor_holds_2__62'(or_holds(A, B), C, D, E).
'CHRor_holds_2__63'(['CHRall_holds_3'(all_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRor_holds_2__63'([A|B], C, D, E) :-
	'CHRor_holds_2__63'(B, C, D, E).
:- set_flag('CHRor_holds_2__63' / 4, leash, notrace).
'CHRor_holds_2__64'(['CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRor_holds_2__64'([A|B], C, D, E) :-
	'CHRor_holds_2__64'(B, C, D, E).
:- set_flag('CHRor_holds_2__64' / 4, leash, notrace).
'CHRor_holds_2__65'(['CHRnot_holds_2'(not_holds(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRor_holds_2__65'([A|B], C, D, E) :-
	'CHRor_holds_2__65'(B, C, D, E).
:- set_flag('CHRor_holds_2__65' / 4, leash, notrace).
'CHRor_holds_2__66'(['CHRcancel_2'(cancel(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRor_holds_2__66'([A|B], C, D, E) :-
	'CHRor_holds_2__66'(B, C, D, E).
:- set_flag('CHRor_holds_2__66' / 4, leash, notrace).
:- set_flag('CHRor_holds_2' / 4, leash, notrace).
:- current_macro('CHRor_holds_2' / 4, _39990, _39991, _39992) -> true ; define_macro('CHRor_holds_2' / 4, tr_chr / 2, [write]).
'CHRor_holds_2__62'(A, B, C, D) :-
	'CHRor_holds_2__67'(A, B, C, D).
:- set_flag('CHRor_holds_2__62' / 4, leash, notrace).
'CHRor_holds_2__67'(or_holds(A, B), C, D, E) :-
	(
	    'CHRvar'(C)
	->
	    'CHRdelay'([C, or_holds(A, B)], 'CHRor_holds_2'(or_holds(A, B), C, D, E))
	;
	    true
	).
:- set_flag('CHRor_holds_2__67' / 4, leash, notrace).
or_holds(A, B, C) :-
	'CHRgen_num'(D),
	coca(add_one_constraint(D, or_holds(A, B, C))),
	'CHRor_holds_3'(or_holds(A, B, C), E, F, D).



%%% Rules handling for or_holds / 3

'CHRor_holds_3'(or_holds(A, B, C), D, E, F) :-
	(
	    'CHRnonvar'(D)
	;
	    'CHRalready_in'('CHRor_holds_3'(or_holds(A, B, C), D, E, F)),
	    coca(already_in)
	),
	!.
'CHRor_holds_3'(or_holds([A|B], C, [D|E]), F, G, H) ?-
	coca(try_rule(H, or_holds([A|B], C, [D|E]), anonymous("26"), or_holds([I|J], K, [L|M]), replacement, true, I == L -> true ; I \= L -> or_holds(J, [I|K], [L|M]) ; (I =.. [N|O], L =.. [P|Q], or_holds(J, [eq(O, Q), I|K], [L|M])))),
	!,
	'CHRkill'(F),
	coca(fired_rule(anonymous("26"))),
	(
	    A == D
	->
	    true
	;
	    (
		A \= D
	    ->
		or_holds(B, [A|C], [D|E])
	    ;
		A =.. [R|S],
		D =.. [T|U],
		or_holds(B, [eq(S, U), A|C], [D|E])
	    )
	).
'CHRor_holds_3'(or_holds([], A, [B|C]), D, E, F) ?-
	coca(try_rule(F, or_holds([], A, [B|C]), anonymous("27"), or_holds([], G, [H|I]), replacement, true, or_holds(G, I))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("27"))),
	or_holds(A, C).
'CHRor_holds_3'(or_holds(A, B, C), D, E, F) :-
	'CHRor_holds_3__68'(or_holds(A, B, C), D, E, F).
:- set_flag('CHRor_holds_3' / 4, leash, notrace).
:- current_macro('CHRor_holds_3' / 4, _40931, _40932, _40933) -> true ; define_macro('CHRor_holds_3' / 4, tr_chr / 2, [write]).
'CHRor_holds_3__68'(A, B, C, D) :-
	'CHRor_holds_3__69'(A, B, C, D).
:- set_flag('CHRor_holds_3__68' / 4, leash, notrace).
'CHRor_holds_3__69'(or_holds(A, B, C), D, E, F) :-
	(
	    'CHRvar'(D)
	->
	    'CHRdelay'([D, or_holds(A, B, C)], 'CHRor_holds_3'(or_holds(A, B, C), D, E, F))
	;
	    true
	).
:- set_flag('CHRor_holds_3__69' / 4, leash, notrace).
all_holds(A, B) :-
	'CHRgen_num'(C),
	coca(add_one_constraint(C, all_holds(A, B))),
	'CHRall_holds_2'(all_holds(A, B), D, E, C).



%%% Rules handling for all_holds / 2

'CHRall_holds_2'(all_holds(A, B), C, D, E) :-
	(
	    'CHRnonvar'(C)
	;
	    'CHRalready_in'('CHRall_holds_2'(all_holds(A, B), C, D, E)),
	    coca(already_in)
	),
	!.
'CHRall_holds_2'(all_holds(A, B), C, D, E) ?-
	coca(try_rule(E, all_holds(A, B), anonymous("4"), all_holds(F, G), replacement, true, all_holds(F, 0 #= 0, G))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("4"))),
	all_holds(A, 0 #= 0, B).
'CHRall_holds_2'(all_holds(A, B), C, D, E) :-
	'CHRall_holds_2__70'(all_holds(A, B), C, D, E).
:- set_flag('CHRall_holds_2' / 4, leash, notrace).
:- current_macro('CHRall_holds_2' / 4, _41603, _41604, _41605) -> true ; define_macro('CHRall_holds_2' / 4, tr_chr / 2, [write]).
'CHRall_holds_2__70'(A, B, C, D) :-
	'CHRall_holds_2__71'(A, B, C, D).
:- set_flag('CHRall_holds_2__70' / 4, leash, notrace).
'CHRall_holds_2__71'(all_holds(A, B), C, D, E) :-
	(
	    'CHRvar'(C)
	->
	    'CHRdelay'([C, all_holds(A, B)], 'CHRall_holds_2'(all_holds(A, B), C, D, E))
	;
	    true
	).
:- set_flag('CHRall_holds_2__71' / 4, leash, notrace).
all_holds(A, B, C) :-
	'CHRgen_num'(D),
	coca(add_one_constraint(D, all_holds(A, B, C))),
	'CHRall_holds_3'(all_holds(A, B, C), E, F, D).



%%% Rules handling for all_holds / 3

'CHRall_holds_3'(all_holds(A, B, C), D, E, F) :-
	(
	    'CHRnonvar'(D)
	;
	    'CHRalready_in'('CHRall_holds_3'(all_holds(A, B, C), D, E, F)),
	    coca(already_in)
	),
	!.
'CHRall_holds_3'(all_holds(A, B, [C|D]), E, F, G) ?-
	coca(try_rule(G, all_holds(A, B, [C|D]), anonymous("5"), all_holds(H, I, [J|K]), replacement, true, \+ (H = J, call(I)) -> all_holds(H, I, K) ; (H =.. [L|M], J =.. [N|O], or_neq(exists, M, O, P), all_holds(H, #/\(I, P), K)))),
	!,
	'CHRkill'(E),
	coca(fired_rule(anonymous("5"))),
	(
	    \+ (A = C, call(B))
	->
	    all_holds(A, B, D)
	;
	    A =.. [Q|R],
	    C =.. [S|T],
	    or_neq(exists, R, T, U),
	    all_holds(A, #/\(B, U), D)
	).
'CHRall_holds_3'(all_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRall_holds_3__73'(G, [C], [H, I], J),
	coca(try_double(F, all_holds(A, B, C), J, all_not_holds(I, H, C), all_holds(K, L, M), all_not_holds(N, O, M), replacement, (copy_fluent(K, L, P, Q), copy_fluent(N, O, R, S), P = R, call(#/\(Q, S))), false, anonymous("7"))),
	no_delayed_goals((copy_fluent(A, B, T, U), copy_fluent(I, H, V, W), T = V, call(#/\(U, W)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("7"))),
	false.
'CHRall_holds_3'(all_holds(A, B, C), D, E, F) :-
	'CHRall_holds_3__72'(all_holds(A, B, C), D, E, F).
'CHRall_holds_3__73'(['CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHRkill'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRall_holds_3__73'([A|B], C, D, E) :-
	'CHRall_holds_3__73'(B, C, D, E).
:- set_flag('CHRall_holds_3__73' / 4, leash, notrace).
:- set_flag('CHRall_holds_3' / 4, leash, notrace).
:- current_macro('CHRall_holds_3' / 4, _42907, _42908, _42909) -> true ; define_macro('CHRall_holds_3' / 4, tr_chr / 2, [write]).
'CHRall_holds_3__72'(A, B, C, D) :-
	'CHRall_holds_3__74'(A, B, C, D).
:- set_flag('CHRall_holds_3__72' / 4, leash, notrace).
'CHRall_holds_3__74'(all_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_holds_3__74__75'(G, D, all_holds(A, B, C), E, F).
'CHRall_holds_3__74'(all_holds(A, B, C), D, E, F) :-
	'CHRall_holds_3__74__76'(all_holds(A, B, C), D, E, F).
:- set_flag('CHRall_holds_3__74' / 4, leash, notrace).
'CHRall_holds_3__74__75'(['CHRor_holds_2'(or_holds(A, B), C, D, E)|F], G, all_holds(H, I, B), J, K) ?-
	'CHRvar'(C),
	coca(try_double(K, all_holds(H, I, B), E, or_holds(A, B), all_holds(L, M, N), or_holds(O, N), keep_first, (member(P, O), copy_fluent(L, M, Q, R), Q = P, \+ call(#\+(R))), true, anonymous("8"))),
	no_delayed_goals((member(S, A), copy_fluent(H, I, T, U), T = S, \+ call(#\+(U)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("8"))),
	'CHRall_holds_3__74__75'(F, G, all_holds(H, I, B), J, K).
'CHRall_holds_3__74__75'([A|B], C, D, E, F) :-
	'CHRall_holds_3__74__75'(B, C, D, E, F).
'CHRall_holds_3__74__75'([], A, B, C, D) :-
	'CHRall_holds_3__74__76'(B, A, C, D).
:- set_flag('CHRall_holds_3__74__75' / 5, leash, notrace).
'CHRall_holds_3__74__76'(all_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_holds_3__74__76__77'(G, D, all_holds(A, B, C), E, F).
'CHRall_holds_3__74__76'(all_holds(A, B, C), D, E, F) :-
	'CHRall_holds_3__74__76__78'(all_holds(A, B, C), D, E, F).
:- set_flag('CHRall_holds_3__74__76' / 4, leash, notrace).
'CHRall_holds_3__74__76__77'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, all_holds(I, J, C), K, L) ?-
	'CHRvar'(D),
	coca(try_double(L, all_holds(I, J, C), F, if_then_or_holds(A, B, C), all_holds(M, N, O), if_then_or_holds(P, Q, O), keep_first, (copy_fluent(M, N, R, S), R = P, \+ call(#\+(S))), or_holds(Q, O), anonymous("9"))),
	no_delayed_goals((copy_fluent(I, J, T, U), T = A, \+ call(#\+(U)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("9"))),
	'CHRall_holds_3__74__76__77'(G, H, all_holds(I, J, C), K, L),
	or_holds(B, C).
'CHRall_holds_3__74__76__77'([A|B], C, D, E, F) :-
	'CHRall_holds_3__74__76__77'(B, C, D, E, F).
'CHRall_holds_3__74__76__77'([], A, B, C, D) :-
	'CHRall_holds_3__74__76__78'(B, A, C, D).
:- set_flag('CHRall_holds_3__74__76__77' / 5, leash, notrace).
'CHRall_holds_3__74__76__78'(all_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_holds_3__74__76__78__79'(G, D, all_holds(A, B, C), E, F).
'CHRall_holds_3__74__76__78'(all_holds(A, B, C), D, E, F) :-
	'CHRall_holds_3__74__76__78__80'(all_holds(A, B, C), D, E, F).
:- set_flag('CHRall_holds_3__74__76__78' / 4, leash, notrace).
'CHRall_holds_3__74__76__78__79'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, all_holds(I, J, C), K, L) ?-
	'CHRvar'(D),
	coca(try_double(L, all_holds(I, J, C), F, if_then_or_holds(A, B, C), all_holds(M, N, O), if_then_or_holds(P, Q, O), keep_first, (member(R, Q), copy_fluent(M, N, S, T), S = R, \+ call(#\+(T))), true, anonymous("10"))),
	no_delayed_goals((member(U, B), copy_fluent(I, J, V, W), V = U, \+ call(#\+(W)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("10"))),
	'CHRall_holds_3__74__76__78__79'(G, H, all_holds(I, J, C), K, L).
'CHRall_holds_3__74__76__78__79'([A|B], C, D, E, F) :-
	'CHRall_holds_3__74__76__78__79'(B, C, D, E, F).
'CHRall_holds_3__74__76__78__79'([], A, B, C, D) :-
	'CHRall_holds_3__74__76__78__80'(B, A, C, D).
:- set_flag('CHRall_holds_3__74__76__78__79' / 5, leash, notrace).
'CHRall_holds_3__74__76__78__80'(all_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_holds_3__74__76__78__80__81'(G, D, all_holds(A, B, C), E, F).
'CHRall_holds_3__74__76__78__80'(all_holds(A, B, C), D, E, F) :-
	'CHRall_holds_3__74__76__78__80__82'(all_holds(A, B, C), D, E, F).
:- set_flag('CHRall_holds_3__74__76__78__80' / 4, leash, notrace).
'CHRall_holds_3__74__76__78__80__81'(['CHRnot_holds_2'(not_holds(A, B), C, D, E)|F], G, all_holds(H, I, B), J, K) ?-
	'CHRvar'(C),
	'CHRcheck_and_mark_applied'(anonymous("6"), G, C, J, D),
	coca(try_double(K, all_holds(H, I, B), E, not_holds(A, B), all_holds(L, M, N), not_holds(O, N), augmentation, copy_fluent(L, M, P, Q), (P = O, call(#\+(Q))), anonymous("6"))),
	no_delayed_goals(copy_fluent(H, I, R, S)),
	!,
	coca(fired_rule(anonymous("6"))),
	'CHRall_holds_3__74__76__78__80__81'(F, G, all_holds(H, I, B), J, K),
	R = A,
	call(#\+(S)).
'CHRall_holds_3__74__76__78__80__81'([A|B], C, D, E, F) :-
	'CHRall_holds_3__74__76__78__80__81'(B, C, D, E, F).
'CHRall_holds_3__74__76__78__80__81'([], A, B, C, D) :-
	'CHRall_holds_3__74__76__78__80__82'(B, A, C, D).
:- set_flag('CHRall_holds_3__74__76__78__80__81' / 5, leash, notrace).
'CHRall_holds_3__74__76__78__80__82'(all_holds(A, B, C), D, E, F) :-
	(
	    'CHRvar'(D)
	->
	    'CHRdelay'([D, all_holds(A, B, C)], 'CHRall_holds_3'(all_holds(A, B, C), D, E, F))
	;
	    true
	).
:- set_flag('CHRall_holds_3__74__76__78__80__82' / 4, leash, notrace).
all_not_holds(A, B, C) :-
	'CHRgen_num'(D),
	coca(add_one_constraint(D, all_not_holds(A, B, C))),
	'CHRall_not_holds_3'(all_not_holds(A, B, C), E, F, D).



%%% Rules handling for all_not_holds / 3

'CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F) :-
	(
	    'CHRnonvar'(D)
	;
	    'CHRalready_in'('CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F)),
	    coca(already_in)
	),
	!.
'CHRall_not_holds_3'(all_not_holds(A, B, []), C, D, E) ?-
	coca(try_rule(E, all_not_holds(A, B, []), anonymous("12"), all_not_holds(F, G, []), replacement, true, true)),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("12"))).
'CHRall_not_holds_3'(all_not_holds(A, B, [C|D]), E, F, G) ?-
	coca(try_rule(G, all_not_holds(A, B, [C|D]), anonymous("17"), all_not_holds(H, I, [J|K]), replacement, true, ((\+ (H = J, call(I)) -> true ; copy_fluent(H = J, I, L = M, N), L = M, eq(J, M, O), neq_all(H, J, P), call(#\/(#/\(O, #\+(N)), P))), all_not_holds(H, I, K)))),
	!,
	'CHRkill'(E),
	coca(fired_rule(anonymous("17"))),
	(
	    \+ (A = C, call(B))
	->
	    true
	;
	    copy_fluent(A = C, B, Q = R, S),
	    Q = R,
	    eq(C, R, T),
	    neq_all(A, C, U),
	    call(#\/(#/\(T, #\+(S)), U))
	),
	all_not_holds(A, B, D).
'CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRall_not_holds_3__84'(G, [C], [H, I], J),
	coca(try_double(F, all_not_holds(A, B, C), J, all_holds(I, H, C), all_not_holds(K, L, M), all_holds(N, O, M), replacement, (copy_fluent(N, O, P, Q), copy_fluent(K, L, R, S), P = R, call(#/\(Q, S))), false, anonymous("7"))),
	no_delayed_goals((copy_fluent(I, H, T, U), copy_fluent(A, B, V, W), T = V, call(#/\(U, W)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("7"))),
	false.
'CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F) :-
	'CHRall_not_holds_3__83'(all_not_holds(A, B, C), D, E, F).
'CHRall_not_holds_3__84'(['CHRall_holds_3'(all_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHRkill'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRall_not_holds_3__84'([A|B], C, D, E) :-
	'CHRall_not_holds_3__84'(B, C, D, E).
:- set_flag('CHRall_not_holds_3__84' / 4, leash, notrace).
:- set_flag('CHRall_not_holds_3' / 4, leash, notrace).
:- current_macro('CHRall_not_holds_3' / 4, _46737, _46738, _46739) -> true ; define_macro('CHRall_not_holds_3' / 4, tr_chr / 2, [write]).
'CHRall_not_holds_3__83'(A, B, C, D) :-
	'CHRall_not_holds_3__85'(A, B, C, D).
:- set_flag('CHRall_not_holds_3__83' / 4, leash, notrace).
'CHRall_not_holds_3__85'(all_not_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_not_holds_3__85__86'(G, D, all_not_holds(A, B, C), E, F).
'CHRall_not_holds_3__85'(all_not_holds(A, B, C), D, E, F) :-
	'CHRall_not_holds_3__85__87'(all_not_holds(A, B, C), D, E, F).
:- set_flag('CHRall_not_holds_3__85' / 4, leash, notrace).
'CHRall_not_holds_3__85__86'(['CHRnot_holds_2'(not_holds(A, B), C, D, E)|F], G, all_not_holds(H, I, B), J, K) ?-
	'CHRvar'(C),
	coca(try_double(K, all_not_holds(H, I, B), E, not_holds(A, B), all_not_holds(L, M, N), not_holds(O, N), keep_first, (copy_fluent(L, M, P, Q), P = O, \+ call(#\+(Q))), true, anonymous("13"))),
	no_delayed_goals((copy_fluent(H, I, R, S), R = A, \+ call(#\+(S)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("13"))),
	'CHRall_not_holds_3__85__86'(F, G, all_not_holds(H, I, B), J, K).
'CHRall_not_holds_3__85__86'([A|B], C, D, E, F) :-
	'CHRall_not_holds_3__85__86'(B, C, D, E, F).
'CHRall_not_holds_3__85__86'([], A, B, C, D) :-
	'CHRall_not_holds_3__85__87'(B, A, C, D).
:- set_flag('CHRall_not_holds_3__85__86' / 5, leash, notrace).
'CHRall_not_holds_3__85__87'(all_not_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_not_holds_3__85__87__88'(G, D, all_not_holds(A, B, C), E, F).
'CHRall_not_holds_3__85__87'(all_not_holds(A, B, C), D, E, F) :-
	'CHRall_not_holds_3__85__87__89'(all_not_holds(A, B, C), D, E, F).
:- set_flag('CHRall_not_holds_3__85__87' / 4, leash, notrace).
'CHRall_not_holds_3__85__87__88'(['CHRor_holds_2'(or_holds(A, B), C, D, E)|F], G, all_not_holds(H, I, B), J, K) ?-
	'CHRvar'(C),
	coca(try_double(K, all_not_holds(H, I, B), E, or_holds(A, B), all_not_holds(L, M, N), or_holds(O, N), keep_first, (member(P, O, Q), copy_fluent(L, M, R, S), R = P, \+ call(#\+(S))), or_holds(Q, N), anonymous("14"))),
	no_delayed_goals((member(T, A, U), copy_fluent(H, I, V, W), V = T, \+ call(#\+(W)))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("14"))),
	'CHRall_not_holds_3__85__87__88'(F, G, all_not_holds(H, I, B), J, K),
	or_holds(U, B).
'CHRall_not_holds_3__85__87__88'([A|B], C, D, E, F) :-
	'CHRall_not_holds_3__85__87__88'(B, C, D, E, F).
'CHRall_not_holds_3__85__87__88'([], A, B, C, D) :-
	'CHRall_not_holds_3__85__87__89'(B, A, C, D).
:- set_flag('CHRall_not_holds_3__85__87__88' / 5, leash, notrace).
'CHRall_not_holds_3__85__87__89'(all_not_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_not_holds_3__85__87__89__90'(G, D, all_not_holds(A, B, C), E, F).
'CHRall_not_holds_3__85__87__89'(all_not_holds(A, B, C), D, E, F) :-
	'CHRall_not_holds_3__85__87__89__91'(all_not_holds(A, B, C), D, E, F).
:- set_flag('CHRall_not_holds_3__85__87__89' / 4, leash, notrace).
'CHRall_not_holds_3__85__87__89__90'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, all_not_holds(I, J, C), K, L) ?-
	'CHRvar'(D),
	coca(try_double(L, all_not_holds(I, J, C), F, if_then_or_holds(A, B, C), all_not_holds(M, N, O), if_then_or_holds(P, Q, O), keep_first, (copy_fluent(M, N, R, S), R = P, \+ call(#\+(S))), true, anonymous("15"))),
	no_delayed_goals((copy_fluent(I, J, T, U), T = A, \+ call(#\+(U)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("15"))),
	'CHRall_not_holds_3__85__87__89__90'(G, H, all_not_holds(I, J, C), K, L).
'CHRall_not_holds_3__85__87__89__90'([A|B], C, D, E, F) :-
	'CHRall_not_holds_3__85__87__89__90'(B, C, D, E, F).
'CHRall_not_holds_3__85__87__89__90'([], A, B, C, D) :-
	'CHRall_not_holds_3__85__87__89__91'(B, A, C, D).
:- set_flag('CHRall_not_holds_3__85__87__89__90' / 5, leash, notrace).
'CHRall_not_holds_3__85__87__89__91'(all_not_holds(A, B, C), D, E, F) ?-
	'CHRvar'(D),
	!,
	'CHRget_delayed_goals'(C, G),
	'CHRall_not_holds_3__85__87__89__91__92'(G, D, all_not_holds(A, B, C), E, F).
'CHRall_not_holds_3__85__87__89__91'(all_not_holds(A, B, C), D, E, F) :-
	'CHRall_not_holds_3__85__87__89__91__93'(all_not_holds(A, B, C), D, E, F).
:- set_flag('CHRall_not_holds_3__85__87__89__91' / 4, leash, notrace).
'CHRall_not_holds_3__85__87__89__91__92'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, all_not_holds(I, J, C), K, L) ?-
	'CHRvar'(D),
	coca(try_double(L, all_not_holds(I, J, C), F, if_then_or_holds(A, B, C), all_not_holds(M, N, O), if_then_or_holds(P, Q, O), keep_first, (member(R, Q, S), copy_fluent(M, N, T, U), T = R, \+ call(#\+(U))), if_then_or_holds(P, S, O), anonymous("16"))),
	no_delayed_goals((member(V, B, W), copy_fluent(I, J, X, Y), X = V, \+ call(#\+(Y)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("16"))),
	'CHRall_not_holds_3__85__87__89__91__92'(G, H, all_not_holds(I, J, C), K, L),
	if_then_or_holds(A, W, C).
'CHRall_not_holds_3__85__87__89__91__92'([A|B], C, D, E, F) :-
	'CHRall_not_holds_3__85__87__89__91__92'(B, C, D, E, F).
'CHRall_not_holds_3__85__87__89__91__92'([], A, B, C, D) :-
	'CHRall_not_holds_3__85__87__89__91__93'(B, A, C, D).
:- set_flag('CHRall_not_holds_3__85__87__89__91__92' / 5, leash, notrace).
'CHRall_not_holds_3__85__87__89__91__93'(all_not_holds(A, B, C), D, E, F) :-
	(
	    'CHRvar'(D)
	->
	    'CHRdelay'([D, all_not_holds(A, B, C)], 'CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F))
	;
	    true
	).
:- set_flag('CHRall_not_holds_3__85__87__89__91__93' / 4, leash, notrace).
if_then_holds(A, B, C) :-
	'CHRgen_num'(D),
	coca(add_one_constraint(D, if_then_holds(A, B, C))),
	'CHRif_then_holds_3'(if_then_holds(A, B, C), E, F, D).



%%% Rules handling for if_then_holds / 3

'CHRif_then_holds_3'(if_then_holds(A, B, C), D, E, F) :-
	(
	    'CHRnonvar'(D)
	;
	    'CHRalready_in'('CHRif_then_holds_3'(if_then_holds(A, B, C), D, E, F)),
	    coca(already_in)
	),
	!.
'CHRif_then_holds_3'(if_then_holds(A, B, C), D, E, F) ?-
	coca(try_rule(F, if_then_holds(A, B, C), anonymous("29"), if_then_holds(G, H, I), replacement, true, if_then_or_holds(G, [H], I))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("29"))),
	if_then_or_holds(A, [B], C).
'CHRif_then_holds_3'(if_then_holds(A, B, C), D, E, F) :-
	'CHRif_then_holds_3__94'(if_then_holds(A, B, C), D, E, F).
:- set_flag('CHRif_then_holds_3' / 4, leash, notrace).
:- current_macro('CHRif_then_holds_3' / 4, _49791, _49792, _49793) -> true ; define_macro('CHRif_then_holds_3' / 4, tr_chr / 2, [write]).
'CHRif_then_holds_3__94'(A, B, C, D) :-
	'CHRif_then_holds_3__95'(A, B, C, D).
:- set_flag('CHRif_then_holds_3__94' / 4, leash, notrace).
'CHRif_then_holds_3__95'(if_then_holds(A, B, C), D, E, F) :-
	(
	    'CHRvar'(D)
	->
	    'CHRdelay'([D, if_then_holds(A, B, C)], 'CHRif_then_holds_3'(if_then_holds(A, B, C), D, E, F))
	;
	    true
	).
:- set_flag('CHRif_then_holds_3__95' / 4, leash, notrace).
if_then_or_holds(A, B, C) :-
	'CHRgen_num'(D),
	coca(add_one_constraint(D, if_then_or_holds(A, B, C))),
	'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), E, F, D).



%%% Rules handling for if_then_or_holds / 3

'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) :-
	(
	    'CHRnonvar'(D)
	;
	    'CHRalready_in'('CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)),
	    coca(already_in)
	),
	!.
'CHRif_then_or_holds_3'(if_then_or_holds(A, [], B), C, D, E) ?-
	coca(try_rule(E, if_then_or_holds(A, [], B), anonymous("30"), if_then_or_holds(F, [], G), replacement, true, not_holds(F, G))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("30"))),
	not_holds(A, B).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, []), C, D, E) ?-
	coca(try_rule(E, if_then_or_holds(A, B, []), anonymous("31"), if_then_or_holds(F, G, []), replacement, true, true)),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("31"))).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	coca(try_rule(F, if_then_or_holds(A, B, C), anonymous("32"), if_then_or_holds(G, H, I), replacement, (member(eq(J, K), H), or_neq(exists, J, K, L), \+ call(L)), true)),
	no_delayed_goals((member(eq(M, N), B), or_neq(exists, M, N, O), \+ call(O))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("32"))).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	coca(try_rule(F, if_then_or_holds(A, B, C), anonymous("33"), if_then_or_holds(G, H, I), replacement, (member(eq(J, K), H, L), \+ (and_eq(J, K, M), call(M))), if_then_or_holds(G, L, I))),
	no_delayed_goals((member(eq(N, O), B, P), \+ (and_eq(N, O, Q), call(Q)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("33"))),
	if_then_or_holds(A, P, C).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, [C|D]), E, F, G) ?-
	coca(try_rule(G, if_then_or_holds(A, B, [C|D]), anonymous("34"), if_then_or_holds(H, I, [J|K]), replacement, true, H == J -> or_holds(I, [J|K]) ; H \= J -> if_then_or_holds(H, I, [], [J|K]) ; (H =.. [L|M], J =.. [N|O], or_holds([neq(M, O)|I], [J|K]), if_then_or_holds(H, I, [], [J|K])))),
	!,
	'CHRkill'(E),
	coca(fired_rule(anonymous("34"))),
	(
	    A == C
	->
	    or_holds(B, [C|D])
	;
	    (
		A \= C
	    ->
		if_then_or_holds(A, B, [], [C|D])
	    ;
		A =.. [P|Q],
		C =.. [R|S],
		or_holds([neq(Q, S)|B], [C|D]),
		if_then_or_holds(A, B, [], [C|D])
	    )
	).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__97'(G, [C], [H, I], J),
	coca(try_double(F, if_then_or_holds(A, B, C), J, all_holds(I, H, C), if_then_or_holds(K, L, M), all_holds(N, O, M), keep_second, (copy_fluent(N, O, P, Q), P = K, \+ call(#\+(Q))), or_holds(L, M), anonymous("9"))),
	no_delayed_goals((copy_fluent(I, H, R, S), R = A, \+ call(#\+(S)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("9"))),
	or_holds(B, C).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__98'(G, [C], [H, I], J),
	coca(try_double(F, if_then_or_holds(A, B, C), J, all_holds(I, H, C), if_then_or_holds(K, L, M), all_holds(N, O, M), keep_second, (member(P, L), copy_fluent(N, O, Q, R), Q = P, \+ call(#\+(R))), true, anonymous("10"))),
	no_delayed_goals((member(S, B), copy_fluent(I, H, T, U), T = S, \+ call(#\+(U)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("10"))).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__99'(G, [C], [H, I], J),
	coca(try_double(F, if_then_or_holds(A, B, C), J, all_not_holds(I, H, C), if_then_or_holds(K, L, M), all_not_holds(N, O, M), keep_second, (copy_fluent(N, O, P, Q), P = K, \+ call(#\+(Q))), true, anonymous("15"))),
	no_delayed_goals((copy_fluent(I, H, R, S), R = A, \+ call(#\+(S)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("15"))).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__100'(G, [C], [H, I], J),
	coca(try_double(F, if_then_or_holds(A, B, C), J, all_not_holds(I, H, C), if_then_or_holds(K, L, M), all_not_holds(N, O, M), keep_second, (member(P, L, Q), copy_fluent(N, O, R, S), R = P, \+ call(#\+(S))), if_then_or_holds(K, Q, M), anonymous("16"))),
	no_delayed_goals((member(T, B, U), copy_fluent(I, H, V, W), V = T, \+ call(#\+(W)))),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("16"))),
	if_then_or_holds(A, U, C).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__101'(G, [C], [H], I),
	coca(try_double(F, if_then_or_holds(A, B, C), I, not_holds(H, C), if_then_or_holds(J, K, L), not_holds(M, L), keep_second, M == J, true, anonymous("37"))),
	no_delayed_goals(H == A),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("37"))).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__102'(G, [C], [H], I),
	coca(try_double(F, if_then_or_holds(A, B, C), I, not_holds(H, C), if_then_or_holds(J, K, L), not_holds(M, L), keep_second, (member(N, K, O), M == N), if_then_or_holds(J, O, L), anonymous("38"))),
	no_delayed_goals((member(P, B, Q), H == P)),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("38"))),
	if_then_or_holds(A, Q, C).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__103'(G, [C], [H], I),
	coca(try_double(F, if_then_or_holds(A, B, C), I, cancel(H, C), if_then_or_holds(J, K, L), cancel(M, L), keep_second, \+ M \= J, true, anonymous("42"))),
	no_delayed_goals(\+ H \= A),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("42"))).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) ?-
	'CHRget_delayed_goals'(C, G),
	'CHRif_then_or_holds_3__104'(G, [C], [H], I),
	coca(try_double(F, if_then_or_holds(A, B, C), I, cancel(H, C), if_then_or_holds(J, K, L), cancel(M, L), keep_second, (member(N, K), \+ M \= N), true, anonymous("43"))),
	no_delayed_goals((member(O, B), \+ H \= O)),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("43"))).
'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F) :-
	'CHRif_then_or_holds_3__96'(if_then_or_holds(A, B, C), D, E, F).
'CHRif_then_or_holds_3__97'(['CHRall_holds_3'(all_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRif_then_or_holds_3__97'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__97'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__97' / 4, leash, notrace).
'CHRif_then_or_holds_3__98'(['CHRall_holds_3'(all_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRif_then_or_holds_3__98'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__98'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__98' / 4, leash, notrace).
'CHRif_then_or_holds_3__99'(['CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRif_then_or_holds_3__99'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__99'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__99' / 4, leash, notrace).
'CHRif_then_or_holds_3__100'(['CHRall_not_holds_3'(all_not_holds(A, B, C), D, E, F)|G], [C], [H, I], J) ?-
	'CHRvar'(D),
	'CHR='([B, A], [H, I]),
	'CHR='(F, J).
'CHRif_then_or_holds_3__100'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__100'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__100' / 4, leash, notrace).
'CHRif_then_or_holds_3__101'(['CHRnot_holds_2'(not_holds(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRif_then_or_holds_3__101'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__101'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__101' / 4, leash, notrace).
'CHRif_then_or_holds_3__102'(['CHRnot_holds_2'(not_holds(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRif_then_or_holds_3__102'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__102'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__102' / 4, leash, notrace).
'CHRif_then_or_holds_3__103'(['CHRcancel_2'(cancel(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRif_then_or_holds_3__103'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__103'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__103' / 4, leash, notrace).
'CHRif_then_or_holds_3__104'(['CHRcancel_2'(cancel(A, B), C, D, E)|F], [B], [G], H) ?-
	'CHRvar'(C),
	'CHR='([A], [G]),
	'CHR='(E, H).
'CHRif_then_or_holds_3__104'([A|B], C, D, E) :-
	'CHRif_then_or_holds_3__104'(B, C, D, E).
:- set_flag('CHRif_then_or_holds_3__104' / 4, leash, notrace).
:- set_flag('CHRif_then_or_holds_3' / 4, leash, notrace).
:- current_macro('CHRif_then_or_holds_3' / 4, _55080, _55081, _55082) -> true ; define_macro('CHRif_then_or_holds_3' / 4, tr_chr / 2, [write]).
'CHRif_then_or_holds_3__96'(A, B, C, D) :-
	'CHRif_then_or_holds_3__105'(A, B, C, D).
:- set_flag('CHRif_then_or_holds_3__96' / 4, leash, notrace).
'CHRif_then_or_holds_3__105'(if_then_or_holds(A, B, C), D, E, F) :-
	(
	    'CHRvar'(D)
	->
	    'CHRdelay'([D, if_then_or_holds(A, B, C)], 'CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F))
	;
	    true
	).
:- set_flag('CHRif_then_or_holds_3__105' / 4, leash, notrace).
if_then_or_holds(A, B, C, D) :-
	'CHRgen_num'(E),
	coca(add_one_constraint(E, if_then_or_holds(A, B, C, D))),
	'CHRif_then_or_holds_4'(if_then_or_holds(A, B, C, D), F, G, E).



%%% Rules handling for if_then_or_holds / 4

'CHRif_then_or_holds_4'(if_then_or_holds(A, B, C, D), E, F, G) :-
	(
	    'CHRnonvar'(E)
	;
	    'CHRalready_in'('CHRif_then_or_holds_4'(if_then_or_holds(A, B, C, D), E, F, G)),
	    coca(already_in)
	),
	!.
'CHRif_then_or_holds_4'(if_then_or_holds(A, [B|C], D, [E|F]), G, H, I) ?-
	coca(try_rule(I, if_then_or_holds(A, [B|C], D, [E|F]), anonymous("35"), if_then_or_holds(J, [K|L], M, [N|O]), replacement, true, K == N -> true ; K \= N -> if_then_or_holds(J, L, [K|M], [N|O]) ; (K =.. [P|Q], N =.. [R|S], if_then_or_holds(J, L, [eq(Q, S), K|M], [N|O])))),
	!,
	'CHRkill'(G),
	coca(fired_rule(anonymous("35"))),
	(
	    B == E
	->
	    true
	;
	    (
		B \= E
	    ->
		if_then_or_holds(A, C, [B|D], [E|F])
	    ;
		B =.. [T|U],
		E =.. [V|W],
		if_then_or_holds(A, C, [eq(U, W), B|D], [E|F])
	    )
	).
'CHRif_then_or_holds_4'(if_then_or_holds(A, [], B, [C|D]), E, F, G) ?-
	coca(try_rule(G, if_then_or_holds(A, [], B, [C|D]), anonymous("36"), if_then_or_holds(H, [], I, [J|K]), replacement, true, if_then_or_holds(H, I, K))),
	!,
	'CHRkill'(E),
	coca(fired_rule(anonymous("36"))),
	if_then_or_holds(A, B, D).
'CHRif_then_or_holds_4'(if_then_or_holds(A, B, C, D), E, F, G) :-
	'CHRif_then_or_holds_4__106'(if_then_or_holds(A, B, C, D), E, F, G).
:- set_flag('CHRif_then_or_holds_4' / 4, leash, notrace).
:- current_macro('CHRif_then_or_holds_4' / 4, _56042, _56043, _56044) -> true ; define_macro('CHRif_then_or_holds_4' / 4, tr_chr / 2, [write]).
'CHRif_then_or_holds_4__106'(A, B, C, D) :-
	'CHRif_then_or_holds_4__107'(A, B, C, D).
:- set_flag('CHRif_then_or_holds_4__106' / 4, leash, notrace).
'CHRif_then_or_holds_4__107'(if_then_or_holds(A, B, C, D), E, F, G) :-
	(
	    'CHRvar'(E)
	->
	    'CHRdelay'([E, if_then_or_holds(A, B, C, D)], 'CHRif_then_or_holds_4'(if_then_or_holds(A, B, C, D), E, F, G))
	;
	    true
	).
:- set_flag('CHRif_then_or_holds_4__107' / 4, leash, notrace).
cancel(A, B) :-
	'CHRgen_num'(C),
	coca(add_one_constraint(C, cancel(A, B))),
	'CHRcancel_2'(cancel(A, B), D, E, C).



%%% Rules handling for cancel / 2

'CHRcancel_2'(cancel(A, B), C, D, E) :-
	(
	    'CHRnonvar'(C)
	;
	    'CHRalready_in'('CHRcancel_2'(cancel(A, B), C, D, E)),
	    coca(already_in)
	),
	!.
'CHRcancel_2'(cancel(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRcancel_2__109'(F, [B, A], [], G),
	coca(try_double(E, cancel(A, B), G, cancelled(A, B), cancel(H, I), cancelled(H, I), replacement, true, true, anonymous("44"))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("44"))).
'CHRcancel_2'(cancel(A, B), C, D, E) :-
	'CHRcancel_2__108'(cancel(A, B), C, D, E).
'CHRcancel_2__109'(['CHRcancelled_2'(cancelled(A, B), C, D, E)|F], [B, A], [], G) ?-
	'CHRvar'(C),
	'CHRkill'(C),
	'CHR='([], []),
	'CHR='(E, G).
'CHRcancel_2__109'([A|B], C, D, E) :-
	'CHRcancel_2__109'(B, C, D, E).
:- set_flag('CHRcancel_2__109' / 4, leash, notrace).
:- set_flag('CHRcancel_2' / 4, leash, notrace).
:- current_macro('CHRcancel_2' / 4, _56976, _56977, _56978) -> true ; define_macro('CHRcancel_2' / 4, tr_chr / 2, [write]).
'CHRcancel_2__108'(A, B, C, D) :-
	'CHRcancel_2__110'(A, B, C, D).
:- set_flag('CHRcancel_2__108' / 4, leash, notrace).
'CHRcancel_2__110'(cancel(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRcancel_2__110__111'(F, C, cancel(A, B), D, E).
'CHRcancel_2__110'(cancel(A, B), C, D, E) :-
	'CHRcancel_2__110__112'(cancel(A, B), C, D, E).
:- set_flag('CHRcancel_2__110' / 4, leash, notrace).
'CHRcancel_2__110__111'(['CHRnot_holds_2'(not_holds(A, B), C, D, E)|F], G, cancel(H, B), I, J) ?-
	'CHRvar'(C),
	coca(try_double(J, cancel(H, B), E, not_holds(A, B), cancel(K, L), not_holds(M, L), keep_first, \+ K \= M, true, anonymous("39"))),
	no_delayed_goals(\+ H \= A),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("39"))),
	'CHRcancel_2__110__111'(F, G, cancel(H, B), I, J).
'CHRcancel_2__110__111'([A|B], C, D, E, F) :-
	'CHRcancel_2__110__111'(B, C, D, E, F).
'CHRcancel_2__110__111'([], A, B, C, D) :-
	'CHRcancel_2__110__112'(B, A, C, D).
:- set_flag('CHRcancel_2__110__111' / 5, leash, notrace).
'CHRcancel_2__110__112'(cancel(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRcancel_2__110__112__113'(F, C, cancel(A, B), D, E).
'CHRcancel_2__110__112'(cancel(A, B), C, D, E) :-
	'CHRcancel_2__110__112__114'(cancel(A, B), C, D, E).
:- set_flag('CHRcancel_2__110__112' / 4, leash, notrace).
'CHRcancel_2__110__112__113'(['CHRnot_holds_all_2'(not_holds_all(A, B), C, D, E)|F], G, cancel(H, B), I, J) ?-
	'CHRvar'(C),
	coca(try_double(J, cancel(H, B), E, not_holds_all(A, B), cancel(K, L), not_holds_all(M, L), keep_first, \+ K \= M, true, anonymous("40"))),
	no_delayed_goals(\+ H \= A),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("40"))),
	'CHRcancel_2__110__112__113'(F, G, cancel(H, B), I, J).
'CHRcancel_2__110__112__113'([A|B], C, D, E, F) :-
	'CHRcancel_2__110__112__113'(B, C, D, E, F).
'CHRcancel_2__110__112__113'([], A, B, C, D) :-
	'CHRcancel_2__110__112__114'(B, A, C, D).
:- set_flag('CHRcancel_2__110__112__113' / 5, leash, notrace).
'CHRcancel_2__110__112__114'(cancel(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRcancel_2__110__112__114__115'(F, C, cancel(A, B), D, E).
'CHRcancel_2__110__112__114'(cancel(A, B), C, D, E) :-
	'CHRcancel_2__110__112__114__116'(cancel(A, B), C, D, E).
:- set_flag('CHRcancel_2__110__112__114' / 4, leash, notrace).
'CHRcancel_2__110__112__114__115'(['CHRor_holds_2'(or_holds(A, B), C, D, E)|F], G, cancel(H, B), I, J) ?-
	'CHRvar'(C),
	coca(try_double(J, cancel(H, B), E, or_holds(A, B), cancel(K, L), or_holds(M, L), keep_first, (member(N, M), \+ K \= N), true, anonymous("41"))),
	no_delayed_goals((member(O, A), \+ H \= O)),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("41"))),
	'CHRcancel_2__110__112__114__115'(F, G, cancel(H, B), I, J).
'CHRcancel_2__110__112__114__115'([A|B], C, D, E, F) :-
	'CHRcancel_2__110__112__114__115'(B, C, D, E, F).
'CHRcancel_2__110__112__114__115'([], A, B, C, D) :-
	'CHRcancel_2__110__112__114__116'(B, A, C, D).
:- set_flag('CHRcancel_2__110__112__114__115' / 5, leash, notrace).
'CHRcancel_2__110__112__114__116'(cancel(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRcancel_2__110__112__114__116__117'(F, C, cancel(A, B), D, E).
'CHRcancel_2__110__112__114__116'(cancel(A, B), C, D, E) :-
	'CHRcancel_2__110__112__114__116__118'(cancel(A, B), C, D, E).
:- set_flag('CHRcancel_2__110__112__114__116' / 4, leash, notrace).
'CHRcancel_2__110__112__114__116__117'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, cancel(I, C), J, K) ?-
	'CHRvar'(D),
	coca(try_double(K, cancel(I, C), F, if_then_or_holds(A, B, C), cancel(L, M), if_then_or_holds(N, O, M), keep_first, \+ L \= N, true, anonymous("42"))),
	no_delayed_goals(\+ I \= A),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("42"))),
	'CHRcancel_2__110__112__114__116__117'(G, H, cancel(I, C), J, K).
'CHRcancel_2__110__112__114__116__117'([A|B], C, D, E, F) :-
	'CHRcancel_2__110__112__114__116__117'(B, C, D, E, F).
'CHRcancel_2__110__112__114__116__117'([], A, B, C, D) :-
	'CHRcancel_2__110__112__114__116__118'(B, A, C, D).
:- set_flag('CHRcancel_2__110__112__114__116__117' / 5, leash, notrace).
'CHRcancel_2__110__112__114__116__118'(cancel(A, B), C, D, E) ?-
	'CHRvar'(C),
	!,
	'CHRget_delayed_goals'(B, F),
	'CHRcancel_2__110__112__114__116__118__119'(F, C, cancel(A, B), D, E).
'CHRcancel_2__110__112__114__116__118'(cancel(A, B), C, D, E) :-
	'CHRcancel_2__110__112__114__116__118__120'(cancel(A, B), C, D, E).
:- set_flag('CHRcancel_2__110__112__114__116__118' / 4, leash, notrace).
'CHRcancel_2__110__112__114__116__118__119'(['CHRif_then_or_holds_3'(if_then_or_holds(A, B, C), D, E, F)|G], H, cancel(I, C), J, K) ?-
	'CHRvar'(D),
	coca(try_double(K, cancel(I, C), F, if_then_or_holds(A, B, C), cancel(L, M), if_then_or_holds(N, O, M), keep_first, (member(P, O), \+ L \= P), true, anonymous("43"))),
	no_delayed_goals((member(Q, B), \+ I \= Q)),
	!,
	'CHRkill'(D),
	coca(fired_rule(anonymous("43"))),
	'CHRcancel_2__110__112__114__116__118__119'(G, H, cancel(I, C), J, K).
'CHRcancel_2__110__112__114__116__118__119'([A|B], C, D, E, F) :-
	'CHRcancel_2__110__112__114__116__118__119'(B, C, D, E, F).
'CHRcancel_2__110__112__114__116__118__119'([], A, B, C, D) :-
	'CHRcancel_2__110__112__114__116__118__120'(B, A, C, D).
:- set_flag('CHRcancel_2__110__112__114__116__118__119' / 5, leash, notrace).
'CHRcancel_2__110__112__114__116__118__120'(cancel(A, B), C, D, E) :-
	(
	    'CHRvar'(C)
	->
	    'CHRdelay'([C, cancel(A, B)], 'CHRcancel_2'(cancel(A, B), C, D, E))
	;
	    true
	).
:- set_flag('CHRcancel_2__110__112__114__116__118__120' / 4, leash, notrace).
cancelled(A, B) :-
	'CHRgen_num'(C),
	coca(add_one_constraint(C, cancelled(A, B))),
	'CHRcancelled_2'(cancelled(A, B), D, E, C).



%%% Rules handling for cancelled / 2

'CHRcancelled_2'(cancelled(A, B), C, D, E) :-
	(
	    'CHRnonvar'(C)
	;
	    'CHRalready_in'('CHRcancelled_2'(cancelled(A, B), C, D, E)),
	    coca(already_in)
	),
	!.
'CHRcancelled_2'(cancelled(A, B), C, D, E) ?-
	'CHRget_delayed_goals'(B, F),
	'CHRcancelled_2__122'(F, [B, A], [], G),
	coca(try_double(E, cancelled(A, B), G, cancel(A, B), cancelled(H, I), cancel(H, I), replacement, true, true, anonymous("44"))),
	!,
	'CHRkill'(C),
	coca(fired_rule(anonymous("44"))).
'CHRcancelled_2'(cancelled(A, B), C, D, E) :-
	'CHRcancelled_2__121'(cancelled(A, B), C, D, E).
'CHRcancelled_2__122'(['CHRcancel_2'(cancel(A, B), C, D, E)|F], [B, A], [], G) ?-
	'CHRvar'(C),
	'CHRkill'(C),
	'CHR='([], []),
	'CHR='(E, G).
'CHRcancelled_2__122'([A|B], C, D, E) :-
	'CHRcancelled_2__122'(B, C, D, E).
:- set_flag('CHRcancelled_2__122' / 4, leash, notrace).
:- set_flag('CHRcancelled_2' / 4, leash, notrace).
:- current_macro('CHRcancelled_2' / 4, _60627, _60628, _60629) -> true ; define_macro('CHRcancelled_2' / 4, tr_chr / 2, [write]).
'CHRcancelled_2__121'(A, B, C, D) :-
	'CHRcancelled_2__123'(A, B, C, D).
:- set_flag('CHRcancelled_2__121' / 4, leash, notrace).
'CHRcancelled_2__123'(cancelled(A, B), C, D, E) :-
	(
	    'CHRvar'(C)
	->
	    'CHRdelay'([C, cancelled(A, B)], 'CHRcancelled_2'(cancelled(A, B), C, D, E))
	;
	    true
	).
:- set_flag('CHRcancelled_2__123' / 4, leash, notrace).

:- getval(variable_names_flag, Val), set_flag(variable_names, Val).
