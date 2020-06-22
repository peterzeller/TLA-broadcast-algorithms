-module(vectorclock_tests).
-include_lib("eunit/include/eunit.hrl").

% Creates a vectorclock from a list of key-value pairs
vc([]) -> vectorclock:new();
vc([{P,0}|R]) -> vc(R);
vc([{P,N}|R]) -> vectorclock:increment(vc([{P,N-1}|R]), P).

increment_test() ->
	V0 = vectorclock:new(),
	?assertEqual(0, vectorclock:get(V0, p1)),
	V1 = vectorclock:increment(V0, p1),
	?assertEqual(1, vectorclock:get(V1, p1)).

get_test() ->
	V = vc([{p1, 3}, {p2, 4}, {p3, 1}]),
	?assertEqual(3, vectorclock:get(V, p1)),
	?assertEqual(4, vectorclock:get(V, p2)),
	?assertEqual(1, vectorclock:get(V, p3)).

leq1_test() ->
	A = vc([{p1, 3}, {p2, 4}, {p3, 1}]),
	B = vc([{p1, 6}, {p2, 4}, {p3, 2}]),
	?assertEqual(true, vectorclock:leq(A, B)).

leq2_test() ->
	A = vc([{p1, 3}, {p3, 1}]),
	B = vc([{p1, 6}, {p2, 4}, {p3, 2}]),
	?assertEqual(true, vectorclock:leq(A, B)).

leq3_test() ->
	A = vc([{p1, 3}, {p2, 4}, {p3, 1}]),
	B = vc([{p1, 6}, {p2, 3}, {p3, 2}]),
	?assertEqual(false, vectorclock:leq(A, B)).

merge1_test() ->
	A = vc([{p1, 3}, {p2, 5}, {p3, 1}]),
	B = vc([{p1, 6}, {p2, 4}, {p3, 2}]),
	C = vectorclock:merge(A, B),
	?assertEqual(6, vectorclock:get(C, p1)),
	?assertEqual(5, vectorclock:get(C, p2)),
	?assertEqual(2, vectorclock:get(C, p3)).

merge2_test() ->
	A = vc([         {p2, 5}, {p3, 1}]),
	B = vc([{p1, 6}, {p2, 4}         ]),
	C = vectorclock:merge(A, B),
	?assertEqual(6, vectorclock:get(C, p1)),
	?assertEqual(5, vectorclock:get(C, p2)),
	?assertEqual(1, vectorclock:get(C, p3)).