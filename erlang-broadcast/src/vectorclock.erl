-module(vectorclock).

-export([new/0, increment/2, get/2, leq/2, merge/2, from_list/1, to_list/1]).

new() ->
    maps:new().

from_list(List) ->
    maps:from_list(List).

to_list(VC) ->
    maps:to_list(VC).

increment(VC, P) ->
    maps:put(P, get(VC, P) + 1, VC).

get(VC, P) ->
    maps:get(P, VC, 0).

leq(VC1, VC2) ->
    maps:fold(fun(P, V, Res) -> Res andalso get(VC2, P) >= V end, true, VC1).

merge(VC1, VC2) ->
    M = maps:merge(VC1, VC2),
    maps:fold(fun(P, V, Res) ->
        maps:put(P, max(V, get(Res, P)), Res)
    end, M, VC1).

