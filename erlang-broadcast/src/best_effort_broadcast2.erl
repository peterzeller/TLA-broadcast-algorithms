-module(best_effort_broadcast2).
% alternative implementation without gen_server
-export([start_link/2, broadcast/2]).

start_link(LL, RespondTo)->
    Pid = spawn_link(fun() -> loop(LL, RespondTo) end),
    link_layer:register(LL, Pid),
    {ok, Pid}.

loop(LL, RespondTo)->
    receive
        {broadcast, Msg} ->
            {ok, AllNodes} = link_layer:all_nodes(LL),
            lists:foreach(fun(N) ->
                link_layer:send(LL, {best_effort_broadcast_msg, Msg}, N)
            end, AllNodes),
            loop(LL, RespondTo);
        {best_effort_broadcast_msg, Msg} ->
            RespondTo ! {deliver, Msg},
            loop(LL, RespondTo)
    end.

broadcast(Beb, Message)->
    Beb ! {broadcast, Message},
    ok.
