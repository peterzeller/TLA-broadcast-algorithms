-module(causal_broadcast).

-behavior(gen_server).

-export([start_link/2, broadcast/2]).

% gen_server callbacks
-export([code_change/3, handle_call/3, handle_cast/2, handle_info/2, init/1, terminate/2]).

-record(state, {
    rb :: pid(), % reliable broadcast
    respond_to :: pid(),
    pending = sets:new(), % pending messages
    vc = vectorclock:new(),
    self % own name
}).

start_link(LinkLayer, RespondTo) ->
    gen_server:start_link(?MODULE, [LinkLayer, RespondTo], []).

broadcast(B, Msg) ->
    gen_server:call(B, {rco_broadcast, Msg}).


init([LL,R]) ->
    {ok, Rb} = reliable_broadcast:start_link(LL, self()),
    {ok, ThisNode} = link_layer:this_node(LL),
    {ok, #state{rb=Rb, respond_to=R, self=ThisNode}}.

handle_call({rco_broadcast, Msg}, _From, State) ->
    % deliver self
    State#state.respond_to ! {deliver, Msg},
    % broadcast to everyone
    reliable_broadcast:broadcast(State#state.rb, {State#state.self, State#state.vc, Msg}),
    % increment vectorclock
    NewState = State#state{
        vc = vectorclock:increment(State#state.vc, State#state.self)
    },
    {reply, ok, NewState}.

handle_info({deliver, {P, VC, M}}, State) ->
    case P == State#state.self of
        true ->
            {noreply, State};
        false ->
            Pending = sets:add_element({P, VC, M}, State#state.pending),
            {NewPending, NewVc} = deliver_pending(State, Pending, State#state.vc),
            {noreply, State#state{pending = NewPending, vc = NewVc}}
    end.

deliver_pending(State, Pending, Vc) ->
    CanDeliver = sets:filter(fun({_, VcQ, _}) -> vectorclock:leq(VcQ, Vc) end, Pending),
    case sets:size(CanDeliver) of
        0 ->
            {Pending, Vc};
        _ ->
            NewPending = sets:subtract(Pending, CanDeliver),
            NewVc = sets:fold(fun({Q, _, M}, VcA) ->
                State#state.respond_to ! {deliver, M},
                vectorclock:increment(VcA, Q)
            end, Vc, CanDeliver),
            deliver_pending(State, NewPending, NewVc)
    end.





handle_cast(_Request, State) ->
    {noreply, State}.

terminate(_Reason, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.