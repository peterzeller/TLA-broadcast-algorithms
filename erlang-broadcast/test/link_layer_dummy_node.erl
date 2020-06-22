-module(link_layer_dummy_node).
% An implementation of the link layer for testing
% Provides additional methods to simulate node crashes

-behaviour(gen_server).

-export([start/2]).
-export([init/1, handle_call/3, handle_cast/2, terminate/2, code_change/3, handle_info/2]).

-record(state, {
    self :: atom(), % name of this node
	network :: pid(), % gen server running link_layer_dummy
    respond_to = undefined :: pid()  % process to answer to
}).

start(Network, NodeName) ->
    gen_server:start_link(?MODULE, [Network, NodeName], []).

init([Network, NodeName]) ->
    {ok, #state{network=Network, self=NodeName}}.

terminate(_Reason, _State) ->
    ok.

handle_call({send, Data, Node}, _From, State) ->
    gen_server:call(State#state.network, {add_message, State#state.self, Node, Data}),
    {reply, ok, State};
handle_call({register, R}, _From, State) ->
    {reply, ok, State#state{respond_to=R}};
handle_call(all_nodes, _From, State) ->
    {ok, Members} = gen_server:call(State#state.network, all_nodes),
    {reply, {ok, Members}, State};
handle_call(other_nodes, _From, State) ->
    {ok, Members} = gen_server:call(State#state.network, all_nodes),
    Self = State#state.self,
    OtherMembers = [M || M <- Members, M /= Self],
    {reply, {ok, OtherMembers}, State};
handle_call(this_node, _From, State) ->
    {reply, {ok, State#state.self}, State}.

handle_cast(Msg, State) ->
    io:format("dummy_node unhandled cast message: ~p~n", [Msg]),
    {noreply, State}.

handle_info({remote, Msg}, State) ->
    RespondTo = State#state.respond_to,
    RespondTo ! Msg,
    {noreply, State};
handle_info(Msg, State) ->
    io:format("dummy_node unhandled message: ~p~n", [Msg]),
    {noreply, State}.

code_change(_OldVsn, State, _Extra) ->
	{ok, State}.