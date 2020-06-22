-module(link_layer_distr_erl).
% An implementation of the link layer using distributed Erlang

-behaviour(gen_server).

-export([start_link/1]).
-export([init/1, handle_call/3, handle_cast/2, terminate/2, code_change/3, handle_info/2]).

-record(state, {group_name, respond_to}).

start_link(GroupName) ->
    gen_server:start_link(?MODULE, [GroupName], []).

init([GroupName]) ->
    pg2:create(GroupName),
    pg2:join(GroupName, self()),
    {ok, #state{group_name=GroupName, respond_to=none}}.

terminate(_Reason, State) ->
    pg2:leave(State#state.group_name, self()).

handle_call({send, Data, Node}, _From, State) ->
    gen_server:cast(Node, {remote, Data}),
    {reply, ok, State};
handle_call({register, R}, _From, State) ->
    {reply, ok, State#state{respond_to=R}};
handle_call(all_nodes, _From, State) ->
    Members = pg2:get_members(State#state.group_name),
    {reply, {ok, Members}, State};
handle_call(other_nodes, _From, State) ->
    Members = pg2:get_members(State#state.group_name),
    Self = self(),
    OtherMembers = [M || M <- Members, M /= Self],
    {reply, {ok, OtherMembers}, State};
handle_call(this_node, _From, State) ->
    {reply, {ok, self()}, State}.

handle_cast({remote, Msg}, State) ->
    RespondTo = State#state.respond_to,
    RespondTo ! Msg,
    {noreply, State}.

handle_info(_Msg, State) ->
    {noreply, State}.

code_change(_OldVsn, State, _Extra) ->
	{ok, State}.