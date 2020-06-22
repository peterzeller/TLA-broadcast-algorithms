-module(link_layer_dummy).
-include_lib("eunit/include/eunit.hrl").
% An implementation of the link layer for testing
% Provides additional methods to simulate node crashes

-behaviour(gen_server).

-export([start_link/1, finish/1, deliver_all/1, deliver/4, crash/2]).
-export([init/1, handle_call/3, handle_cast/2, terminate/2, code_change/3, handle_info/2]).

-record(state, {
    nodes :: orddict:orddict(Name::atom(), pid()),
    crashed_nodes = sets:new() :: sets:set(atom()),
    messages = [] :: [{From::pid(), To::pid(), Msg::any()}]
}).

% Start the dummy layer with length(NodeNames) nodes
start_link(NodeNames) ->
    {ok, LL} = gen_server:start_link(?MODULE, [NodeNames], []),
    Processes = gen_server:call(LL, get_node_processes),
    {ok, LL, Processes}.

% deliver all messages until the protocol completes
finish(LL) ->
    gen_server:call(LL, finish).

% deliver all messages currently in transition
deliver_all(LL) ->
    gen_server:call(LL, deliver_all).

% deliver the Nth message that is currently in transition between From and To
% if there is no such message, nothing happens
% if N is greater or equal to the number of messages, a modulo operation is performed
deliver(LL, From, To, N) ->
    gen_server:call(LL, {deliver, From, To, N}).

% crashes the given node
% no more messages will be delivered to or from this node
crash(LL, Node) ->
    gen_server:call(LL, {crash, Node}).



init([NodeNames]) ->
    Nodes = lists:map(fun(Name) ->
        {ok, Pid} = link_layer_dummy_node:start(self(), Name),
        {Name, Pid}
      end, NodeNames),
    {ok, #state{nodes = orddict:from_list(Nodes)}}.

terminate(_Reason, _State) ->
    ok.

node_pid(State, Node) ->
    {ok, Pid} = orddict:find(Node, State#state.nodes),
    Pid.

is_crashed(State, Node) ->
    sets:is_element(Node, State#state.crashed_nodes).

deliver(State, To, Msg) ->
    case is_crashed(State, To) of
        true ->
            ignore;
        false ->
            node_pid(State, To) ! {remote, Msg}
    end.


handle_call({add_message, From, To, Msg}, _From, State) ->
    Msgs = case is_crashed(State, To) of
        true ->
            State#state.messages;
        false ->
            State#state.messages ++ [{From, To, Msg}]
    end,
    {reply, ok, State#state{messages=Msgs}};
handle_call(get_node_processes, _From, State) ->
    Pids = [P || {_,P} <- State#state.nodes],
    {reply, Pids, State};
handle_call(all_nodes, _From, State) ->
    Members = [Name || {Name,_} <- State#state.nodes],
    {reply, {ok, Members}, State};
handle_call({crash, Node}, _From, State) ->
    NewState = State#state{
        % add node to crashed nodes:
        crashed_nodes = sets:add_element(Node, State#state.crashed_nodes),
        % remove pending messages from crashed node,
        messages = [{From, To, Msg} || {From, To, Msg} <- State#state.messages, From /= Node]
    },
    {reply, ok, NewState};
handle_call(deliver_all, _From, State) ->
    [deliver(State, To, Msg) || {_, To, Msg} <- State#state.messages],
    Delivered = length(State#state.messages),
    {reply, {ok, Delivered}, State#state{messages = []}};
handle_call({deliver, From, To, N}, _From, State) ->
    Msgs = [{F,T,M} || {F,T,M} <- State#state.messages, F == From, T == To],
    case length(Msgs) of
        0 ->
            {reply, ok, State};
        MsgCount ->
            Msg = {_, T, M} = lists:nth(1 + (N rem MsgCount), Msgs),
            deliver(State, T, M),
            NewMsgs = lists:delete(Msg, State#state.messages),
            {reply, ok, State#state{messages = NewMsgs}}
    end;
handle_call(finish, From, State) ->
    Self = self(),
    spawn_link(fun() -> finish(Self, false, From) end),
    {noreply, State}.

finish(LL, Zero, ReplyTo) ->
    {ok, Count} = gen_server:call(LL, deliver_all),
    case {Zero, Count} of
        {true, 0} ->
            gen_server:reply(ReplyTo, ok);
        {false, 0} ->
            timer:sleep(10),
            finish(LL, true, ReplyTo);
        _ ->
            finish(LL, false, ReplyTo)
    end.


handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info(_Msg, State) ->
    {noreply, State}.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.



link_layer_dummy_test() ->
    % initialize dummy link layer:
    {ok, LL, [NodeA, NodeB]} = link_layer_dummy:start_link([nodeA, nodeB]),
    M1 = mailbox:new(),
    M2 = mailbox:new(),
    link_layer:register(NodeA, M1),
    link_layer:register(NodeB, M2),
    link_layer:send(NodeA, ping, nodeB),
    link_layer:send(NodeB, pong, nodeA),
    gen_server:call(LL, deliver_all),
    ?assertEqual([ping], mailbox:read(M2)),
    ?assertEqual([pong], mailbox:read(M1)).