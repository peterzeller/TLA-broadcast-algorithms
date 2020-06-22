-module(causal_broadcast_tests).

-include_lib("eunit/include/eunit.hrl").

% a simple chat server for testing the broadcast:
chat_server(LL) ->
    {ok, B} = causal_broadcast:start_link(LL, self()),
    chat_loop(B, []).

chat_loop(B, Received) ->
    receive
        {post, From, Msg} ->
            causal_broadcast:broadcast(B, Msg),
            From ! {self(), ok},
            chat_loop(B, Received);
        {deliver, Msg} ->
            chat_loop(B, [Msg|Received]);
        {get_received, From} ->
            From ! {self(), lists:reverse(Received)},
            chat_loop(B, Received)
    end.

no_crash_test() ->
    % Create dummy link layer for testing:
    TestNodes = [nodeA, nodeB, nodeC],
    {ok, LLD, [LL1, LL2, LL3]} = link_layer_dummy:start_link(TestNodes),

    % Create 3 chat servers:
    Chat1 = spawn_link(fun() -> chat_server(LL1) end),
    Chat2 = spawn_link(fun() -> chat_server(LL2) end),
    Chat3 = spawn_link(fun() -> chat_server(LL3) end),

    % post a message to chatserver 1
    Chat1 ! {post, self(), 'Hello everyone!'},
    receive {Chat1, ok} -> ok end,

    % finish exchanging messages
    link_layer_dummy:finish(LLD),

    % check that all chat-servers got the message:
    Chat1 ! {get_received, self()},
    Chat2 ! {get_received, self()},
    Chat3 ! {get_received, self()},
    receive {Chat1, Received1} -> ok end,
    receive {Chat2, Received2} -> ok end,
    receive {Chat3, Received3} -> ok end,
    ?assertEqual(['Hello everyone!'], Received1),
    ?assertEqual(['Hello everyone!'], Received2),
    ?assertEqual(['Hello everyone!'], Received3).



with_crash_test() ->
    % Create dummy link layer for testing:
    TestNodes = [nodeA, nodeB, nodeC],
    {ok, LLD, [LL1, LL2, LL3]} = link_layer_dummy:start_link(TestNodes),

    % Create 3 chat servers:
    Chat1 = spawn_link(fun() -> chat_server(LL1) end),
    Chat2 = spawn_link(fun() -> chat_server(LL2) end),
    Chat3 = spawn_link(fun() -> chat_server(LL3) end),

    % post a message to chatserver 1
    Chat1 ! {post, self(), 'Hello everyone!'},
    receive {Chat1, ok} -> ok end,

    % deliver one message from nodeA to nodeB:
    link_layer_dummy:deliver(LLD, nodeA, nodeB, 0),
    % then crash nodeA -> message from nodeA to nodeC is lost
    link_layer_dummy:crash(LLD, nodeA),
    % finish sending all messages
    link_layer_dummy:finish(LLD),

    % Chat1 and Chat2 are not crashed, so they both should have received the message:
    Chat2 ! {get_received, self()},
    Chat3 ! {get_received, self()},
    receive {Chat2, Received2} -> ok end,
    receive {Chat3, Received3} -> ok end,
    ?assertEqual(['Hello everyone!'], Received2),
    ?assertEqual(['Hello everyone!'], Received3).



causality_test() ->
    % Create dummy link layer for testing:
    TestNodes = [nodeA, nodeB, nodeC],
    {ok, LLD, [LL1, LL2, LL3]} = link_layer_dummy:start_link(TestNodes),

    % Create 3 chat servers:
    Chat1 = spawn_link(fun() -> chat_server(LL1) end),
    Chat2 = spawn_link(fun() -> chat_server(LL2) end),
    Chat3 = spawn_link(fun() -> chat_server(LL3) end),

    % post a message to chatserver 1
    Chat1 ! {post, self(), 'How are you?'},
    receive {Chat1, ok} -> ok end,

    % deliver message to chatserver 2
    link_layer_dummy:deliver(LLD, nodeA, nodeB, 0),
    % wait for message to be handled
    timer:sleep(1),

    % Chat 2 should have received the message:
    Chat2 ! {get_received, self()},
    receive {Chat2, Rcv2} -> ok end,
    ?assertEqual(['How are you?'], Rcv2),

    % post a message to Chat 2
    Chat2 ! {post, self(), 'fine'},
    receive {Chat2, ok} -> ok end,

    % deliver message from 2 to 3 (skipping one message)
    link_layer_dummy:deliver(LLD, nodeB, nodeC, 1),

    % finish exchanging messages
    link_layer_dummy:finish(LLD),

    % check that all chat-servers got the message:
    Chat1 ! {get_received, self()},
    Chat2 ! {get_received, self()},
    Chat3 ! {get_received, self()},
    receive {Chat1, Received1} -> ok end,
    receive {Chat2, Received2} -> ok end,
    receive {Chat3, Received3} -> ok end,
    ?assertEqual(['How are you?', 'fine'], Received1),
    ?assertEqual(['How are you?', 'fine'], Received2),
    ?assertEqual(['How are you?', 'fine'], Received3).
