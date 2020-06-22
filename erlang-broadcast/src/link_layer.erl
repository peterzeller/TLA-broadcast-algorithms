-module(link_layer).


%% API
-export([send/3, register/2, all_nodes/1, other_nodes/1, this_node/1]).

%% sends Data to other Node
send(LL, Data, Node) ->
    gen_server:call(LL, {send, Data, Node}).

%% Registers a receiver: all future messages will be delivered to the registered process
register(LL, Receiver) ->
    gen_server:call(LL, {register, Receiver}).

%% get all nodes (including own node)
all_nodes(LL) ->
    gen_server:call(LL, all_nodes).

%% get all other nodes
other_nodes(LL) ->
    gen_server:call(LL, other_nodes).

%% get this node
this_node(LL) ->
    gen_server:call(LL, this_node).
