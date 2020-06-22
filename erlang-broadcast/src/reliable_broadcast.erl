-module(reliable_broadcast).

-behavior(gen_server).

-export([start_link/2, broadcast/2]).

% gen_server callbacks
-export([code_change/3, handle_call/3, handle_cast/2, handle_info/2, init/1, terminate/2]).

-record(state, {
	beb :: pid(), % best effort broadcast
	respond_to :: pid(),
	delivered = sets:new(),
	msg_counter = 0, % counter for creating unique identifiers
	self % own name
}).

start_link(LinkLayer, RespondTo) ->
	gen_server:start_link(?MODULE, [LinkLayer, RespondTo], []).

broadcast(B, Msg) ->
	gen_server:call(B, {rb_broadcast, Msg}).


init([LL,R]) ->
	{ok, Beb} = best_effort_broadcast:start_link(LL, self()),
	{ok, ThisNode} = link_layer:this_node(LL),
	{ok, #state{beb=Beb, respond_to=R, self=ThisNode}}.

handle_call({rb_broadcast, Msg}, _From, State) ->
	% deliver self
	State#state.respond_to ! {deliver, Msg},
	% generate new unique message id
	Uid = {State#state.self, State#state.msg_counter},
	NewState = State#state{
		delivered = sets:add_element(Uid, State#state.delivered),
		msg_counter = State#state.msg_counter + 1
	},
	% broadcast to everyone
	best_effort_broadcast:broadcast(State#state.beb, {Uid, Msg}),
	{reply, ok, NewState}.

handle_info({deliver, {Uid, Msg}}, State) ->
	case sets:is_element(Uid, State#state.delivered) of
		true ->
			{noreply, State};
		false ->
			NewState = State#state{delivered=sets:add_element(Uid, State#state.delivered)},
			% deliver self
			State#state.respond_to ! {deliver, Msg},
			% broadcast to everyone
			best_effort_broadcast:broadcast(State#state.beb, {Uid, Msg}),
			{noreply, NewState}
	end.

handle_cast(_Request, State) ->
	{noreply, State}.

terminate(_Reason, _State) ->
	ok.

code_change(_OldVsn, State, _Extra) ->
	{ok, State}.