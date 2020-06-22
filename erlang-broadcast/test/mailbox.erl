-module(mailbox).

-export([new/0, read/1]).

new() ->
	spawn_link(fun() -> mailbox_loop([]) end).

mailbox_loop(Msgs) ->
	receive
		{read_mailbox, P} ->
			P ! {read_mailbox_resp, lists:reverse(Msgs)},
			mailbox_loop(Msgs);
		X ->
			mailbox_loop([X|Msgs])
	end.

read(M) ->
	M!{read_mailbox, self()},
	receive {read_mailbox_resp, X} -> X end.