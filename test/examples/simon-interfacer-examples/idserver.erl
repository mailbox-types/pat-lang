-module(idserver).
-export([client/0]).

-type get_message_T() :: {get, pid():client_T()}.
-type init_message_T() :: {init, integer()}.
-type id_server_T() :: init_message_T() | get_message_T().
-type client_T() :: {id, integer()}.

-interface id_server:id_server_T(). %% Messages sent to a process running this function have type id_server_T().
-spec id_server() -> no_return()
id_server() ->
	receive %% Check that the guards are within id_server_T().
		{init, N} -> id_server_loop(N)
	end.

-spec id_server_loop(integer()).
id_server_loop(N) ->
	receive %% Check that the guards are within id_server_T().
		{get, Client} -> %% Check that Client is used with type pid():client_T().
			Client ! {id, N}, %% Check that N has type integer().
			id_server_loop(N + 1);
		{init, _} -> error %% Defensive code because we don't have mailbox types.
	end.

-interface client:client_T() %% Messages sent to a process running this function have type client_T().
                             %% Within this function, self() has type client_T().
-spec client() -> no_return()
client() ->
	Server = spawn(fun id_server/0), %% Server has type pid():id_server_T().
	Server ! {init, 5}, %% Check that {init, 5} has type id_server_T().
	Server ! {get, self()}, %% Check that {get, self()} has type id_server_T().
	receive
		{id, Id} -> io:format("Client received ~p.~n", [Id]) %% Check that Id is used with type integer().
	end.