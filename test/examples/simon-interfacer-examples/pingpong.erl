%% Based on an example from the Erlang/OTP documentation.

-module(pingpong).
-export([start/0,ping/2,pong/0]).

-type ping_message_T() :: {ping, pid():ping_T()}.
-type pong_message_T() :: pong.
-type finished_T() :: finished.
-type ping_T() :: pong_message_T().
-type pong_T() :: ping_message_T() | finished_T().

%% We need a way of refining type pid() by specifying an interface.
%% For now, write this as pid():interface_type(), but maybe it should be pid(interface_type())
%% or something different.

-interface ping:ping_T(). %% Messages sent to a process running this function have type ping_T().
                          %% Within this function, self() has type pid():ping_T(). 
-spec ping(integer(), pid():pong_T()) -> no_return().
ping(0, Pong_PID) ->
	Pong_PID ! finished, %% Check that finished has type pong_T().
	io:format("ping finished~n");

ping(N, Pong_PID) ->
	Pong_PID ! {ping, self()}, %% Check that {ping, self()} has type pong_T().
	receive %% Check that the guards are within ping_T().
		pong ->
			io:format("Ping received pong~n")
	end,
	ping(N - 1, Pong_PID).

-interface pong:pong_T(). %% Messages sent to a process running this function have type pong_T().
-spec pong() -> no_return()
pong() ->
	receive %% Check that the guards are within pong_T().
		finished ->
			io:format("pong finished~n");
		{ping, Ping_PID} -> %% Check that Ping_PID is used with type pid():ping_T().
			Ping_PID ! pong, %% Check that pong has type ping_T().
			pong()
	end.

-spec start() -> no_return()
start() ->
	io:format("Starting.~n"),
	Pong_PID = spawn(pingpong, pong, []), %% Pong_PID has type pid():pong_T().
	spawn(pingpong, ping, [3, Pong_PID]). %% Check that Pong_PID has type pid():pong_T().