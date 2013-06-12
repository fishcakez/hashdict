-module(hashdict_SUITE).

%% CT callbacks
-export([all/0,
         groups/0]).

%% Testcases
-export([dict_statem/1]).

-include_lib("common_test/include/ct.hrl").

%% CT callbacks

all() ->
    [{group, proper}].

groups() ->
    [{proper, [dict_statem]}].

%% Testcases

dict_statem(_) ->
    case hashdict_statem:quickcheck([{numtests, 250}, {max_size, 50},
                                     long_result, {on_output, fun log/2}]) of
         true ->
             ok;
         {error, Reason} ->
             error(Reason);
         CounterExample ->
             ct:log("Counter Example:~n~p", [CounterExample]),
             error(counterexample)
    end.

%% Custom log format.

log(".", []) ->
    ok;
log("!", []) ->
    ok;
log("OK: " ++ Comment = Format, Args) ->
    ct:comment(no_trailing_newline(Comment), Args),
    io:format(no_trailing_newline(Format), Args);
log("Failed: " ++ Comment = Format, Args) ->
    ct:comment(no_trailing_newline(Comment), Args),
    io:format(no_trailing_newline(Format), Args);
log(Format, Args) ->
    io:format(no_trailing_newline(Format), Args).

no_trailing_newline(Format) ->
    try lists:split(length(Format) - 2, Format) of
         {Format2, "~n"} ->
             Format2;
         _ ->
             Format
    catch
        error:badarg ->
            Format
    end.
