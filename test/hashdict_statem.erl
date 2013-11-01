-module(hashdict_statem).

-include_lib("proper/include/proper.hrl").
-include_lib("common_test/include/ct.hrl").

-record(state, {dict=dict:new(),
                hashdict=hashdict:new()}).

-export([quickcheck/0]).
-export([quickcheck/1]).
-export([catch_fetch/2]).
-export([catch_take/2]).
-export([catch_append/3]).
-export([catch_append_list/3]).
-export([catch_update/3]).
-export([catch_update_counter/3]).
-export([merge/3]).

-export([initial_state/0]).
-export([command/1]).
-export([next_state/3]).
-export([precondition/2]).
-export([postcondition/3]).

quickcheck() ->
    quickcheck([]).

quickcheck(Opts) ->
    proper:quickcheck(prop_as_dict(), Opts).

prop_as_dict() ->
    ?FORALL(Cmds, commands(?MODULE),
            begin
                {History, State, Result} = run_commands(?MODULE, Cmds),
                ok,
                ?WHENFAIL(begin
                              io:format("History~n~p", [History]),
                              io:format("State~n~p", [State]),
                              io:format("Result~n~p", [Result])
                          end,
                          aggregate(command_names(Cmds), Result =:= ok))
            end).

key() ->
    term().

value() ->
    term().

key(Dict) ->
    elements([Key || Key <- dict:fetch_keys(Dict)]).

key_new(Dict) ->
    ?SUCHTHAT(Key, term(),
              begin
                  dict:find(Key, Dict) =:= error
              end).

dictlist() ->
    list({key(), value()}).

initial_state() ->
    #state{}.

command(#state{dict=Dict, hashdict=Hashdict}) ->
    KeyCur = key(Dict),
    Empty = dict:size(Dict) =:= 0,
    KeyNew = key_new(Dict),
    SplitListVal = fun(Key, Value, {ListAcc, NotListAcc}) when is_list(Value) ->
                          {dict:store(Key, Value, ListAcc), NotListAcc};
                      (Key, Value, {ListAcc, NotListAcc}) ->
                          {ListAcc, dict:store(Key, Value, NotListAcc)}
                   end,
    {DictListVal, DictNotListVal} = dict:fold(SplitListVal,
                                              {dict:new(), dict:new()},
                                              Dict),
    EmptyListVal = dict:size(DictListVal) =:= 0,
    KeyListVal = key(DictListVal),
    EmptyNotListVal = dict:size(DictNotListVal) =:= 0,
    KeyNotListVal = key(DictNotListVal),
    SplitNumVal = fun(Key, Value, {NumAcc, NotNumAcc}) when is_number(Value) ->
                          {dict:store(Key, Value, NumAcc), NotNumAcc};
                      (Key, Value, {NumAcc, NotNumAcc}) ->
                          {NumAcc, dict:store(Key, Value, NotNumAcc)}
                   end,
    {DictNumVal, DictNotNumVal} = dict:fold(SplitNumVal,
                                             {dict:new(), dict:new()},
                                             Dict),
    EmptyNumVal = dict:size(DictNumVal) =:= 0,
    KeyNumVal = key(DictNumVal),
    EmptyNotNumVal = dict:size(DictNotNumVal) =:= 0,
    KeyNotNumVal = key(DictNotNumVal),
    Update = fun(Value) -> {Value} end,
    Fold = fun(Key, Value, Acc) -> [{{Key}, [Value]} | Acc] end,
    Acc = [],
    Map = fun(_Key, Value) -> [Value] end,
    Filter = fun(_Key, Value) -> erlang:phash2(Value, 8) =:= 0 end,
    Merge = fun(_Key, ValueA, ValueB) -> [ValueA, ValueB] end,
    Calls = [[{call, hashdict, is_key, [KeyCur, Hashdict]} || not Empty],
             [{call, hashdict, to_list, [Hashdict]}],
             [{call, hashdict, from_list, [dictlist()]}],
             [{call, hashdict, size, [Hashdict]}],
             [{call, hashdict, fetch, [KeyCur, Hashdict]} || not Empty],
             [{call, ?MODULE, catch_fetch, [KeyNew, Hashdict]}],
             [{call, hashdict, find, [KeyCur, Hashdict]} || not Empty],
             [{call, hashdict, find, [KeyNew, Hashdict]}],
             [{call, hashdict, fetch_keys, [Hashdict]}],
             [{call, hashdict, take, [KeyCur, Hashdict]} || not Empty],
             [{call, ?MODULE, catch_take, [KeyNew, Hashdict]}],
             [{call, hashdict, erase, [KeyCur, Hashdict]} || not Empty],
             [{call, hashdict, erase, [KeyNew, Hashdict]}],
             [{call, hashdict, store, [KeyNew, value(), Hashdict]}],
             [{call, hashdict, store,
               [KeyCur, value(), Hashdict]} || not Empty],
             [{call, hashdict, append,
               [KeyListVal, value(), Hashdict]} || not EmptyListVal],
             [{call, hashdict, append, [KeyNew, value(), Hashdict]}],
             [{call, ?MODULE, catch_append,
               [KeyNotListVal, value(), Hashdict]} || not EmptyNotListVal],
             [{call, hashdict, append_list,
               [KeyListVal, list(), Hashdict]} || not EmptyListVal],
             [{call, hashdict, append_list, [KeyNew, list(), Hashdict]}],
             [{call, ?MODULE, catch_append_list,
               [KeyNotListVal, value(), Hashdict]} || not EmptyNotListVal],
             [{call, hashdict, update,
               [KeyCur, Update, Hashdict]} || not Empty],
             [{call, ?MODULE, catch_update, [KeyNew, Update, Hashdict]}],
             [{call, hashdict, update,
               [KeyCur, Update, value(), Hashdict]} || not Empty],
             [{call, hashdict, update, [KeyNew, Update, value(), Hashdict]}],
             [{call, hashdict, update_counter,
               [KeyNumVal, number(), Hashdict]} || not EmptyNumVal],
             [{call, hashdict, update_counter, [KeyNew, number(), Hashdict]}],
             [{call, ?MODULE, catch_update_counter,
               [KeyNotNumVal, number(), Hashdict]} || not EmptyNotNumVal],
             [{call, hashdict, fold, [Fold, Acc, Hashdict]}],
             [{call, hashdict, map, [Map, Hashdict]}],
             [{call, hashdict, filter, [Filter, Hashdict]}],
             [{call, ?MODULE, merge, [Merge,  dictlist(), Hashdict]}]],
    oneof(lists:flatten(Calls)).

catch_fetch(Key, Hashdict) ->
    catch hashdict:fetch(Key, Hashdict).

catch_take(Key, Hashdict) ->
    catch hashdict:take(Key, Hashdict).

catch_append(Key, Value, Hashdict) ->
    catch hashdict:append(Key, Value, Hashdict).

catch_append_list(Key, Value, Hashdict) ->
    catch hashdict:append_list(Key, Value, Hashdict).

catch_update(Key, Update, Hashdict) ->
    catch hashdict:update(Key, Update, Hashdict).

catch_update_counter(Key, Incr, Hashdict) ->
    catch hashdict:update_counter(Key, Incr, Hashdict).

merge(Merge, DictList, Hashdict) ->
    hashdict:merge(Merge, hashdict:from_list(DictList), Hashdict).

next_state(State, V, {call, _, from_list, [List]}) ->
    State#state{dict=dict:from_list(List),
                hashdict=V};
next_state(#state{dict=Dict} = State, V, {call, _, take, [Key, _]}) ->
    V2 = {call, erlang, element, [3, V]},
    State#state{dict=dict:erase(Key, Dict),
                hashdict=V2};
next_state(#state{dict=Dict} = State, V, {call, _, erase, [Key, _]}) ->
    State#state{dict=dict:erase(Key, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V, {call, _, store, [Key, Value, _]}) ->
    State#state{dict=dict:store(Key, Value, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V, {call, _, append, [Key, Value, _]}) ->
    State#state{dict=dict:append(Key, Value, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V,
           {call, _, append_list, [Key, Value, _]}) ->
    State#state{dict=dict:append_list(Key, Value, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V, {call, _, update, [Key, Update, _]}) ->
    State#state{dict=dict:update(Key, Update, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V,
           {call, _, update, [Key, Update, Value, _]}) ->
    State#state{dict=dict:update(Key, Update, Value, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V,
           {call, _, update_counter, [Key, Incr, _]}) ->
    State#state{dict=dict:update_counter(Key, Incr, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V, {call, _, map, [Map, _]}) ->
    State#state{dict=dict:map(Map, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V, {call, _, filter, [Filter, _]}) ->
    State#state{dict=dict:filter(Filter, Dict),
                hashdict=V};
next_state(#state{dict=Dict} = State, V,
           {call, _, merge, [Merge, DictList, _]}) ->
    Dict2 = dict:from_list(DictList),
    State#state{dict=dict:merge(Merge, Dict2, Dict),
                hashdict=V};
next_state(State, _V, _Call) ->
    State.

precondition(_State, _Call) ->
    true.

postcondition(#state{dict=Dict}, {call, _, is_key, [Key, _]}, Result) ->
    dict:is_key(Key, Dict) =:= Result;
postcondition(#state{dict=Dict}, {call, _, to_list, _}, Result) ->
    lists_equal(dict:to_list(Dict), Result);
postcondition(_, {call, _, from_list, [List]}, Hashdict) ->
    dicts_check(dict:from_list(List), Hashdict);
postcondition(#state{dict=Dict}, {call, _, size, _}, Result) ->
    dict:size(Dict) =:= Result;
postcondition(#state{dict=Dict}, {call, _, fetch, [Key, _]}, Result) ->
    dict:fetch(Key, Dict) =:= Result;
postcondition(_State, {call, _, catch_fetch, _}, Result) ->
    check_exit(fetch, Result);
postcondition(#state{dict=Dict}, {call, _, find, [Key, _]}, Result) ->
    dict:find(Key, Dict) =:= Result;
postcondition(#state{dict=Dict}, {call, _, fetch_keys, _}, Result) ->
    lists_equal(dict:fetch_keys(Dict), Result);
postcondition(#state{dict=Dict}, {call, _, take, [Key, _]},
              {Key, Value, Hashdict}) ->
    Dict2 = dict:erase(Key, Dict),
    dict:fetch(Key, Dict) =:= Value andalso dicts_equal(Dict2, Hashdict);
postcondition(_, {call, _, take, _}, _) ->
    false;
postcondition(_State, {call, _, catch_take, _}, Result) ->
    check_exit(take, Result);
postcondition(_State, {call, _, catch_append, _}, Result) ->
    check_exit(append, Result);
postcondition(_State, {call, _, catch_append_list, _}, Result) ->
    check_exit(append_list, Result);
postcondition(_State, {call, _, catch_update, _}, Result) ->
    check_exit(update, Result);
postcondition(_State, {call, _, catch_update_counter, _}, Result) ->
    check_exit(update_counter, Result);
postcondition(#state{dict=Dict}, {call, _, fold, [Fun, Acc, _]}, Result) ->
    lists_equal(dict:fold(Fun, Acc, Dict), Result);
postcondition(#state{dict=Dict}, {call, _, merge, [Merge, DictList, _]},
              Hashdict) ->
    dicts_check(dict:merge(Merge, dict:from_list(DictList), Dict), Hashdict);
postcondition(#state{dict=Dict}, {call, _, Fun, Args}, Hashdict) ->
    %% Hashdict is always last arg in remaining functions and Hashdict is always
    %% returned.
    Args2 = lists:reverse([Dict | tl(lists:reverse(Args))]),
    Dict2 = erlang:apply(dict, Fun, Args2),
    dicts_check(Dict2, Hashdict).

lists_equal(A, B) ->
    SetA = sets:from_list(A),
    SetB = sets:from_list(B),
    sets:is_subset(SetA, SetB) andalso sets:is_subset(SetB, SetA).

dicts_check(undefined = Dict, Hashdict) ->
    case hashdict:info(mode, Hashdict) of
        ordered ->
            ordered_check(Hashdict) andalso dicts_equal(Dict, Hashdict);
        trie ->
            trie_check(Hashdict) andalso dicts_equal(Dict, Hashdict)
    end;
dicts_check(Dict, Hashdict) ->
    dicts_equal(Dict, Hashdict).

ordered_check(Hashdict) ->
    Threshold = hashdict:info(ordered_threshold, Hashdict),
    case hashdict:size(Hashdict) of
         Size when Size =< Threshold ->
            true;
         _Size ->
             false
    end.

trie_check(Hashdict) ->
    Root = hashdict:info(root, Hashdict),
    is_tuple(Root) andalso trie_check_element(Root, Hashdict).

trie_check_element(Node, Hashdict) when is_tuple(Node) ->
    Elems = tuple_to_list(Node),
    NonEmptyElems = [Elem || Elem <- Elems, Elem =/= []],
    tuple_size(Node) =:= hashdict:info(node_size, Hashdict) andalso
    [] =:= [error ||
            Elem <- Elems, not trie_check_element(Elem, Hashdict)] andalso
    %% A node should contract when it has 1 non empty bucket whose number of
    %% k-v pairs is equal to or less than the contract load.
    length(NonEmptyElems) =/= 0 andalso
    (length(NonEmptyElems) =/= 1 orelse
     is_tuple(hd(NonEmptyElems)) orelse
     length(hd(NonEmptyElems)) > hashdict:info(contract_load, Hashdict));
trie_check_element(Bucket, Hashdict) when is_list(Bucket) ->
    length(Bucket) < hashdict:info(expand_load, Hashdict).

dicts_equal(Dict, Hashdict) ->
    List = hashdict:to_list(Hashdict),
    (dict:size(Dict) =:= hashdict:size(Hashdict) andalso
     length(List) =:= hashdict:size(Hashdict) andalso
     lists_equal(dict:to_list(Dict), List)).

check_exit(update_counter, {'EXIT', {badarith, _}}) ->
    true;
check_exit(Fun, {'EXIT', {badarg, _}}) when Fun =/= update_counter ->
    true;
check_exit(_Fun, _Result) ->
    false.
