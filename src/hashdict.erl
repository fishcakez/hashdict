%% Copyright (c) 2012-2013, Plataformatec
%% Copyright (c) 2013, James Fish <james@fishcakez.com>
%%
%% This file is provided to you under the Apache License,
%% Version 2.0 (the "License"); you may not use this file
%% except in compliance with the License.  You may obtain
%% a copy of the License at
%%
%%   http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing,
%% software distributed under the License is distributed on an
%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%% KIND, either express or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
-module(hashdict).

%% Original source:
%% https://github.com/elixir-lang/elixir/blob/c0547a15cebcb401fd0ac64d158301301685b2ff/lib/elixir/lib/hash_dict.ex

-compile({inline, [hash/1, shift/1, index/1, index/2]}).

%% dict api (and take/2)
-export([new/0]).
-export([is_key/2]).
-export([to_list/1]).
-export([from_list/1]).
-export([size/1]).
-export([fetch/2]).
-export([find/2]).
-export([fetch_keys/1]).
-export([take/2]).
-export([erase/2]).
-export([store/3]).
-export([append/3]).
-export([append_list/3]).
-export([update/3]).
-export([update/4]).
-export([update_counter/3]).
-export([fold/3]).
-export([map/2]).
-export([filter/2]).
-export([merge/3]).

%% private
-export([info/2]).

-define(ORDERED_THRESHOLD, 8).
-define(EXPAND_LOAD, 5).
-define(CONTRACT_LOAD, 3).
-define(NODE_BITMAP, 2#111).
-define(NODE_SHIFT, 3).
-define(NODE_SIZE, 8). % ?NODE_TEMPLATE and dict_node() assume this is 8.
-define(NODE_TEMPLATE, {[],[],[],[],[],[],[],[]}).

-define(KV(Key, Value), [Key | Value]).

-type bucket() :: [?KV(term(), term())].
-type dict_node() :: {dict_node(), dict_node(), dict_node(), dict_node(),
                      dict_node(), dict_node(), dict_node(), dict_node()} |
                     {bucket(), bucket(), bucket(), bucket(),
                      bucket(), bucket(), bucket(), bucket()}.
-record(hashdict, {size = 0 :: non_neg_integer(),
                   root = [] :: bucket() | dict_node()}).

-opaque hashdict() :: #hashdict{}.

-export_type([hashdict/0]).

-spec new() -> hashdict().
new() ->
    #hashdict{}.

-spec is_key(term(), hashdict()) -> boolean().
is_key(Key, Dict) ->
    case find(Key, Dict) of
         {_ok, _Value} ->
             true;
         _error ->
             false
    end.

-spec to_list(hashdict()) -> [{term(), term()}].
to_list(Dict) ->
    fold(fun(Key, Value, Acc) -> [{Key, Value} | Acc] end, [], Dict).

-spec from_list([{term(), term()}]) -> hashdict().
from_list(List) ->
    lists:foldl(fun({Key, Value}, Dict) -> store(Key, Value, Dict) end, new(),
                List).

-spec size(hashdict()) -> non_neg_integer().
size(#hashdict{size=Size}) ->
    Size.

-spec fetch(term(), hashdict()) -> term().
fetch(Key, Dict) ->
    case find(Key, Dict) of
         {_ok, Value} ->
             Value;
         error ->
             error(badarg, [Key, Dict])
    end.

-spec find(term(), hashdict()) -> {ok, term()} | error.
find(Key, #hashdict{root=Bucket}) when is_list(Bucket) ->
    bucket_find(Bucket, Key);
find(Key, #hashdict{root=Root}) ->
    Bucket = bucket_get(Root, hash(Key)),
    bucket_find(Bucket, Key).

-spec fetch_keys(hashdict()) -> [term()].
fetch_keys(Dict) ->
    fold(fun(Key, _Value, Acc) -> [Key | Acc] end, [], Dict).

%% @doc Returns {Key, Value, Dict2} if Key exists in Dict. Dict2 is Dict with
%% Key removed. If Key does not exist, fails with badarg.
-spec take(term(), hashdict()) -> {term(), term(), hashdict()}.
take(Key, #hashdict{size=Size, root=Bucket} = Dict) when is_list(Bucket) ->
    case bucket_take(Bucket, Key) of
         {Bucket2, -1, Value} ->
             {Key, Value, Dict#hashdict{size=(Size-1), root=Bucket2}};
         {_Bucket2, 0, error} ->
             error(badarg, [Key, Dict])
    end;
take(Key, #hashdict{size=Size, root=Root} = Dict) ->
    Fun = fun(Bucket) -> bucket_take(Bucket, Key) end,
    case bucket_apply_info(Root, hash(Key), Fun) of
         {Root2, -1, Value} ->
             {Key, Value, Dict#hashdict{size=(Size-1), root=Root2}};
         {_Root2, 0, error} ->
             error(badarg, [Key, Dict])
    end.

-spec erase(term(), hashdict()) -> hashdict().
erase(Key, #hashdict{size=Size, root=Bucket} = Dict) when is_list(Bucket) ->
    {Bucket2, Incr} = bucket_erase(Bucket, Key),
    Dict#hashdict{size=(Size+Incr), root=Bucket2};
erase(Key, #hashdict{size=Size, root=Root} = Dict) ->
    Fun = fun(Bucket) -> bucket_erase(Bucket, Key) end,
    {Root2, Incr} = bucket_apply(Root, hash(Key), Fun),
    Dict#hashdict{size=(Size+Incr), root=Root2}.

-spec store(term(), term(), hashdict()) -> hashdict().
store(Key, Value, #hashdict{size=Size, root=Bucket} = Dict)
  when is_list(Bucket) ->
    case bucket_store(Bucket, Key, Value) of
        {Bucket2, Incr} when Incr > 0 andalso Size > ?ORDERED_THRESHOLD ->
            Dict#hashdict{size=(Size+Incr), root=bucket_expand(Bucket2, 0)};
        {Bucket2, Incr} ->
            Dict#hashdict{size=(Size+Incr), root=Bucket2}
    end;
store(Key, Value, #hashdict{size=Size, root=Root} = Dict) ->
    Fun = fun(Bucket) -> bucket_store(Bucket, Key, Value) end,
    {Root2, Incr} = bucket_apply(Root, hash(Key), Fun),
    Dict#hashdict{size=(Size+Incr), root=Root2}.

-spec append(term(), term(), hashdict()) -> hashdict().
append(Key, Value, Dict) ->
    append_list(Key, [Value], Dict).

-spec append_list(term(), list(), hashdict()) -> hashdict().
append_list(Key, List, Dict) ->
    update(Key, fun(Current) -> Current ++ List end, List, Dict).

-spec update(term(), fun((term())->term()), hashdict()) -> hashdict().
update(Key, Fun, #hashdict{root=Bucket} = Dict) when is_list(Bucket) ->
    case bucket_update_existing(Bucket, Key, Fun) of
         {Bucket2, _Incr, ok} ->
             Dict#hashdict{root=Bucket2};
         {_Bucket2, _Incr, error} ->
             error(badarg, [Key, Fun, Dict])
    end;
update(Key, Fun, #hashdict{root=Root} = Dict) ->
    Fun2 = fun(Bucket) -> bucket_update_existing(Bucket, Key, Fun) end,
    case bucket_apply_info(Root, hash(Key), Fun2) of
         {Root2, _Incr, ok} ->
             Dict#hashdict{root=Root2};
         {_Root2, _Incr, error} ->
             error(badarg, [Key, Fun, Dict])
    end.

-spec update(term(), fun((term())->term()), term(), hashdict()) -> hashdict().
update(Key, Fun, Initial, #hashdict{size=Size, root=Bucket} = Dict)
  when is_list(Bucket) ->
    case bucket_update(Bucket, Key, Fun, Initial) of
        {Bucket2, Incr} when Incr > 0 andalso Size > ?ORDERED_THRESHOLD ->
            Dict#hashdict{size=(Size+Incr), root=bucket_expand(Bucket2, 0)};
        {Bucket2, Incr} ->
            Dict#hashdict{size=(Size+Incr), root=Bucket2}
    end;
update(Key, Fun, Initial, #hashdict{size=Size, root=Root} = Dict) ->
    Fun2 = fun(Bucket) -> bucket_update(Bucket, Key, Fun, Initial) end,
    {Root2, Incr} = bucket_apply(Root, hash(Key), Fun2),
    Dict#hashdict{size=(Size+Incr), root=Root2}.

-spec update_counter(term(), number(), hashdict()) -> hashdict().
update_counter(Key, Incr, Dict) ->
    update(Key, fun(Current) -> Current + Incr end, Incr, Dict).

-spec fold(fun((term(), term(), term())-> term()), term(), hashdict()) ->
    term().
fold(Fun, Acc, #hashdict{root=Bucket}) when is_list(Bucket) ->
    bucket_fold(Bucket, Fun, Acc);
fold(Fun, Acc, #hashdict{root=Root}) ->
    node_fold(Fun, Acc, Root).

-spec map(fun((term(),term())->term()), hashdict()) -> hashdict().
map(Fun, #hashdict{root=Bucket} = Dict) when is_list(Bucket) ->
    Bucket2 = bucket_map(Bucket, Fun),
    Dict#hashdict{root=Bucket2};
map(Fun, #hashdict{root=Root} = Dict) ->
    Root2 = node_map(Root, Fun),
    Dict#hashdict{root=Root2}.

-spec filter(fun((term(), term()) -> boolean()), hashdict()) ->
    hashdict().
filter(Fun, #hashdict{size=Size, root=Bucket} = Dict) when is_list(Bucket) ->
    {Bucket2, Incr} = bucket_filter(Bucket, Fun),
    Dict#hashdict{size=(Size+Incr), root=Bucket2};
filter(Fun, #hashdict{size=Size, root=Root} = Dict) ->
    {Root2, Incr} = node_filter(Root, Fun),
    Dict#hashdict{size=(Size+Incr), root=Root2}.

-spec merge(fun((term(), term(), term())->term()), hashdict(), hashdict()) ->
    hashdict().
merge(Fun, #hashdict{size=SizeA} = DictA, #hashdict{size=SizeB} = DictB)
        when SizeA >= SizeB ->
    Fun2 = fun(Key, ValueB, Acc) ->
                  Fun3 = fun(ValueA) -> Fun(Key, ValueA, ValueB) end,
                  update(Key, Fun3, ValueB, Acc)
           end,
    fold(Fun2, DictA, DictB);
merge(Fun, DictA, DictB) ->
    Fun2 = fun(Key, ValueA, Acc) ->
                  Fun3 = fun(ValueB) -> Fun(Key, ValueA, ValueB) end,
                  update(Key, Fun3, ValueA, Acc)
           end,
    fold(Fun2, DictB, DictA).

%% @private Used for testing.
info(size, #hashdict{size=Size}) ->
    Size;
info(root, #hashdict{root=Root}) ->
    Root;
info(node_size, #hashdict{}) ->
    ?NODE_SIZE;
info(expand_load, #hashdict{}) ->
    ?EXPAND_LOAD+1;
info(contract_load, #hashdict{}) ->
    ?CONTRACT_LOAD-1;
info(ordered_threshold, #hashdict{}) ->
    ?ORDERED_THRESHOLD+1;
info(mode, #hashdict{root=Bucket}) when is_list(Bucket) ->
    ordered;
info(mode, #hashdict{}) ->
    trie.

%% internal.

hash(Key) ->
    erlang:phash2(Key).

index(Hash) ->
    (Hash band ?NODE_BITMAP) + 1.


index(Depth, Hash) ->
    ((Hash bsr (?NODE_SHIFT * Depth)) band ?NODE_BITMAP) + 1.

shift(Hash) ->
    Hash bsr ?NODE_SHIFT.

bucket_apply(Node, Hash, Fun) ->
    bucket_apply(Node, Hash, Fun, 0).

bucket_apply(Node, Hash, Fun, Depth) ->
    Pos = index(Hash),
    case element(Pos, Node) of
        Bucket when is_list(Bucket) ->
            case Fun(Bucket) of
                {Bucket2, Incr} when Incr > 0 andalso
                                     length(Bucket2) > ?EXPAND_LOAD ->
                    Elem = bucket_expand(Bucket2, Depth+1),
                    {setelement(Pos, Node, Elem), Incr};
                {[], Incr} when Incr < 0 ->
                    Node2 = setelement(Pos, Node, []),
                    {node_contract(Node2), Incr};
                {Bucket2, Incr} ->
                    {setelement(Pos, Node, Bucket2), Incr}
            end;
        Elem ->
            Depth2 = Depth + 1,
            {Elem2, Incr} = bucket_apply(Elem, shift(Hash), Fun, Depth2),
            {setelement(Pos, Node, Elem2), Incr}
    end.

bucket_apply_info(Node, Hash, Fun) ->
    bucket_apply_info(Node, Hash, Fun, 0).

bucket_apply_info(Node, Hash, Fun, Depth) ->
    Pos = index(Hash),
    case element(Pos, Node) of
        Bucket when is_list(Bucket) ->
            case Fun(Bucket) of
                {Bucket2, Incr, Info} when Incr > 0 andalso
                                           length(Bucket2) > ?EXPAND_LOAD ->
                    Elem = bucket_expand(Bucket2, Depth+1),
                    {setelement(Pos, Node, Elem), Incr, Info};
                {[], Incr, Info} when Incr < 0 ->
                    Node2 = setelement(Pos, Node, []),
                    {node_contract(Node2), Incr, Info};
                {Bucket2, Incr, Info} ->
                    {setelement(Pos, Node, Bucket2), Incr, Info}
            end;
        Elem ->
            Depth2 = Depth + 1,
            {Elem2, Incr, Info} = bucket_apply_info(Elem, shift(Hash), Fun,
                                                    Depth2),
            {setelement(Pos, Node, Elem2), Incr, Info}
    end.

bucket_find([?KV(Key, Value) | _Bucket], Key) ->
    {ok, Value};
bucket_find([_Elem | Bucket], Key) ->
    bucket_find(Bucket, Key);
bucket_find([], _Key) ->
    error.

bucket_get(Node, Hash) ->
    case element(index(Hash), Node) of
         Bucket when is_list(Bucket) ->
             Bucket;
         Elem ->
             bucket_get(Elem, shift(Hash))
    end.

bucket_take(Bucket, Key) ->
    bucket_take(Bucket, Key, []).

bucket_take([?KV(Key, Value) | Bucket], Key, Acc) ->
    {Bucket ++ Acc, -1, Value};
bucket_take([Elem | Bucket], Key, Acc) ->
    bucket_take(Bucket, Key, [Elem | Acc]);
bucket_take([], _Key, Acc) ->
    {Acc, 0, error}.

bucket_erase(Bucket, Key) ->
    bucket_erase(Bucket, Key, []).

bucket_erase([?KV(Key, _Value) | Bucket], Key, Acc) ->
    {Bucket ++ Acc, -1};
bucket_erase([Elem | Bucket], Key, Acc) ->
    bucket_erase(Bucket, Key, [Elem | Acc]);
bucket_erase([], _Key, Acc) ->
    {Acc, 0}.

bucket_store(Bucket, Key, Value) ->
    bucket_store(Bucket, Key, Value, []).

bucket_store([?KV(Key, _V) | Bucket], Key, Value, Acc) ->
    {Bucket ++ [?KV(Key, Value) | Acc], 0};
bucket_store([Elem | Bucket], Key, Value, Acc) ->
    bucket_store(Bucket, Key, Value, [Elem | Acc]);
bucket_store([], Key, Value, Acc) ->
    {[?KV(Key, Value) | Acc], 1}.

bucket_update_existing(Bucket, Key, Fun) ->
    bucket_update_existing(Bucket, Key, Fun, []).

bucket_update_existing([?KV(Key, Value) | Bucket], Key, Fun, Acc) ->
    {Bucket ++ [?KV(Key, Fun(Value)) | Acc], 0, ok};
bucket_update_existing([Elem | Bucket], Key, Fun, Acc) ->
    bucket_update_existing(Bucket, Key, Fun, [Elem | Acc]);
bucket_update_existing([], _Key, _Fun, _Acc) ->
    {[], 0, error}.

bucket_update(Bucket, Key, Fun, Initial) ->
    bucket_update(Bucket, Key, Fun, Initial, []).

bucket_update([?KV(Key, Value) | Bucket], Key, Fun, _Initial, Acc) ->
    {Bucket ++ [?KV(Key, Fun(Value)) | Acc], 0};
bucket_update([Elem | Bucket], Key, Fun, Initial, Acc) ->
    bucket_update(Bucket, Key, Fun, Initial, [Elem | Acc]);
bucket_update([], Key, _Fun, Initial, Acc) ->
    {[?KV(Key, Initial) | Acc], 1}.

bucket_fold([?KV(Key, Value) | Bucket], Fun, Acc) ->
    Acc2 = Fun(Key, Value, Acc),
    bucket_fold(Bucket, Fun, Acc2);
bucket_fold([], _Fun, Acc) ->
    Acc.

node_fold(Fun, Acc, Root) ->
    node_fold(Fun, Acc, Root, ?NODE_SIZE).

node_fold(Fun, Acc, Node, N) ->
    case element(N, Node) of
         Bucket when is_list(Bucket) andalso N > 1 ->
             Acc2 = bucket_fold(Bucket, Fun, Acc),
             node_fold(Fun, Acc2, Node, N - 1);
         Bucket when is_list(Bucket) ->
             bucket_fold(Bucket, Fun, Acc);
         Elem when N > 1 ->
            Acc2 = node_fold(Fun, Acc, Elem, ?NODE_SIZE),
            node_fold(Fun, Acc2, Node, N - 1);
         Elem ->
            node_fold(Fun, Acc, Elem, ?NODE_SIZE)
    end.

bucket_map(Bucket, Fun) ->
    [?KV(Key, Fun(Key, Value)) || ?KV(Key, Value) <- Bucket].

node_map(Bucket, Fun) when is_list(Bucket) ->
    bucket_map(Bucket, Fun);
node_map(Node, Fun) ->
    list_to_tuple([node_map(Elem, Fun) || Elem <- tuple_to_list(Node)]).

bucket_filter(Bucket, Fun) ->
    bucket_filter(Bucket, Fun, [], 0).

bucket_filter([?KV(Key, Value) | Bucket], Fun, Acc, Incr) ->
    case Fun(Key, Value) of
         true ->
             bucket_filter(Bucket, Fun, [?KV(Key, Value) | Acc], Incr);
         false ->
             bucket_filter(Bucket, Fun, Acc, Incr - 1)
    end;
bucket_filter([], _Fun, Acc, Incr) ->
    {lists:reverse(Acc), Incr}.

node_filter(Root, Fun) ->
    node_filter(Root, Fun, 0).

node_filter(Bucket, Fun, Incr) when is_list(Bucket) ->
    bucket_filter(Bucket, Fun, [], Incr);
node_filter(Node, Fun, Incr) ->
    node_filter(tuple_to_list(Node), Fun, Incr, []).

node_filter([Elem | Rest], Fun, Incr, Acc) ->
    {Elem2, Incr2} = node_filter(Elem, Fun, Incr),
    node_filter(Rest, Fun, Incr2, [Elem2 | Acc]);
node_filter([], _Fun, Incr, Acc) when Incr < 0 ->
    Node = list_to_tuple(lists:reverse(Acc)),
    {node_contract(Node), Incr};
node_filter([], _Fun, Incr, Acc) ->
    {list_to_tuple(lists:reverse(Acc)), Incr}.

bucket_expand(Bucket, Depth) ->
    bucket_expand(Bucket, Depth, ?NODE_TEMPLATE).

bucket_expand([?KV(Key, _Value) = Pair | Bucket], Depth, Node) ->
    Pos = index(Depth, hash(Key)),
    Node2 = setelement(Pos, Node, [Pair | element(Pos, Node)]),
    bucket_expand(Bucket, Depth, Node2);
bucket_expand([], _Depth, Node) ->
    Node.

node_contract({Bucket, [], [], [], [], [], [], []})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract({[], Bucket, [], [], [], [], [], []})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract({[], [], Bucket, [], [], [], [], []})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract({[], [], [], Bucket, [], [], [], []})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract({[], [], [], [], Bucket, [], [], []})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract({[], [], [], [], [], Bucket, [], []})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract({[], [], [], [], [], [], Bucket, []})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract({[], [], [], [], [], [], [], Bucket})
  when length(Bucket) < ?CONTRACT_LOAD  ->
    Bucket;
node_contract(Node) ->
    Node.
