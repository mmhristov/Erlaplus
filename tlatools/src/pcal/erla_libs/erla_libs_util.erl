% This module contains some commonly used functions that alleviate code duplication and improve
% the generated code's readability.
-module(erla_libs_util).

%% API
-export([get_nested_value/2, update_nested_value/3, is_test/0]).

% Function to retrieve a nested value from a map

% Base case
get_nested_value(Value, []) ->
  Value;

% Recursive case: access the next level of the map
%%-spec get_nested_value(#{K => #{K|A => V} | _}, [K|A]) -> V | error.
get_nested_value(Map, [Key | RestKeys]) when is_map(Map) ->
  case maps:find(Key, Map) of
    {ok, NextMap} ->
      get_nested_value(NextMap, RestKeys);
    error ->
      % Key is not found => throw error
      error(io_lib:format("Key ~p was not found", [Key]))
  end;

% Recursive case: access the next level of the list
get_nested_value(List, [Key | RestKeys]) when is_list(List) ->
  case lists:nth(Key, List) of
    error ->
      {error, not_found};
    NextList ->
      get_nested_value(NextList, RestKeys)
  end.

% Base case: when Keys list is empty, update the current value
update_nested_value(_, [], NewValue) ->
  NewValue;

% Recursive case: update the next level of the map
update_nested_value(Map, [Key | RestKeys], NewValue) when is_map(Map) ->
  case maps:find(Key, Map) of
     {ok, NextMap} ->
       maps:update(Key, update_nested_value(NextMap, RestKeys, NewValue), Map);
     error ->
       error("Key " ++ Key ++ "was not found")
  end;

% Base case for updating a nested element in a list
update_nested_value(List, [Key | RestKeys], NewValue) when is_list(List) ->
  {Before, After} = lists:split(Key - 1, List),
  case After of
    [] -> [NewValue];
    [Head | Tail] ->
      UpdatedElement = update_nested_value(Head, RestKeys, NewValue),
      Before ++ [UpdatedElement | Tail]
  end.

is_test() -> false. % temporary, change when test scheduling works.