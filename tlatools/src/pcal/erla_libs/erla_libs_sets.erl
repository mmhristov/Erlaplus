% This module contains helper functions for the erlang translation of operations on sets.
-module(erla_libs_sets).

%% API
-export([powerSet/1]).

powerSet(S) ->
  sets:from_list(generate(sets:to_list(S))).

generate([]) -> [[]];

generate([H | T]) -> PT = generate(T),
  [[H | X] || X <- PT] ++ PT.