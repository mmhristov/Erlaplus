% This module contains helper functions for inter-process communication,
% which includes functions for process-registration, sending/broadcasting of messages, and more.
-module(erla_libs_comm).

%% API
-export([send/2, register_proc/1, get_proc_name/1, broadcast/1, get_all_procs/0]).

register_proc(Name) ->
  GlobalName = get_proc_name(Name),
  case global:register_name(GlobalName, self()) of
    yes -> ok;
    no -> error("Error in registering global proc with name " ++ GlobalName)
  end.

get_proc_prefix() -> "proc_".

get_proc_name(Name) ->
  case is_atom(Name) of
    true -> Name;
    false ->
      case is_integer(Name) of
        true -> Str = get_proc_prefix() ++ integer_to_list(Name), list_to_atom(Str);
        false -> error("Proc name needs to be an integer")
      end
  end.

send(Name, Msg) ->
  global:send(get_proc_name(Name), Msg).

get_all_procs_internal() ->
  global:registered_names().

get_all_procs() ->
  List = get_all_procs_internal(),
  OnlyErlaProcAtoms = [string:to_integer(tl(string:tokens(atom_to_list(X), "_"))) || X <- List, string:str(atom_to_list(X), get_proc_prefix()) =:= 1],
  OnlyErlaProcs = [I || {I, _} <- OnlyErlaProcAtoms],
  sets:from_list(OnlyErlaProcs).

broadcast(Msg) ->
  AllProcs = get_all_procs_internal(),
  lists:foreach(fun(X) ->  erla_libs:send(X, Msg) end, AllProcs).