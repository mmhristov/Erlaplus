-module(locksvc).
-export[process_Server/1, start_process_Server/1, process_Client/1, start_process_Client/1, init/0, run/0].
-include_lib("stdlib/include/assert.hrl").
-define(IS_TEST, false).

-record(state_Server, {
    procvar_ID = -1,
    var_msg = [],
    var_q = []
}).

-record(state_Client, {
    procvar_ID = -1,
    var_req = [],
    var_resp = "",
    var_hasLock = false
}).

-define(const_ClientSet, sets:from_list(lists:seq(1, ?const_NumClients))).
-define(const_NodeSet, sets:union(?const_ServerSet, ?const_ClientSet)).
-define(const_NumClients, 3).
-define(const_ServerID, 0).
-define(const_ServerSet, sets:from_list([?const_ServerID])).

function_while0(State0) ->
    case
    (true) of
        true ->
            receive
                Message1 ->
                    State1 = State0#state_Server{var_msg = Message1},
                    case ((maps:get(key_type, State1#state_Server.var_msg) =:= "lock")) of
                    true ->
                        case ((State1#state_Server.var_q =:= [])) of
                        true ->
                            erla_libs_comm:send(maps:get(key_sender, State1#state_Server.var_msg), "grant"),
                            ok;
                        false ->
                            ok
                        end,
                        State2 = State1#state_Server{var_q = State1#state_Server.var_q ++ [maps:get(key_sender, (State1#state_Server.var_msg))]},
                        ok;
                    false ->
                        case ((maps:get(key_type, State1#state_Server.var_msg) =:= "unlock")) of
                        true ->
                            State2 = State1#state_Server{var_q = tl(State1#state_Server.var_q)},
                            case ((State2#state_Server.var_q =/= [])) of
                            true ->
                                erla_libs_comm:send(hd(State2#state_Server.var_q), "grant"),
                                ok;
                            false ->
                                ok
                            end,
                            ok;
                        false ->
                            State2 = State1,
                            ok
                        end,
                        ok
                    end
            end,
            function_while0(State2);
        false ->
            State0
    end.
    
process_Server(State0) -> 
    % Register process globally
    erla_libs_comm:register_proc(State0#state_Server.procvar_ID),
    
    % Wait for 'go' message
    receive
        go -> ok
    end,
    
    % Body
    State1 = function_while0(State0).
    
start_process_Server(Id) ->
    spawn_link(?MODULE, process_Server, [#state_Server{procvar_ID = Id}]).

process_Client(State0) -> 
    % Register process globally
    erla_libs_comm:register_proc(State0#state_Client.procvar_ID),
    
    % Wait for 'go' message
    receive
        go -> ok
    end,
    
    % Body
    State1 = State0#state_Client{var_req = #{key_sender => State0#state_Client.procvar_ID, key_type => "lock"}},
    erla_libs_comm:send(?const_ServerID, State1#state_Client.var_req),
    receive
        Message1 ->
            State2 = State1#state_Client{var_resp = Message1},
            ?assert(((State2#state_Client.var_resp =:= "grant"))),
            State3 = State2#state_Client{var_hasLock = true},
            State4 = State3#state_Client{var_req = #{key_sender => State3#state_Client.procvar_ID, key_type => "unlock"}},
            erla_libs_comm:send(?const_ServerID, State4#state_Client.var_req),
            State5 = State4#state_Client{var_hasLock = false}
    end.
    
start_process_Client(Id) ->
    spawn_link(?MODULE, process_Client, [#state_Client{procvar_ID = Id}]).

init() -> 
    [start_process_Server(Id) || Id <- sets:to_list(?const_ServerSet)],
    [start_process_Client(Id) || Id <- sets:to_list(?const_ClientSet)].

run() -> 
    erla_libs_comm:broadcast('go').
