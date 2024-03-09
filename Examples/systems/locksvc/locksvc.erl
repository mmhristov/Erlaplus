-module(locksvc).
-export[process_Server/1, start_process_Server/1, process_Client/1, start_process_Client/1].
-record(state_Server, {
    procvar_Num = -1,
    var_msg = defaultInitValue,
    var_q = [],
    var_response_message = []
}).

-record(state_Client, {
    procvar_Num = -1,
    var_request = [],
    var_response = [],
    var_hasLock = false
}).
-include_lib("stdlib/include/assert.hrl").



function_while0( State0 ) ->
    if
    (true) -> 
        receive
            Message1 ->
                State1 = State0#state_Server{var_msg = (Message1)},
                case (maps:get(key_type, State1#state_Server.var_msg) =:= "lock") of
                true ->
                    case (State1#state_Server.var_q =:= []) of
                    true ->
                        State2 = State1#state_Server{var_response_message = ("grant")},
                        erlang:display("Granted lock to proc " ++ [integer_to_list(maps:get(key_from, State2#state_Server.var_msg))]),
                        erla_libs:send(maps:get(key_from, State2#state_Server.var_msg), State2#state_Server.var_response_message);
                    false ->
                        State2 = State1
                    end,
                    State3 = State2#state_Server{var_q = (State2#state_Server.var_q ++ [maps:get(key_from, (State2#state_Server.var_msg))])};
                false ->
                    case (maps:get(key_type, State1#state_Server.var_msg) =:= "unlock") of
                    true ->
                        State2 = State1#state_Server{var_q = (tl(State1#state_Server.var_q))},
                        erlang:display("Granted unlock to proc " ++ [integer_to_list(maps:get(key_from, State2#state_Server.var_msg))]),
                        case (State2#state_Server.var_q =/= []) of
                        true ->
                            State3 = State2#state_Server{var_response_message = ("grant")},
                            erla_libs:send(hd(State3#state_Server.var_q), State3#state_Server.var_response_message);
                        false ->
                            State3 = State2
                        end;
                    false ->
                        State3 = State1
                    end
                end
        end,
        function_while0( State3);
    true ->
        State0
    end.
    
process_Server(State0) -> 
    % Register process globally
    erla_libs:register_proc(State0#state_Server.procvar_Num),
    
    State1 = function_while0( State0).
    
start_process_Server(Name) ->
    spawn_link(?MODULE, process_Server, [#state_Server{procvar_Num = Name}]).

process_Client(State0) -> 
    % Register process globally
    erla_libs:register_proc(State0#state_Client.procvar_Num),
    
    State1 = State0#state_Client{var_request = (#{key_from => State0#state_Client.procvar_Num, key_type => "lock"})},
    erla_libs:send(0, State1#state_Client.var_request),
    receive
        Message1 ->
            State2 = State1#state_Client{var_response = (Message1)},
            ?assert((State2#state_Client.var_response =:= "grant")),
            State3 = State2#state_Client{var_hasLock = (true)},
            State4 = State3#state_Client{var_request = (#{key_from => State3#state_Client.procvar_Num, key_type => "unlock"})},
            erla_libs:send(0, State4#state_Client.var_request),
            State5 = State4#state_Client{var_hasLock = (false)}
    end.
    
start_process_Client(Name) ->
    spawn_link(?MODULE, process_Client, [#state_Client{procvar_Num = Name}]).

