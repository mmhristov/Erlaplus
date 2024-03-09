-module(raft_Erla).
-export[process_leaderElection/1, start_process_leaderElection/1, process_client/1, start_process_client/1].
-record(state_leaderElection, {
    procvar_Num = -1,
    var_role = "follower",
    var_log = [],
    var_plog = [],
    var_currentTerm = 0,
    var_votedFor = 0,
    var_votesResponded = sets:from_list([]),
    var_votesGranted = sets:from_list([]),
    var_leader = 0,
    var_becomeLeaderCh = false,
    var_msg = [],
    var_lastTermVar = 0,
    var_logOK = false,
    var_grant = false,
    var_index = 0,
    var_isQuorum = false,
    var_allProcs = sets:from_list([]),
    var_allProcsSize = 0,
    var_leaderTimeout = 0,
    var_logPop = 0
}).
-include_lib("stdlib/include/assert.hrl").

-record(state_client, {
    procvar_Num = -1,
    var_timeoutMsg = #{key_mtype => "timeout"}
}).



function_while0(State0 ) ->
    if
    (true) -> 
        % maybeFail
        receive
            Message1 ->
                State1 = State0#state_leaderElection{var_msg = Message1},
                case ((maps:get(key_mtype, State1#state_leaderElection.var_msg) =:= "timeout")) of
                true ->
                    erlang:display("Election timeout received"),
                    case (not ((sets:is_element(State1#state_leaderElection.var_role, sets:from_list(["follower", "candidate"]))))) of
                    true ->
                        % fail
                        ok;
                    false ->
                        ok
                    end,
                    State2 = State1#state_leaderElection{var_role = "candidate"},
                    State3 = State2#state_leaderElection{var_currentTerm = (State2#state_leaderElection.var_currentTerm + 1)},
                    State4 = State3#state_leaderElection{var_votedFor = State3#state_leaderElection.procvar_Num},
                    State5 = State4#state_leaderElection{var_votesResponded = sets:from_list([State4#state_leaderElection.procvar_Num])},
                    State6 = State5#state_leaderElection{var_votesGranted = sets:from_list([State5#state_leaderElection.procvar_Num])},
                    case ((length(State6#state_leaderElection.var_log) =:= 0)) of
                    true ->
                        State7 = State6#state_leaderElection{var_lastTermVar = 0},
                        ok;
                    false ->
                        State7 = State6#state_leaderElection{var_lastTermVar = maps:get(key_term, lists:nth(length(State6#state_leaderElection.var_log), State6#state_leaderElection.var_log))},
                        ok
                    end,
                    State13 = State7,
                    erla_libs:broadcast(#{key_mtype => "RequestVoteRequest", key_mterm => State7#state_leaderElection.var_currentTerm, key_mlastLogTerm => State7#state_leaderElection.var_lastTermVar, key_mlastLogIndex => length(State7#state_leaderElection.var_log), key_msource => State7#state_leaderElection.procvar_Num}),
                    ok;
                false ->
                    case ((maps:get(key_mtype, State1#state_leaderElection.var_msg) =:= "RequestVoteRequest")) of
                    true ->
                        case ((maps:get(key_msource, State1#state_leaderElection.var_msg) =:= State1#state_leaderElection.procvar_Num)) of
                        true ->
                            % skip
                            State11 = State1,
                            % skip
                            ok;
                        false ->
                            case ((maps:get(key_mterm, State1#state_leaderElection.var_msg) > State1#state_leaderElection.var_currentTerm)) of
                            true ->
                                State2 = State1#state_leaderElection{var_currentTerm = maps:get(key_mterm, State1#state_leaderElection.var_msg)},
                                State3 = State2#state_leaderElection{var_role = "follower"},
                                State4 = State3#state_leaderElection{var_votedFor = 0},
                                State5 = State4#state_leaderElection{var_leader = 0},
                                ok;
                            false ->
                                State5 = State1,
                                ok
                            end,
                            case ((length(State5#state_leaderElection.var_log) =:= 0)) of
                            true ->
                                State6 = State5#state_leaderElection{var_lastTermVar = 0},
                                ok;
                            false ->
                                State6 = State5#state_leaderElection{var_lastTermVar = maps:get(key_term, lists:nth(length(State5#state_leaderElection.var_log), State5#state_leaderElection.var_log))},
                                ok
                            end,
                            State7 = State6#state_leaderElection{var_logOK = (((maps:get(key_mlastLogTerm, State6#state_leaderElection.var_msg) > State6#state_leaderElection.var_lastTermVar)) or (((maps:get(key_mlastLogTerm, State6#state_leaderElection.var_msg) =:= State6#state_leaderElection.var_lastTermVar) and (maps:get(key_mlastLogIndex, State6#state_leaderElection.var_msg) >= length(State6#state_leaderElection.var_log)))))},
                            State10 = State7#state_leaderElection{var_grant = (((maps:get(key_mterm, State7#state_leaderElection.var_msg) =:= State7#state_leaderElection.var_currentTerm)) and (State7#state_leaderElection.var_logOK and ((sets:is_element(State7#state_leaderElection.var_votedFor, sets:from_list([0, maps:get(key_msource, State7#state_leaderElection.var_msg)]))))))},
                            ?assert((maps:get(key_mterm, State10#state_leaderElection.var_msg) =< State10#state_leaderElection.var_currentTerm)),
                            case (State10#state_leaderElection.var_grant) of
                            true ->
                                State11 = State10#state_leaderElection{var_votedFor = maps:get(key_msource, State10#state_leaderElection.var_msg)},
                                ok;
                            false ->
                                State11 = State10,
                                ok
                            end,
                            erla_libs:send(maps:get(key_msource, State11#state_leaderElection.var_msg), #{key_mtype => "RequestVoteResponse", key_mterm => State11#state_leaderElection.var_currentTerm, key_mvoteGranted => State11#state_leaderElection.var_grant, key_msource => State11#state_leaderElection.procvar_Num}),
                            ok
                        end,
                        State13 = State11,
                        ok;
                    false ->
                        case ((maps:get(key_mtype, State1#state_leaderElection.var_msg) =:= "RequestVoteResponse")) of
                        true ->
                            case ((maps:get(key_mterm, State1#state_leaderElection.var_msg) > State1#state_leaderElection.var_currentTerm)) of
                            true ->
                                State2 = State1#state_leaderElection{var_currentTerm = maps:get(key_mterm, State1#state_leaderElection.var_msg)},
                                State3 = State2#state_leaderElection{var_role = "follower"},
                                State4 = State3#state_leaderElection{var_votedFor = 0},
                                State5 = State4#state_leaderElection{var_leader = 0},
                                ok;
                            false ->
                                State5 = State1,
                                ok
                            end,
                            case ((maps:get(key_mterm, State5#state_leaderElection.var_msg) < State5#state_leaderElection.var_currentTerm)) of
                            true ->
                                % skip
                                State13 = State5,
                                ok;
                            false ->
                                ?assert((maps:get(key_mterm, State5#state_leaderElection.var_msg) =:= State5#state_leaderElection.var_currentTerm)),
                                State6 = State5#state_leaderElection{var_votesResponded = (sets:union(State5#state_leaderElection.var_votesResponded, sets:from_list([State5#state_leaderElection.procvar_Num])))},
                                case (maps:get(key_mvoteGranted, State6#state_leaderElection.var_msg)) of
                                true ->
                                    State7 = State6#state_leaderElection{var_votesGranted = (sets:union(State6#state_leaderElection.var_votesGranted, sets:from_list([maps:get(key_msource, State6#state_leaderElection.var_msg)])))},
                                    case ((State7#state_leaderElection.var_becomeLeaderCh =:= true)) of
                                    true ->
                                        % skip
                                        State13 = State7,
                                        ok;
                                    false ->
                                        State10 = State7#state_leaderElection{var_allProcs = erla_libs:get_all_procs()},
                                        State11 = State10#state_leaderElection{var_allProcsSize = sets:size(State10#state_leaderElection.var_allProcs)},
                                        State12 = State11#state_leaderElection{var_isQuorum = ((sets:size(State11#state_leaderElection.var_votesGranted) * 2) > State11#state_leaderElection.var_allProcsSize)},
                                        case (((State12#state_leaderElection.var_role =:= "candidate") and State12#state_leaderElection.var_isQuorum)) of
                                        true ->
                                            State13 = State12#state_leaderElection{var_becomeLeaderCh = true},
                                            erlang:display("I AM LEADER"),
                                            ok;
                                        false ->
                                            State13 = State12,
                                            ok
                                        end,
                                        ok
                                    end,
                                    ok;
                                false ->
                                    State13 = State6,
                                    ok
                                end,
                                ok
                            end,
                            ok;
                        false ->
                            case ((maps:get(key_mtype, State1#state_leaderElection.var_msg) =:= "AppendEntriesRequest")) of
                            true ->
                                case ((maps:get(key_mterm, State1#state_leaderElection.var_msg) =:= State1#state_leaderElection.var_currentTerm)) of
                                true ->
                                    State2 = State1#state_leaderElection{var_leader = maps:get(key_msource, State1#state_leaderElection.var_msg)},
                                    State3 = State2#state_leaderElection{var_leaderTimeout = 0},
                                    ok;
                                false ->
                                    State3 = State1,
                                    ok
                                end,
                                case (((maps:get(key_mterm, State3#state_leaderElection.var_msg) =:= State3#state_leaderElection.var_currentTerm) and (State3#state_leaderElection.var_role =:= "candidate"))) of
                                true ->
                                    State4 = State3#state_leaderElection{var_role = "follower"},
                                    ok;
                                false ->
                                    State4 = State3,
                                    ok
                                end,
                                case ((((maps:get(key_mterm, State4#state_leaderElection.var_msg) < State4#state_leaderElection.var_currentTerm)) or (((maps:get(key_mterm, State4#state_leaderElection.var_msg) =:= State4#state_leaderElection.var_currentTerm) and ((State4#state_leaderElection.var_role =:= "follower") and (not State4#state_leaderElection.var_logOK)))))) of
                                true ->
                                    erla_libs:send(maps:get(key_msource, State4#state_leaderElection.var_msg), #{key_mtype => "AppendEntriesResponse", key_mterm => State4#state_leaderElection.var_currentTerm, key_msuccess => false, key_mmatchIndex => 0, key_msource => State4#state_leaderElection.procvar_Num}),
                                    State6 = State4,
                                    ok;
                                false ->
                                    ?assert(((maps:get(key_mterm, State4#state_leaderElection.var_msg) =:= State4#state_leaderElection.var_currentTerm) and ((State4#state_leaderElection.var_role =:= "follower") and State4#state_leaderElection.var_logOK))),
                                    State5 = State4#state_leaderElection{var_index = (maps:get(key_mprevLogIndex, State4#state_leaderElection.var_msg) + 1)},
                                    State6 = State5#state_leaderElection{var_plog = #{key_cmd => State5#state_leaderElection.var_logPop, key_cnt => (length(State5#state_leaderElection.var_log) - maps:get(key_mprevLogIndex, State5#state_leaderElection.var_msg))}},
                                    ok
                                end,
                                ok;
                            false ->
                                State6 = State1,
                                ok
                            end,
                            State13 = State6,
                            ok
                        end,
                        ok
                    end,
                    ok
                end
        end,
        function_while0(State13);
    true ->
        State0
    end.
    
process_leaderElection(State0) -> 
    % Register process globally
    erla_libs:register_proc(State0#state_leaderElection.procvar_Num),
    
    State1 = function_while0(State0).
    
start_process_leaderElection(Name) ->
    spawn_link(?MODULE, process_leaderElection, [#state_leaderElection{procvar_Num = Name}]).

process_client(State0) -> 
    % Register process globally
    erla_libs:register_proc(State0#state_client.procvar_Num),
    
    erla_libs:send(1, State0#state_client.var_timeoutMsg).
    
start_process_client(Name) ->
    spawn_link(?MODULE, process_client, [#state_client{procvar_Num = Name}]).

