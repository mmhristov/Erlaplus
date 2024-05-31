-module(erla_RaftKVS).
-export[process_raftNode/1, start_process_raftNode/1, process_client/1, start_process_client/1, process_timeouter/1, start_process_timeouter/1, init/0, run/0].
-include_lib("stdlib/include/assert.hrl").
-define(IS_TEST, false).
-record(state_raftNode, {
    procvar_ID = -1,
    var_stateMachine = maps:from_list([{Key, 0} || Key <- sets:to_list(sets:from_list([]))]),
    var_stateMachineDomain = sets:from_list([]),
    var_role = "follower",
    var_log = [],
    var_currentTerm = 0,
    var_votedFor = 0,
    var_votesResponded = sets:from_list([]),
    var_votesGranted = sets:from_list([]),
    var_leader = 0,
    var_nextIndex = [],
    var_matchIndex = [],
    var_commitIndex = 0,
    var_msg = [],
    var_lastTermVar = 0,
    var_logOK = false,
    var_grant = false,
    var_isQuorum = false,
    var_temp_i = 0,
    var_isDone = false,
    var_prevLogTerm = 0,
    var_newCommitIndex = 0,
    var_maxAgreeIndex = 0,
    var_responseType = ""
}).

-record(state_client, {
    procvar_ID = -1,
    var_leaderId = 1,
    var_reqId = 1,
    var_req = [],
    var_reqs = [#{key_type => "Put", key_key => "a", key_value => "Value1"}, #{key_type => "Get", key_key => "a"}],
    var_resp = []
}).

-record(state_timeouter, {
    procvar_ID = -1,
    var_timeoutMsg = #{key_mtype => "timeout"}
}).

-define(const_ClientSet, sets:from_list([666])).
-define(const_NodeSet, (sets:union(?const_ClientSet, ?const_ServerSet))).
-define(const_NumRaftNodes, 3).
-define(const_ServerSet, sets:from_list((lists:seq(1, ?const_NumRaftNodes)))).
-define(const_TimeouterSet, sets:from_list((lists:seq((((1 * ?const_NumRaftNodes) + 1)), ((2 * ?const_NumRaftNodes)))))).

function_while1(State0) ->
    case
    ((State0#state_raftNode.var_temp_i =< sets:size(?const_ServerSet))) of
        true ->
            case ((State0#state_raftNode.var_temp_i =/= State0#state_raftNode.procvar_ID)) of
            true ->
                erla_libs_comm:send(State0#state_raftNode.var_temp_i, #{key_mtype => "RequestVoteRequest", key_mterm => State0#state_raftNode.var_currentTerm, key_mlastLogTerm => State0#state_raftNode.var_lastTermVar, key_mlastLogIndex => length(State0#state_raftNode.var_log), key_msource => State0#state_raftNode.procvar_ID}),
                ok;
            false ->
                ok
            end,
            State1 = State0#state_raftNode{var_temp_i = (State0#state_raftNode.var_temp_i + 1)},
            function_while1(State1);
        false ->
            State0
    end.

function_while2(State0) ->
    case
    ((State0#state_raftNode.var_temp_i =< maps:get(key_mcommitIndex, State0#state_raftNode.var_msg))) of
        true ->
            Temp_cmd0 = maps:get(key_cmd, erla_libs_util:get_nested_value(State0#state_raftNode.var_log, [State0#state_raftNode.var_temp_i])),
            case ((maps:get(key_type, Temp_cmd0) =:= "Put")) of
            true ->
                State1 = State0#state_raftNode{var_stateMachine = (maps:merge(State0#state_raftNode.var_stateMachine, maps:from_list([{Key, maps:get(key_value, Temp_cmd0)} || Key <- sets:to_list(sets:from_list([maps:get(key_key, Temp_cmd0)]))])))},
                State2 = State1#state_raftNode{var_stateMachineDomain = (sets:union(State1#state_raftNode.var_stateMachineDomain, sets:from_list([maps:get(key_key, Temp_cmd0)])))},
                State3 = State2#state_raftNode{var_commitIndex = State2#state_raftNode.var_temp_i},
                ok;
            false ->
                State3 = State0,
                ok
            end,
            State4 = State3#state_raftNode{var_temp_i = (State3#state_raftNode.var_temp_i + 1)},
            function_while2(State4);
        false ->
            State0
    end.

function_while3(State0) ->
    case
    ((((State0#state_raftNode.var_temp_i > 0)) andalso (not State0#state_raftNode.var_isDone))) of
        true ->
            State1 = State0#state_raftNode{var_isQuorum = ((sets:size(((sets:union(sets:from_list([State0#state_raftNode.procvar_ID]), sets:filter(fun(Temp_k0) -> (erla_libs_util:get_nested_value(State0#state_raftNode.var_matchIndex, [Temp_k0]) >= State0#state_raftNode.var_temp_i) end, ?const_ServerSet))))) * 2) > ?const_NumRaftNodes)},
            case (State1#state_raftNode.var_isQuorum) of
            true ->
                State2 = State1#state_raftNode{var_maxAgreeIndex = State1#state_raftNode.var_temp_i},
                State3 = State2#state_raftNode{var_isDone = true},
                ok;
            false ->
                State3 = State1,
                ok
            end,
            State4 = State3#state_raftNode{var_temp_i = (State3#state_raftNode.var_temp_i - 1)},
            function_while3(State4);
        false ->
            State0
    end.

function_while4(State0) ->
    case
    ((State0#state_raftNode.var_commitIndex < State0#state_raftNode.var_newCommitIndex)) of
        true ->
            % maybeFail
            State1 = State0#state_raftNode{var_commitIndex = (State0#state_raftNode.var_commitIndex + 1)},
            Temp_entry0 = erla_libs_util:get_nested_value(State1#state_raftNode.var_log, [State1#state_raftNode.var_commitIndex]),
            Temp_command0 = maps:get(key_cmd, Temp_entry0),
            case ((maps:get(key_type, Temp_command0) =:= "Get")) of
            true ->
                case ((sets:is_element(maps:get(key_key, Temp_command0), State1#state_raftNode.var_stateMachineDomain))) of
                true ->
                    State2 = State1#state_raftNode{var_temp_i = ["ClientGetResponse", erla_libs_util:get_nested_value(State1#state_raftNode.var_stateMachine, [maps:get(key_key, Temp_command0)])]},
                    ok;
                false ->
                    State2 = State1#state_raftNode{var_temp_i = ["ClientGetResponse", "null"]},
                    ok
                end,
                State4 = State2,
                ok;
            false ->
                case ((maps:get(key_type, Temp_command0) =:= "Put")) of
                true ->
                    State2 = State1#state_raftNode{var_stateMachine = (maps:merge(State1#state_raftNode.var_stateMachine, maps:from_list([{Key, maps:get(key_value, Temp_command0)} || Key <- sets:to_list(sets:from_list([maps:get(key_key, Temp_command0)]))])))},
                    State3 = State2#state_raftNode{var_stateMachineDomain = (sets:union(State2#state_raftNode.var_stateMachineDomain, sets:from_list([maps:get(key_key, Temp_command0)])))},
                    State4 = State3#state_raftNode{var_temp_i = ["ClientPutResponse", erla_libs_util:get_nested_value(State3#state_raftNode.var_stateMachine, [maps:get(key_key, Temp_command0)])]},
                    ok;
                false ->
                    erlang:display(["Unknown command", Temp_command0]),
                    ?assert(false),
                    State4 = State1,
                    ok
                end,
                ok
            end,
            Temp_reqOk0 = (sets:is_element(maps:get(key_key, Temp_command0), State4#state_raftNode.var_stateMachineDomain)),
            erla_libs_comm:send(maps:get(key_client, Temp_entry0), #{key_mtype => erla_libs_util:get_nested_value(State4#state_raftNode.var_temp_i, [1]), key_msuccess => true, key_mresponse => #{key_idx => maps:get(key_idx, Temp_command0), key_key => maps:get(key_key, Temp_command0), key_value => erla_libs_util:get_nested_value(State4#state_raftNode.var_temp_i, [2]), key_ok => Temp_reqOk0}, key_mleaderHint => State4#state_raftNode.procvar_ID, key_msource => State4#state_raftNode.procvar_ID, key_mdest => maps:get(key_client, Temp_entry0)}),
            function_while4(State4);
        false ->
            State0
    end.

function_while5(State0) ->
    case
    ((State0#state_raftNode.var_temp_i =< sets:size(?const_ServerSet))) of
        true ->
            case ((State0#state_raftNode.var_temp_i =/= State0#state_raftNode.procvar_ID)) of
            true ->
                Temp_prevLogIndex0 = (erla_libs_util:get_nested_value(State0#state_raftNode.var_nextIndex, [State0#state_raftNode.var_temp_i]) - 1),
                Temp_entries0 = lists:sublist(State0#state_raftNode.var_log, erla_libs_util:get_nested_value(State0#state_raftNode.var_nextIndex, [State0#state_raftNode.var_temp_i]), length(State0#state_raftNode.var_log)),
                case (Temp_prevLogIndex0 > 0) of
                true ->
                    State1 = State0#state_raftNode{var_prevLogTerm = maps:get(key_term, erla_libs_util:get_nested_value(State0#state_raftNode.var_log, [Temp_prevLogIndex0]))},
                    ok;
                false ->
                    State1 = State0#state_raftNode{var_prevLogTerm = 0},
                    ok
                end,
                erla_libs_comm:send(State1#state_raftNode.var_temp_i, #{key_mtype => "AppendEntriesRequest", key_mterm => State1#state_raftNode.var_currentTerm, key_mprevLogIndex => Temp_prevLogIndex0, key_mprevLogTerm => State1#state_raftNode.var_prevLogTerm, key_mentries => Temp_entries0, key_mcommitIndex => State1#state_raftNode.var_commitIndex, key_msource => State1#state_raftNode.procvar_ID}),
                ok;
            false ->
                State1 = State0,
                ok
            end,
            State2 = State1#state_raftNode{var_temp_i = (State1#state_raftNode.var_temp_i + 1)},
            function_while5(State2);
        false ->
            State0
    end.

function_while0(State0) ->
    case
    (true) of
        true ->
            % maybeFail
            receive
                Message1 ->
                    State1 = State0#state_raftNode{var_msg = Message1},
                    case ((maps:get(key_mtype, State1#state_raftNode.var_msg) =:= "timeout")) of
                    true ->
                        erlang:display("Election timeout received"),
                        case (not ((sets:is_element(State1#state_raftNode.var_role, sets:from_list(["follower", "candidate"]))))) of
                        true ->
                            % fail
                            ok;
                        false ->
                            ok
                        end,
                        State2 = State1#state_raftNode{var_role = "candidate"},
                        State3 = State2#state_raftNode{var_currentTerm = (State2#state_raftNode.var_currentTerm + 1)},
                        State4 = State3#state_raftNode{var_votedFor = State3#state_raftNode.procvar_ID},
                        State5 = State4#state_raftNode{var_votesResponded = sets:from_list([State4#state_raftNode.procvar_ID])},
                        State6 = State5#state_raftNode{var_votesGranted = sets:from_list([State5#state_raftNode.procvar_ID])},
                        case ((length(State6#state_raftNode.var_log) =:= 0)) of
                        true ->
                            State7 = State6#state_raftNode{var_lastTermVar = 0},
                            ok;
                        false ->
                            State7 = State6#state_raftNode{var_lastTermVar = maps:get(key_term, erla_libs_util:get_nested_value(State6#state_raftNode.var_log, [length(State6#state_raftNode.var_log)]))},
                            ok
                        end,
                        case ((sets:size(?const_ServerSet) =:= 1)) of
                        true ->
                            State10 = State7#state_raftNode{var_role = "leader"},
                            State11 = State10#state_raftNode{var_nextIndex = maps:from_list([{Key, (length(State10#state_raftNode.var_log) + 1)} || Key <- sets:to_list(?const_ServerSet)])},
                            State12 = State11#state_raftNode{var_matchIndex = maps:from_list([{Key, 0} || Key <- sets:to_list(?const_ServerSet)])},
                            State13 = State12#state_raftNode{var_leader = State12#state_raftNode.procvar_ID},
                            erlang:display(["BecomeLeader", integer_to_list(State13#state_raftNode.procvar_ID)]),
                            ok;
                        false ->
                            State10 = State7#state_raftNode{var_temp_i = 1},
                            State11 = function_while1(State10),
                            State13 = State11,
                            ok
                        end,
                        State15 = State13,
                        ok;
                    false ->
                        case ((maps:get(key_mtype, State1#state_raftNode.var_msg) =:= "RequestVoteRequest")) of
                        true ->
                            case ((maps:get(key_msource, State1#state_raftNode.var_msg) =:= State1#state_raftNode.procvar_ID)) of
                            true ->
                                % skip
                                State11 = State1,
                                ok;
                            false ->
                                case ((maps:get(key_mterm, State1#state_raftNode.var_msg) > State1#state_raftNode.var_currentTerm)) of
                                true ->
                                    State2 = State1#state_raftNode{var_currentTerm = maps:get(key_mterm, State1#state_raftNode.var_msg)},
                                    State3 = State2#state_raftNode{var_role = "follower"},
                                    State4 = State3#state_raftNode{var_votedFor = 0},
                                    State5 = State4#state_raftNode{var_leader = 0},
                                    ok;
                                false ->
                                    State5 = State1,
                                    ok
                                end,
                                case ((length(State5#state_raftNode.var_log) =:= 0)) of
                                true ->
                                    State6 = State5#state_raftNode{var_lastTermVar = 0},
                                    ok;
                                false ->
                                    State6 = State5#state_raftNode{var_lastTermVar = maps:get(key_term, erla_libs_util:get_nested_value(State5#state_raftNode.var_log, [length(State5#state_raftNode.var_log)]))},
                                    ok
                                end,
                                State7 = State6#state_raftNode{var_logOK = (((maps:get(key_mlastLogTerm, State6#state_raftNode.var_msg) > State6#state_raftNode.var_lastTermVar)) orelse (((maps:get(key_mlastLogTerm, State6#state_raftNode.var_msg) =:= State6#state_raftNode.var_lastTermVar) andalso (maps:get(key_mlastLogIndex, State6#state_raftNode.var_msg) >= length(State6#state_raftNode.var_log)))))},
                                State10 = State7#state_raftNode{var_grant = (((maps:get(key_mterm, State7#state_raftNode.var_msg) =:= State7#state_raftNode.var_currentTerm)) andalso (State7#state_raftNode.var_logOK andalso ((sets:is_element(State7#state_raftNode.var_votedFor, sets:from_list([0, maps:get(key_msource, State7#state_raftNode.var_msg)]))))))},
                                ?assert((maps:get(key_mterm, State10#state_raftNode.var_msg) =< State10#state_raftNode.var_currentTerm)),
                                case (State10#state_raftNode.var_grant) of
                                true ->
                                    State11 = State10#state_raftNode{var_votedFor = maps:get(key_msource, State10#state_raftNode.var_msg)},
                                    ok;
                                false ->
                                    State11 = State10,
                                    ok
                                end,
                                erla_libs_comm:send(maps:get(key_msource, State11#state_raftNode.var_msg), #{key_mtype => "RequestVoteResponse", key_mterm => State11#state_raftNode.var_currentTerm, key_mvoteGranted => State11#state_raftNode.var_grant, key_msource => State11#state_raftNode.procvar_ID}),
                                ok
                            end,
                            State15 = State11,
                            ok;
                        false ->
                            case ((maps:get(key_mtype, State1#state_raftNode.var_msg) =:= "RequestVoteResponse")) of
                            true ->
                                case ((maps:get(key_mterm, State1#state_raftNode.var_msg) > State1#state_raftNode.var_currentTerm)) of
                                true ->
                                    State2 = State1#state_raftNode{var_currentTerm = maps:get(key_mterm, State1#state_raftNode.var_msg)},
                                    State3 = State2#state_raftNode{var_role = "follower"},
                                    State4 = State3#state_raftNode{var_votedFor = 0},
                                    State5 = State4#state_raftNode{var_leader = 0},
                                    ok;
                                false ->
                                    State5 = State1,
                                    ok
                                end,
                                case ((maps:get(key_mterm, State5#state_raftNode.var_msg) < State5#state_raftNode.var_currentTerm)) of
                                true ->
                                    % skip
                                    State14 = State5,
                                    ok;
                                false ->
                                    ?assert((maps:get(key_mterm, State5#state_raftNode.var_msg) =:= State5#state_raftNode.var_currentTerm)),
                                    State6 = State5#state_raftNode{var_votesResponded = (sets:union(State5#state_raftNode.var_votesResponded, sets:from_list([State5#state_raftNode.procvar_ID])))},
                                    case (maps:get(key_mvoteGranted, State6#state_raftNode.var_msg)) of
                                    true ->
                                        State7 = State6#state_raftNode{var_votesGranted = (sets:union(State6#state_raftNode.var_votesGranted, sets:from_list([maps:get(key_msource, State6#state_raftNode.var_msg)])))},
                                        case ((State7#state_raftNode.var_role =:= "leader")) of
                                        true ->
                                            % skip
                                            State14 = State7,
                                            ok;
                                        false ->
                                            State10 = State7#state_raftNode{var_isQuorum = ((sets:size(State7#state_raftNode.var_votesGranted) * 2) > ?const_NumRaftNodes)},
                                            case (((State10#state_raftNode.var_role =:= "candidate") andalso State10#state_raftNode.var_isQuorum)) of
                                            true ->
                                                State11 = State10#state_raftNode{var_role = "leader"},
                                                State12 = State11#state_raftNode{var_nextIndex = maps:from_list([{Key, (length(State11#state_raftNode.var_log) + 1)} || Key <- sets:to_list(?const_ServerSet)])},
                                                State13 = State12#state_raftNode{var_matchIndex = maps:from_list([{Key, 0} || Key <- sets:to_list(?const_ServerSet)])},
                                                State14 = State13#state_raftNode{var_leader = State13#state_raftNode.procvar_ID},
                                                erlang:display(["BecomeLeader", integer_to_list(State14#state_raftNode.procvar_ID)]),
                                                ok;
                                            false ->
                                                State14 = State10,
                                                ok
                                            end,
                                            ok
                                        end,
                                        ok;
                                    false ->
                                        State14 = State6,
                                        ok
                                    end,
                                    ok
                                end,
                                State15 = State14,
                                ok;
                            false ->
                                case ((maps:get(key_mtype, State1#state_raftNode.var_msg) =:= "AppendEntriesRequest")) of
                                true ->
                                    case ((maps:get(key_mterm, State1#state_raftNode.var_msg) > State1#state_raftNode.var_currentTerm)) of
                                    true ->
                                        State2 = State1#state_raftNode{var_currentTerm = maps:get(key_mterm, State1#state_raftNode.var_msg)},
                                        State3 = State2#state_raftNode{var_role = "follower"},
                                        State4 = State3#state_raftNode{var_votedFor = 0},
                                        State5 = State4#state_raftNode{var_leader = 0},
                                        ok;
                                    false ->
                                        State5 = State1,
                                        ok
                                    end,
                                    State6 = State5#state_raftNode{var_logOK = ((maps:get(key_mprevLogIndex, State5#state_raftNode.var_msg) =:= 0) orelse (((maps:get(key_mprevLogIndex, State5#state_raftNode.var_msg) > 0) andalso ((maps:get(key_mprevLogIndex, State5#state_raftNode.var_msg) =< length(State5#state_raftNode.var_log)) andalso (maps:get(key_mprevLogTerm, State5#state_raftNode.var_msg) =:= maps:get(key_term, erla_libs_util:get_nested_value(State5#state_raftNode.var_log, [maps:get(key_mprevLogIndex, State5#state_raftNode.var_msg)])))))))},
                                    ?assert((maps:get(key_mterm, State6#state_raftNode.var_msg) =< State6#state_raftNode.var_currentTerm)),
                                    case ((maps:get(key_mterm, State6#state_raftNode.var_msg) =:= State6#state_raftNode.var_currentTerm)) of
                                    true ->
                                        State7 = State6#state_raftNode{var_leader = maps:get(key_msource, State6#state_raftNode.var_msg)},
                                        ok;
                                    false ->
                                        State7 = State6,
                                        ok
                                    end,
                                    case (((maps:get(key_mterm, State7#state_raftNode.var_msg) =:= State7#state_raftNode.var_currentTerm) andalso (State7#state_raftNode.var_role =:= "candidate"))) of
                                    true ->
                                        State10 = State7#state_raftNode{var_role = "follower"},
                                        ok;
                                    false ->
                                        State10 = State7,
                                        ok
                                    end,
                                    case ((((maps:get(key_mterm, State10#state_raftNode.var_msg) < State10#state_raftNode.var_currentTerm)) orelse (((maps:get(key_mterm, State10#state_raftNode.var_msg) =:= State10#state_raftNode.var_currentTerm) andalso ((State10#state_raftNode.var_role =:= "follower") andalso (not State10#state_raftNode.var_logOK)))))) of
                                    true ->
                                        erla_libs_comm:send(maps:get(key_msource, State10#state_raftNode.var_msg), #{key_mtype => "AppendEntriesResponse", key_mterm => State10#state_raftNode.var_currentTerm, key_msuccess => false, key_mmatchIndex => 0, key_msource => State10#state_raftNode.procvar_ID, key_mdest => maps:get(key_msource, State10#state_raftNode.var_msg)}),
                                        State14 = State10,
                                        ok;
                                    false ->
                                        ?assert(((maps:get(key_mterm, State10#state_raftNode.var_msg) =:= State10#state_raftNode.var_currentTerm) andalso ((State10#state_raftNode.var_role =:= "follower") andalso State10#state_raftNode.var_logOK))),
                                        State11 = State10#state_raftNode{var_log = (lists:sublist(State10#state_raftNode.var_log, 1, maps:get(key_mprevLogIndex, State10#state_raftNode.var_msg)) ++ maps:get(key_mentries, State10#state_raftNode.var_msg))},
                                        ?assert((maps:get(key_mcommitIndex, State11#state_raftNode.var_msg) =< length(State11#state_raftNode.var_log))),
                                        State12 = State11#state_raftNode{var_temp_i = (State11#state_raftNode.var_commitIndex + 1)},
                                        State13 = function_while2(State12),
                                        case ((State13#state_raftNode.var_commitIndex < maps:get(key_mcommitIndex, State13#state_raftNode.var_msg))) of
                                        true ->
                                            State14 = State13#state_raftNode{var_commitIndex = maps:get(key_mcommitIndex, State13#state_raftNode.var_msg)},
                                            ok;
                                        false ->
                                            State14 = State13,
                                            ok
                                        end,
                                        erla_libs_comm:send(maps:get(key_msource, State14#state_raftNode.var_msg), #{key_mtype => "AppendEntriesResponse", key_mterm => State14#state_raftNode.var_currentTerm, key_msuccess => true, key_mmatchIndex => (maps:get(key_mprevLogIndex, State14#state_raftNode.var_msg) + length(maps:get(key_mentries, State14#state_raftNode.var_msg))), key_msource => State14#state_raftNode.procvar_ID}),
                                        ok
                                    end,
                                    State15 = State14,
                                    ok;
                                false ->
                                    case ((maps:get(key_mtype, State1#state_raftNode.var_msg) =:= "AppendEntriesResponse")) of
                                    true ->
                                        case ((maps:get(key_mterm, State1#state_raftNode.var_msg) > State1#state_raftNode.var_currentTerm)) of
                                        true ->
                                            State2 = State1#state_raftNode{var_currentTerm = maps:get(key_mterm, State1#state_raftNode.var_msg)},
                                            State3 = State2#state_raftNode{var_role = "follower"},
                                            State4 = State3#state_raftNode{var_votedFor = 0},
                                            State5 = State4#state_raftNode{var_leader = 0},
                                            ok;
                                        false ->
                                            State5 = State1,
                                            ok
                                        end,
                                        erlang:display(["Handle AppendEntriesResponse", maps:get(key_msource, State5#state_raftNode.var_msg), maps:get(key_msuccess, State5#state_raftNode.var_msg), maps:get(key_mmatchIndex, State5#state_raftNode.var_msg), maps:get(key_mterm, State5#state_raftNode.var_msg)]),
                                        case ((maps:get(key_mterm, State5#state_raftNode.var_msg) < State5#state_raftNode.var_currentTerm)) of
                                        true ->
                                            % skip
                                            State15 = State5,
                                            ok;
                                        false ->
                                            ?assert((maps:get(key_mterm, State5#state_raftNode.var_msg) =:= State5#state_raftNode.var_currentTerm)),
                                            case (maps:get(key_msuccess, State5#state_raftNode.var_msg)) of
                                            true ->
                                                State6 = State5#state_raftNode{var_nextIndex = erla_libs_util:update_nested_value(State5#state_raftNode.var_nextIndex, [maps:get(key_msource, State5#state_raftNode.var_msg)], (maps:get(key_mmatchIndex, State5#state_raftNode.var_msg) + 1))},
                                                State7 = State6#state_raftNode{var_matchIndex = erla_libs_util:update_nested_value(State6#state_raftNode.var_matchIndex, [maps:get(key_msource, State6#state_raftNode.var_msg)], maps:get(key_mmatchIndex, State6#state_raftNode.var_msg))},
                                                ok;
                                            false ->
                                                case ((((erla_libs_util:get_nested_value(State5#state_raftNode.var_nextIndex, [maps:get(key_msource, State5#state_raftNode.var_msg)]) - 1)) < 1)) of
                                                true ->
                                                    State6 = State5#state_raftNode{var_nextIndex = erla_libs_util:update_nested_value(State5#state_raftNode.var_nextIndex, [maps:get(key_msource, State5#state_raftNode.var_msg)], (erla_libs_util:get_nested_value(State5#state_raftNode.var_nextIndex, [maps:get(key_msource, State5#state_raftNode.var_msg)]) - 1))},
                                                    ok;
                                                false ->
                                                    State6 = State5#state_raftNode{var_nextIndex = erla_libs_util:update_nested_value(State5#state_raftNode.var_nextIndex, [maps:get(key_msource, State5#state_raftNode.var_msg)], 1)},
                                                    ok
                                                end,
                                                State7 = State6,
                                                ok
                                            end,
                                            case ((State7#state_raftNode.var_role =:= "leader")) of
                                            true ->
                                                State10 = State7#state_raftNode{var_maxAgreeIndex = 0},
                                                State11 = State10#state_raftNode{var_temp_i = length(State10#state_raftNode.var_log)},
                                                State12 = State11#state_raftNode{var_isDone = false},
                                                State13 = function_while3(State12),
                                                case (((State13#state_raftNode.var_maxAgreeIndex =/= 0) andalso (maps:get(key_term, erla_libs_util:get_nested_value(State13#state_raftNode.var_log, [State13#state_raftNode.var_maxAgreeIndex])) =:= State13#state_raftNode.var_currentTerm))) of
                                                true ->
                                                    State14 = State13#state_raftNode{var_newCommitIndex = State13#state_raftNode.var_maxAgreeIndex},
                                                    ?assert((State14#state_raftNode.var_newCommitIndex >= State14#state_raftNode.var_commitIndex)),
                                                    ok;
                                                false ->
                                                    State14 = State13#state_raftNode{var_newCommitIndex = State13#state_raftNode.var_commitIndex},
                                                    ok
                                                end,
                                                State15 = function_while4(State14),
                                                ok;
                                            false ->
                                                State15 = State7,
                                                ok
                                            end,
                                            ok
                                        end,
                                        ok;
                                    false ->
                                        case ((sets:is_element(maps:get(key_mtype, State1#state_raftNode.var_msg), sets:from_list(["ClientGetRequest", "ClientPutRequest"])))) of
                                        true ->
                                            erlang:display(["HandleClientRequest", State1#state_raftNode.procvar_ID, maps:get(key_msource, State1#state_raftNode.var_msg), State1#state_raftNode.var_currentTerm, State1#state_raftNode.var_role]),
                                            case ((State1#state_raftNode.var_role =:= "leader")) of
                                            true ->
                                                case ((maps:get(key_mtype, State1#state_raftNode.var_msg) =:= "ClientGetRequest")) of
                                                true ->
                                                    Temp_command0 = erla_libs_util:get_nested_value(State1#state_raftNode.var_msg, [key_mcmd]),
                                                    Temp_isFound0 = ((sets:is_element(erla_libs_util:get_nested_value(Temp_command0, [key_key]), State1#state_raftNode.var_stateMachineDomain))),
                                                    case (Temp_isFound0) of
                                                    true ->
                                                        State2 = State1#state_raftNode{var_temp_i = erla_libs_util:get_nested_value(State1#state_raftNode.var_stateMachine, [maps:get(key_key, Temp_command0)])},
                                                        ok;
                                                    false ->
                                                        State2 = State1#state_raftNode{var_temp_i = "null"},
                                                        ok
                                                    end,
                                                    erla_libs_comm:send(maps:get(key_msource, State2#state_raftNode.var_msg), #{key_mtype => "ClientGetResponse", key_msuccess => true, key_mresponse => #{key_idx => maps:get(key_idx, Temp_command0), key_key => maps:get(key_key, Temp_command0), key_value => State2#state_raftNode.var_temp_i, key_ok => Temp_isFound0}, key_mleaderHint => State2#state_raftNode.procvar_ID, key_msource => State2#state_raftNode.procvar_ID, key_mdest => maps:get(key_msource, State2#state_raftNode.var_msg)}),
                                                    State4 = State2,
                                                    ok;
                                                false ->
                                                    Temp_entry0 = #{key_term => State1#state_raftNode.var_currentTerm, key_cmd => maps:get(key_mcmd, State1#state_raftNode.var_msg), key_client => maps:get(key_msource, State1#state_raftNode.var_msg)},
                                                    State2 = State1#state_raftNode{var_log = State1#state_raftNode.var_log ++ [Temp_entry0]},
                                                    % maybeFail
                                                    State3 = State2#state_raftNode{var_temp_i = 1},
                                                    State4 = function_while5(State3),
                                                    ok
                                                end,
                                                ok;
                                            false ->
                                                Temp_cmdData0 = maps:get(key_mcmd, State1#state_raftNode.var_msg),
                                                case ((maps:get(key_type, Temp_cmdData0) =:= "Get")) of
                                                true ->
                                                    State2 = State1#state_raftNode{var_responseType = "ClientGetResponse"},
                                                    ok;
                                                false ->
                                                    case ((maps:get(key_type, Temp_cmdData0) =:= "Put")) of
                                                    true ->
                                                        State2 = State1#state_raftNode{var_responseType = "ClientPutResponse"},
                                                        ok;
                                                    false ->
                                                        ?assert(false),
                                                        State2 = State1,
                                                        ok
                                                    end,
                                                    ok
                                                end,
                                                erla_libs_comm:send(maps:get(key_msource, State2#state_raftNode.var_msg), #{key_mtype => State2#state_raftNode.var_responseType, key_msuccess => false, key_mresponse => #{key_idx => erla_libs_util:get_nested_value(State2#state_raftNode.var_msg, [key_mcmd, key_idx]), key_key => erla_libs_util:get_nested_value(State2#state_raftNode.var_msg, [key_mcmd, key_key])}, key_msource => State2#state_raftNode.procvar_ID, key_mleaderHint => State2#state_raftNode.var_leader, key_mdest => maps:get(key_msource, State2#state_raftNode.var_msg)}),
                                                State4 = State2,
                                                ok
                                            end,
                                            ok;
                                        false ->
                                            State4 = State1,
                                            ok
                                        end,
                                        State15 = State4,
                                        ok
                                    end,
                                    ok
                                end,
                                ok
                            end,
                            ok
                        end,
                        ok
                    end
            end,
            function_while0(State15);
        false ->
            State0
    end.

function_while6(State0) ->
    case
    ((State0#state_client.var_reqId =< length(State0#state_client.var_reqs))) of
        true ->
            State1 = State0#state_client{var_req = erla_libs_util:get_nested_value(State0#state_client.var_reqs, [State0#state_client.var_reqId])},
            case ((maps:get(key_type, State1#state_client.var_req) =:= "Put")) of
            true ->
                erla_libs_comm:send(State1#state_client.var_leaderId, #{key_mtype => "ClientPutRequest", key_mcmd => #{key_idx => State1#state_client.var_reqId, key_type => "Put", key_key => maps:get(key_key, State1#state_client.var_req), key_value => maps:get(key_value, State1#state_client.var_req)}, key_msource => State1#state_client.procvar_ID}),
                ok;
            false ->
                erla_libs_comm:send(State1#state_client.var_leaderId, #{key_mtype => "ClientGetRequest", key_mcmd => #{key_idx => State1#state_client.var_reqId, key_type => "Get", key_key => maps:get(key_key, State1#state_client.var_req)}, key_msource => State1#state_client.procvar_ID}),
                ok
            end,
            receive
                Message1 ->
                    State2 = State1#state_client{var_resp = Message1},
                    ?assert((maps:get(key_mdest, State2#state_client.var_resp) =:= State2#state_client.procvar_ID)),
                    case ((maps:get(key_mleaderHint, State2#state_client.var_resp) =/= 0)) of
                    true ->
                        State3 = State2#state_client{var_leaderId = maps:get(key_mleaderHint, State2#state_client.var_resp)},
                        ok;
                    false ->
                        State3 = State2,
                        ok
                    end,
                    erlang:display(["Response", State3#state_client.var_resp]),
                    ?assert(((((not (maps:get(key_type, State3#state_client.var_req) =:= "Get")) or (maps:get(key_mtype, State3#state_client.var_resp) =:= "ClientGetResponse"))) andalso (((not (maps:get(key_type, State3#state_client.var_req) =:= "Put")) or (maps:get(key_mtype, State3#state_client.var_resp) =:= "ClientPutResponse"))))),
                    case (maps:get(key_msuccess, State3#state_client.var_resp)) of
                    true ->
                        Temp_data0 = maps:get(key_mresponse, State3#state_client.var_resp),
                        ?assert(((maps:get(key_idx, Temp_data0) =:= State3#state_client.var_reqId) andalso (maps:get(key_key, Temp_data0) =:= maps:get(key_key, State3#state_client.var_req)))),
                        case ((maps:get(key_type, State3#state_client.var_req) =:= "Get")) of
                        true ->
                            erlang:display(["Get response received", maps:get(key_key, Temp_data0), maps:get(key_value, Temp_data0)]),
                            ok;
                        false ->
                            erlang:display(["Put response received", maps:get(key_key, Temp_data0)]),
                            ok
                        end,
                        ok;
                    false ->
                        ok
                    end,
                    State4 = State3#state_client{var_reqId = (State3#state_client.var_reqId + 1)}
            end,
            function_while6(State4);
        false ->
            State0
    end.
    
process_raftNode(State0) -> 
    % Register process globally
    erla_libs_comm:register_proc(State0#state_raftNode.procvar_ID),
    
    % Wait for 'go' message
    receive
        go -> ok
    end,
    
    % Body
    State1 = function_while0(State0).
    
start_process_raftNode(Id) ->
    spawn_link(?MODULE, process_raftNode, [#state_raftNode{procvar_ID = Id}]).

process_client(State0) -> 
    % Register process globally
    erla_libs_comm:register_proc(State0#state_client.procvar_ID),
    
    % Wait for 'go' message
    receive
        go -> ok
    end,
    
    % Body
    State1 = function_while6(State0).
    
start_process_client(Id) ->
    spawn_link(?MODULE, process_client, [#state_client{procvar_ID = Id}]).

process_timeouter(State0) -> 
    % Register process globally
    erla_libs_comm:register_proc(State0#state_timeouter.procvar_ID),
    
    % Wait for 'go' message
    receive
        go -> ok
    end,
    
    % Body
    % maybeFail
    erla_libs_comm:send(((((((State0#state_timeouter.procvar_ID - 1)) rem sets:size(?const_ServerSet))) + 1)), State0#state_timeouter.var_timeoutMsg).
    
start_process_timeouter(Id) ->
    spawn_link(?MODULE, process_timeouter, [#state_timeouter{procvar_ID = Id}]).

init() -> 
    [start_process_raftNode(Id) || Id <- sets:to_list(?const_ServerSet)],
    [start_process_client(Id) || Id <- sets:to_list(?const_ClientSet)],
    [start_process_timeouter(Id) || Id <- sets:to_list(?const_TimeouterSet)].

run() -> 
    erla_libs_comm:broadcast('go').
