---- MODULE Erla_RaftKVS ----

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumRaftNodes

RECURSIVE MinAcc(_, _) \* used only in invariants -> no translation

Min(s) ==
    LET e == CHOOSE e \in s : TRUE
    IN MinAcc(s \ { e }, e)

MinAcc(s, e1) ==
    IF s = {} THEN e1
    ELSE
        LET e2 == CHOOSE e2 \in s : TRUE
        IN MinAcc(s \ { e2 }, IF e2 < e1 THEN e2 ELSE e1)


(*--algorithm Erla_RaftKVS

    variables queues = [id \in NodeSet |-> <<>>];
    define
        ClientSet == {666}
        ServerSet == {1 .. NumRaftNodes}
        TimeouterSet == {(1 * NumRaftNodes + 1) .. (2 * NumRaftNodes)}
        NodeSet == ClientSet \union ServerSet
    end define;

    macro LastTerm(Result, Log)
    begin
        if (Len(Log) = 0) then
            Result := 0;
        else
            Result := Log[Len(Log)].term;
        end if;
    end macro;

    macro UpdateTerm(m, currentTerm, role, votedFor, leader)
    begin
        if (m.mterm > currentTerm) then
            currentTerm := m.mterm;
            role       := "follower";
            votedFor    := 0;
            leader      := 0;
        end if;
    end macro;

    macro CalculateIsQuorum(result, s)
    begin
        result := Cardinality(s) * 2 > NumRaftNodes;
    end macro;

    macro BecomeLeader(role, nextIndex, matchIndex, log, leader)
    begin
        role := "leader";
        nextIndex := [j \in ServerSet |-> Len(log) + 1];
        matchIndex := [j \in ServerSet |-> 0];
        leader := self;
        print <<"BecomeLeader", ToString(self)>>;
    end macro;

    macro AdvanceCommitIndex(commitIndex, newCommitIndex, log, stateMachine, temps)
    begin
        while (commitIndex < newCommitIndex) do
            maybeFail();
            commitIndex := commitIndex + 1;
            with entry = log[commitIndex], command = entry.cmd do
                if (command.type = "Get") then
                    if (command.key \in stateMachineDomain) then
                        temps := <<"ClientGetResponse", stateMachine[command.key]>>
                    else
                        temps := <<"ClientGetResponse", "null">>; \* todo: make null a constant/definition
                    end if;
                elsif (command.type = "Put") then
                    stateMachine := [key \in {command.key} |-> command.value] @@ stateMachine; \* workaround, todo: replace with :> operator when it's implemented in the translator
                    stateMachineDomain := stateMachineDomain \cup {command.key};
                    temps := <<"ClientPutResponse", stateMachine[command.key]>>; \* todo: make null a constant/definition
                else
                    print <<"Unknown command", command>>;
                    assert FALSE;
                end if;

                with reqOk = command.key \in stateMachineDomain do
                     send([
                        mtype       |-> temps[1],
                        msuccess    |-> TRUE,
                        mresponse   |-> [
                            idx   |-> command.idx,
                            key   |-> command.key,
                            value |-> temps[2],
                            ok    |-> reqOk
                        ],
                        mleaderHint  |-> self,
                        msource      |-> self,
                        mdest        |-> entry.client
                    ], entry.client);
                end with;
            end with;
        end while;
    end macro;

    fair process raftNode \in ServerSet
    variables
        \* State
        stateMachine = [k \in {} |-> 0]; \* initialize as record
        stateMachineDomain = {};
        role = "follower";
        log = <<>>;
        currentTerm = 0;
        votedFor = 0; votesResponded = {}; votesGranted = {};
        leader = 0;
        nextIndex = <<>>;
        matchIndex = <<>>;
        commitIndex = 0;

        \* Non-state vars
        msg = <<>>;
        lastTermVar = 0;
        logOK = FALSE;
        grant = FALSE;
        isQuorum = FALSE;
        temp_i = 0;
        isDone = FALSE;
        prevLogTerm = 0;
        newCommitIndex = 0;
        maxAgreeIndex = 0;
        responseType = "";
    begin
    leaderElectionLoop:
        while (TRUE) do
            maybeFail();

            receive(msg);
            if (msg.mtype = "timeout") then
                print "Election timeout received";

                if (~(role \in {"follower", "candidate"})) then
                    fail();
                end if;

                role := "candidate";
                currentTerm := currentTerm + 1;
                votedFor := self;
                votesResponded := {self};
                votesGranted := {self};

                LastTerm(lastTermVar, log);
            checkCardinalityTimeout:
                if (Cardinality(ServerSet) = 1) then
                becomeLeaderWhenAlone:
                    BecomeLeader(role, nextIndex, matchIndex, log, leader);
                else
                    temp_i := 1;
                broadcastRequestVoteRequest:
                    while (temp_i <= Cardinality(ServerSet)) do
                        if (temp_i # self) then \* do not send AppendEntriesRequest to self
                                send([
                                    mtype         |-> "RequestVoteRequest",
                                    mterm         |-> currentTerm,
                                    mlastLogTerm  |-> lastTermVar,
                                    mlastLogIndex |-> Len(log),
                                    msource       |-> self
                                ], temp_i);
                        end if;
                        temp_i := temp_i + 1;
                    end while;
                end if;
            elsif (msg.mtype = "RequestVoteRequest") then
                if (msg.msource = self) then
                    skip; \* do not handle broadcast message sent from self
                else
                    UpdateTerm(msg, currentTerm, role, votedFor, leader);
                    LastTerm(lastTermVar, log);
                    \* HandleRequestVote
                    logOK := (msg.mlastLogTerm > lastTermVar) \/ (msg.mlastLogTerm = lastTermVar /\ msg.mlastLogIndex >= Len(log));
                    grant := (msg.mterm = currentTerm) /\ logOK /\ (votedFor \in {0, msg.msource});

                    assert msg.mterm <= currentTerm;

                    if (grant) then
                    writeVotedFor:
                        votedFor := msg.msource;
                    end if;
                sendRequestVoteResponse:
                    send([
                        mtype        |-> "RequestVoteResponse",
                        mterm        |-> currentTerm,
                        mvoteGranted |-> grant,
                        msource      |-> self
                    ], msg.msource);
                end if;
            elsif (msg.mtype = "RequestVoteResponse") then
                UpdateTerm(msg, currentTerm, role, votedFor, leader);
                if (msg.mterm < currentTerm) then
                    \* drop stale response
                    skip;
                else
                    \* HandleRequestVoteResponse
                    assert msg.mterm = currentTerm;
                    votesResponded := votesResponded \cup {self};
                    if (msg.mvoteGranted) then
                        votesGranted := votesGranted \cup {msg.msource};

                        if (role = "leader") then
                            skip;
                        else
                        calculateQuorumHandleRequestVoteResponse:
                            CalculateIsQuorum(isQuorum, votesGranted);
                            if (role = "candidate" /\ isQuorum) then
                            becomeLeader:
                                BecomeLeader(role, nextIndex, matchIndex, log, leader);
                            end if;
                        end if;
                    end if;
                end if;
            elsif (msg.mtype = "AppendEntriesRequest") then
                UpdateTerm(msg, currentTerm, role, votedFor, leader);
                logOK := msg.mprevLogIndex = 0 \/ (msg.mprevLogIndex > 0 /\ msg.mprevLogIndex <= Len(log) /\ msg.mprevLogTerm = log[msg.mprevLogIndex].term);

                \* HandleAppendEntriesRequest
                assert msg.mterm <= currentTerm;
                if (msg.mterm = currentTerm) then
            setLeaderHandleAppendEntriesRequest:
                    leader := msg.msource;
                end if;
            returnToFollowerHandleAppendEntriesRequest:
                if (msg.mterm = currentTerm /\ role = "candidate") then
                    role := "follower"; \* return to follower role
                end if;

                if ((msg.mterm < currentTerm) \/ (msg.mterm = currentTerm /\ role = "follower" /\ (~ logOK))) then
                    \* reject request
                sendAppendEntriesResponseReject:
                    send([
                        mtype       |-> "AppendEntriesResponse",
                        mterm       |-> currentTerm,
                        msuccess    |-> FALSE,
                        mmatchIndex |-> 0,
                        msource     |-> self,
                        mdest       |-> msg.msource
                    ], msg.msource);
                else
                    \* accept request
                    assert msg.mterm = currentTerm /\ role = "follower" /\ logOK;
                    log  := SubSeq(log, 1, msg.mprevLogIndex) \o msg.mentries;
                    assert msg.mcommitIndex <= Len(log);

                \* ApplyLog
                    temp_i := commitIndex + 1;
                applyLogFollower:
                    while (temp_i <= msg.mcommitIndex) do
                        with cmd = log[temp_i].cmd do
                            if (cmd.type = "Put") then
                                stateMachine := [comm \in {cmd.key} |-> cmd.value] @@ stateMachine;
                                stateMachineDomain := stateMachineDomain \cup {cmd.key};
                                commitIndex := temp_i;
                            end if;
                            temp_i := temp_i + 1;
                        end with;
                    end while;

                    if (commitIndex < msg.mcommitIndex) then
                        commitIndex := msg.mcommitIndex;
                    end if;

\*                advanceCommitIndexFollower:
\*                    AdvanceCommitIndex(commitIndex, msg.mcommitIndex, log, stateMachine, temp_i); \* commit
                sendAppendEntriesResponse:
                    send([
                        mtype       |-> "AppendEntriesResponse",
                        mterm       |-> currentTerm,
                        msuccess    |-> TRUE,
                        mmatchIndex |-> msg.mprevLogIndex + Len(msg.mentries),
                        msource     |-> self
                    ], msg.msource)
                end if;
            elsif (msg.mtype = "AppendEntriesResponse") then
                UpdateTerm(msg, currentTerm, role, votedFor, leader);

                print <<"Handle AppendEntriesResponse", msg.msource, msg.msuccess, msg.mmatchIndex, msg.mterm>>;

                if (msg.mterm < currentTerm) then
                    \* drop stale response
                    skip;
                else
                    \* HandleAppendEntriesResponse
                    assert msg.mterm = currentTerm;

                    if (msg.msuccess) then
                        nextIndex[msg.msource] := msg.mmatchIndex + 1;
                        matchIndex[msg.msource] := msg.mmatchIndex;
                    else
                        if ((nextIndex[msg.msource] - 1) < 1) then \* todo: use Max function if implemented instead of if-statement
                            nextIndex[msg.msource] := nextIndex[msg.msource] - 1;
                        else
                            nextIndex[msg.msource] := 1;
                        end if;
                    end if;

                    if (role = "leader") then
                        \* FindMaxAgreeIndex
                        maxAgreeIndex := 0;
                        temp_i := Len(log);
                        isDone := FALSE;
                    findMaxAgreeIndex:
                        while ((temp_i > 0) /\ (~ isDone)) do
                        calculateQuorum:
                            CalculateIsQuorum(isQuorum, {self} \cup {k \in ServerSet : matchIndex[k] >= temp_i});
                            if (isQuorum) then
                                maxAgreeIndex := temp_i;
                                isDone := TRUE;
                            end if;
                            temp_i := temp_i - 1;
                        end while;

                        if (maxAgreeIndex # 0 /\ log[maxAgreeIndex].term = currentTerm) then
                            newCommitIndex := maxAgreeIndex;
                            assert newCommitIndex >= commitIndex;
                        else
                            newCommitIndex := commitIndex;
                        end if;

                    advanceCommitIndexLeader:
                        AdvanceCommitIndex(commitIndex, newCommitIndex, log, stateMachine, temp_i); \* commit
                    end if;
                end if;
            elsif (msg.mtype \in {"ClientGetRequest", "ClientPutRequest"}) then
                print <<"HandleClientRequest", self, msg.msource, currentTerm, role>>;

                if (role = "leader") then
                    if (msg.mtype = "ClientGetRequest") then
                    sendGetResponse:
                        with command = msg[mcmd], isFound = (command[key] \in stateMachineDomain) do
                            if (isFound) then
                                temp_i := stateMachine[command.key]
                            else
                                temp_i := "null"
                            end if;
                            send([
                                mtype       |-> "ClientGetResponse",
                                msuccess    |-> TRUE,
                                mresponse   |-> [
                                    idx   |-> command.idx,
                                    key   |-> command.key,
                                    value |-> temp_i,
                                    ok    |-> isFound
                                ],
                                mleaderHint  |-> self,
                                msource      |-> self,
                                mdest        |-> msg.msource
                            ], msg.msource);
                        end with;
                    else
                        with entry = [term |-> currentTerm, cmd  |-> msg.mcmd, client |-> msg.msource] do
                            log := Append(log, entry);
                        end with;

                        maybeFail();

                    iterateOverProcesses:
                        temp_i := 1;
                    assign_i:
                        while (temp_i <= Cardinality(ServerSet)) do
                         \* todo: maybe send AppendEntriesRequest to self in order to enable commiting of messages when there are no followers
                            if (temp_i # self) then \* do not send AppendEntriesRequest to self
                                with prevLogIndex = nextIndex[temp_i] - 1, entries = SubSeq(log, nextIndex[temp_i], Len(log)) do
                                    if prevLogIndex > 0 then
                                        prevLogTerm := log[prevLogIndex].term; \* use max function here when implemented
                                     else
                                        prevLogTerm := 0;
                                     end if;

                                    send([
                                        mtype         |-> "AppendEntriesRequest",
                                        mterm         |-> currentTerm,
                                        mprevLogIndex |-> prevLogIndex,
                                        mprevLogTerm  |-> prevLogTerm,
                                        mentries      |-> entries,
                                        mcommitIndex  |-> commitIndex,
                                        msource       |-> self
                                    ], temp_i);
                                end with;
                            end if;
                            temp_i := temp_i + 1;
                        end while;
                    end if;
                else
                setClientRequest:
                    with cmdData = msg.mcmd do
                        if (cmdData.type = "Get") then
                            responseType := "ClientGetResponse";
                        elsif (cmdData.type = "Put") then
                            responseType := "ClientPutResponse";
                        else
                            assert FALSE; \* fail
                        end if;
                    end with;
                followerReplyGetOrPutRequest:
                    send([
                        mtype       |-> responseType,
                        msuccess    |-> FALSE,
                        mresponse   |->  [idx |-> msg[mcmd][idx], key |-> msg[mcmd][key]],
                        msource     |-> self,
                        mleaderHint |-> leader,
                        mdest       |-> msg.msource
                    ], msg.msource);
                end if;
            end if;
        end while;
    end process;

    fair process client \in ClientSet
    variables
        leaderId = 1; \* assume leader is 1
        reqId = 1;
        req = <<>>;
        reqs = <<
               [type |-> "Put", key |-> "a", value |-> "Value1"],
               [type |-> "Get", key |-> "a"]
           >>;
        resp = <<>>;
    begin
    propose:
        while (reqId <= Len(reqs)) do
            req := reqs[reqId];
            if (req.type = "Put") then
                send([
                    mtype   |-> "ClientPutRequest",
                    mcmd    |-> [
                        idx   |-> reqId,
                        type  |-> "Put",
                        key   |-> req.key,
                        value |-> req.value
                    ],
                    msource |-> self
                ], leaderId);
            else
                send([
                    mtype   |-> "ClientGetRequest",
                    mcmd    |-> [
                        idx   |-> reqId,
                        type  |-> "Get",
                        key   |-> req.key
                    ],
                    msource |-> self
                ], leaderId);
            end if;
        receiveResponseClient:
            receive(resp);

            assert resp.mdest = self;
            if (resp.mleaderHint # 0) then
                leaderId := resp.mleaderHint;
            end if;

            print <<"Response", resp>>;
            assert (req.type = "Get" => resp.mtype = "ClientGetResponse") /\ (req.type = "Put" => resp.mtype = "ClientPutResponse");
            if (resp.msuccess) then
                with data = resp.mresponse do
\*                    print <<data.idx, reqId, data.key, req.key>>;
                    assert data.idx = reqId /\ data.key = req.key;

                    if (req.type = "Get") then
                        print <<"Get response received", data.key, data.value>>;
                    else
                        print <<"Put response received", data.key>>;
                    end if;
                end with;
            end if;

            reqId := reqId + 1;
        end while;
    end process;

    fair process timeouter \in TimeouterSet
    variables
        timeoutMsg = [mtype |-> "timeout"];
    begin
    sendTimeout:
         maybeFail(); \* ensure non-deterministic timeouts
    getRaftNodes4:
        send(timeoutMsg, (((self - 1) % Cardinality(ServerSet)) + 1));
    end process;

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b3ea4f32" /\ chksum(tla) = "bdc266bd")
VARIABLES queues, pc

(* define statement *)
ClientSet == {666}
ServerSet == {1 .. NumRaftNodes}
TimeouterSet == {(1 * NumRaftNodes + 1) .. (2 * NumRaftNodes)}
NodeSet == ClientSet \union ServerSet

VARIABLES stateMachine, stateMachineDomain, role, log, currentTerm, votedFor, 
          votesResponded, votesGranted, leader, nextIndex, matchIndex, 
          commitIndex, msg, lastTermVar, logOK, grant, isQuorum, temp_i, 
          isDone, prevLogTerm, newCommitIndex, maxAgreeIndex, responseType, 
          leaderId, reqId, req, reqs, resp, timeoutMsg

vars == << queues, pc, stateMachine, stateMachineDomain, role, log, 
           currentTerm, votedFor, votesResponded, votesGranted, leader, 
           nextIndex, matchIndex, commitIndex, msg, lastTermVar, logOK, grant, 
           isQuorum, temp_i, isDone, prevLogTerm, newCommitIndex, 
           maxAgreeIndex, responseType, leaderId, reqId, req, reqs, resp, 
           timeoutMsg >>

ProcSet == (ServerSet) \cup (ClientSet) \cup (TimeouterSet)

Init == (* Global variables *)
        /\ queues = [id \in NodeSet |-> <<>>]
        (* Process raftNode *)
        /\ stateMachine = [self \in ServerSet |-> [k \in {} |-> 0]]
        /\ stateMachineDomain = [self \in ServerSet |-> {}]
        /\ role = [self \in ServerSet |-> "follower"]
        /\ log = [self \in ServerSet |-> <<>>]
        /\ currentTerm = [self \in ServerSet |-> 0]
        /\ votedFor = [self \in ServerSet |-> 0]
        /\ votesResponded = [self \in ServerSet |-> {}]
        /\ votesGranted = [self \in ServerSet |-> {}]
        /\ leader = [self \in ServerSet |-> 0]
        /\ nextIndex = [self \in ServerSet |-> <<>>]
        /\ matchIndex = [self \in ServerSet |-> <<>>]
        /\ commitIndex = [self \in ServerSet |-> 0]
        /\ msg = [self \in ServerSet |-> <<>>]
        /\ lastTermVar = [self \in ServerSet |-> 0]
        /\ logOK = [self \in ServerSet |-> FALSE]
        /\ grant = [self \in ServerSet |-> FALSE]
        /\ isQuorum = [self \in ServerSet |-> FALSE]
        /\ temp_i = [self \in ServerSet |-> 0]
        /\ isDone = [self \in ServerSet |-> FALSE]
        /\ prevLogTerm = [self \in ServerSet |-> 0]
        /\ newCommitIndex = [self \in ServerSet |-> 0]
        /\ maxAgreeIndex = [self \in ServerSet |-> 0]
        /\ responseType = [self \in ServerSet |-> ""]
        (* Process client *)
        /\ leaderId = [self \in ClientSet |-> 1]
        /\ reqId = [self \in ClientSet |-> 1]
        /\ req = [self \in ClientSet |-> <<>>]
        /\ reqs = [self \in ClientSet |->     <<
                                              [type |-> "Put", key |-> "a", value |-> "Value1"],
                                              [type |-> "Get", key |-> "a"]
                                          >>]
        /\ resp = [self \in ClientSet |-> <<>>]
        (* Process timeouter *)
        /\ timeoutMsg = [self \in TimeouterSet |-> [mtype |-> "timeout"]]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "leaderElectionLoop"
                                        [] self \in ClientSet -> "propose"
                                        [] self \in TimeouterSet -> "sendTimeout"]

leaderElectionLoop(self) == /\ pc[self] = "leaderElectionLoop"
                            /\ \/ /\ FALSE
                               \/ /\ TRUE
                            /\ Len(queues[self]) > 0 
                            /\ msg' = [msg EXCEPT ![self] = Head(queues[self])]
                            /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                            /\ IF (msg'[self].mtype = "timeout")
                                  THEN /\ PrintT("Election timeout received")
                                       /\ IF (~(role[self] \in {"follower", "candidate"}))
                                             THEN /\ FALSE
                                             ELSE /\ TRUE
                                       /\ role' = [role EXCEPT ![self] = "candidate"]
                                       /\ currentTerm' = [currentTerm EXCEPT ![self] = currentTerm[self] + 1]
                                       /\ votedFor' = [votedFor EXCEPT ![self] = self]
                                       /\ votesResponded' = [votesResponded EXCEPT ![self] = {self}]
                                       /\ votesGranted' = [votesGranted EXCEPT ![self] = {self}]
                                       /\ IF (Len(log[self]) = 0)
                                             THEN /\ lastTermVar' = [lastTermVar EXCEPT ![self] = 0]
                                             ELSE /\ lastTermVar' = [lastTermVar EXCEPT ![self] = log[self][Len(log[self])].term]
                                       /\ pc' = [pc EXCEPT ![self] = "checkCardinalityTimeout"]
                                       /\ UNCHANGED << log, leader, nextIndex, 
                                                       matchIndex, logOK, 
                                                       grant, temp_i, isDone, 
                                                       maxAgreeIndex >>
                                  ELSE /\ IF (msg'[self].mtype = "RequestVoteRequest")
                                             THEN /\ IF (msg'[self].msource = self)
                                                        THEN /\ TRUE
                                                             /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                             /\ UNCHANGED << role, 
                                                                             currentTerm, 
                                                                             votedFor, 
                                                                             leader, 
                                                                             lastTermVar, 
                                                                             logOK, 
                                                                             grant >>
                                                        ELSE /\ IF (msg'[self].mterm > currentTerm[self])
                                                                   THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg'[self].mterm]
                                                                        /\ role' = [role EXCEPT ![self] = "follower"]
                                                                        /\ votedFor' = [votedFor EXCEPT ![self] = 0]
                                                                        /\ leader' = [leader EXCEPT ![self] = 0]
                                                                   ELSE /\ TRUE
                                                                        /\ UNCHANGED << role, 
                                                                                        currentTerm, 
                                                                                        votedFor, 
                                                                                        leader >>
                                                             /\ IF (Len(log[self]) = 0)
                                                                   THEN /\ lastTermVar' = [lastTermVar EXCEPT ![self] = 0]
                                                                   ELSE /\ lastTermVar' = [lastTermVar EXCEPT ![self] = log[self][Len(log[self])].term]
                                                             /\ logOK' = [logOK EXCEPT ![self] = (msg'[self].mlastLogTerm > lastTermVar'[self]) \/ (msg'[self].mlastLogTerm = lastTermVar'[self] /\ msg'[self].mlastLogIndex >= Len(log[self]))]
                                                             /\ grant' = [grant EXCEPT ![self] = (msg'[self].mterm = currentTerm'[self]) /\ logOK'[self] /\ (votedFor'[self] \in {0, msg'[self].msource})]
                                                             /\ Assert(msg'[self].mterm <= currentTerm'[self], 
                                                                       "Failure of assertion at line 179, column 21.")
                                                             /\ IF (grant'[self])
                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "writeVotedFor"]
                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "sendRequestVoteResponse"]
                                                  /\ UNCHANGED << log, 
                                                                  votesResponded, 
                                                                  votesGranted, 
                                                                  nextIndex, 
                                                                  matchIndex, 
                                                                  temp_i, 
                                                                  isDone, 
                                                                  maxAgreeIndex >>
                                             ELSE /\ IF (msg'[self].mtype = "RequestVoteResponse")
                                                        THEN /\ IF (msg'[self].mterm > currentTerm[self])
                                                                   THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg'[self].mterm]
                                                                        /\ role' = [role EXCEPT ![self] = "follower"]
                                                                        /\ votedFor' = [votedFor EXCEPT ![self] = 0]
                                                                        /\ leader' = [leader EXCEPT ![self] = 0]
                                                                   ELSE /\ TRUE
                                                                        /\ UNCHANGED << role, 
                                                                                        currentTerm, 
                                                                                        votedFor, 
                                                                                        leader >>
                                                             /\ IF (msg'[self].mterm < currentTerm'[self])
                                                                   THEN /\ TRUE
                                                                        /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                        /\ UNCHANGED << votesResponded, 
                                                                                        votesGranted >>
                                                                   ELSE /\ Assert(msg'[self].mterm = currentTerm'[self], 
                                                                                  "Failure of assertion at line 200, column 21.")
                                                                        /\ votesResponded' = [votesResponded EXCEPT ![self] = votesResponded[self] \cup {self}]
                                                                        /\ IF (msg'[self].mvoteGranted)
                                                                              THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = votesGranted[self] \cup {msg'[self].msource}]
                                                                                   /\ IF (role'[self] = "leader")
                                                                                         THEN /\ TRUE
                                                                                              /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "calculateQuorumHandleRequestVoteResponse"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                                   /\ UNCHANGED votesGranted
                                                             /\ UNCHANGED << log, 
                                                                             nextIndex, 
                                                                             matchIndex, 
                                                                             logOK, 
                                                                             temp_i, 
                                                                             isDone, 
                                                                             maxAgreeIndex >>
                                                        ELSE /\ IF (msg'[self].mtype = "AppendEntriesRequest")
                                                                   THEN /\ IF (msg'[self].mterm > currentTerm[self])
                                                                              THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg'[self].mterm]
                                                                                   /\ role' = [role EXCEPT ![self] = "follower"]
                                                                                   /\ votedFor' = [votedFor EXCEPT ![self] = 0]
                                                                                   /\ leader' = [leader EXCEPT ![self] = 0]
                                                                              ELSE /\ TRUE
                                                                                   /\ UNCHANGED << role, 
                                                                                                   currentTerm, 
                                                                                                   votedFor, 
                                                                                                   leader >>
                                                                        /\ logOK' = [logOK EXCEPT ![self] = msg'[self].mprevLogIndex = 0 \/ (msg'[self].mprevLogIndex > 0 /\ msg'[self].mprevLogIndex <= Len(log[self]) /\ msg'[self].mprevLogTerm = log[self][msg'[self].mprevLogIndex].term)]
                                                                        /\ Assert(msg'[self].mterm <= currentTerm'[self], 
                                                                                  "Failure of assertion at line 222, column 17.")
                                                                        /\ IF (msg'[self].mterm = currentTerm'[self])
                                                                              THEN /\ pc' = [pc EXCEPT ![self] = "setLeaderHandleAppendEntriesRequest"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "returnToFollowerHandleAppendEntriesRequest"]
                                                                        /\ UNCHANGED << log, 
                                                                                        nextIndex, 
                                                                                        matchIndex, 
                                                                                        temp_i, 
                                                                                        isDone, 
                                                                                        maxAgreeIndex >>
                                                                   ELSE /\ IF (msg'[self].mtype = "AppendEntriesResponse")
                                                                              THEN /\ IF (msg'[self].mterm > currentTerm[self])
                                                                                         THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg'[self].mterm]
                                                                                              /\ role' = [role EXCEPT ![self] = "follower"]
                                                                                              /\ votedFor' = [votedFor EXCEPT ![self] = 0]
                                                                                              /\ leader' = [leader EXCEPT ![self] = 0]
                                                                                         ELSE /\ TRUE
                                                                                              /\ UNCHANGED << role, 
                                                                                                              currentTerm, 
                                                                                                              votedFor, 
                                                                                                              leader >>
                                                                                   /\ PrintT(<<"Handle AppendEntriesResponse", msg'[self].msource, msg'[self].msuccess, msg'[self].mmatchIndex, msg'[self].mterm>>)
                                                                                   /\ IF (msg'[self].mterm < currentTerm'[self])
                                                                                         THEN /\ TRUE
                                                                                              /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                                              /\ UNCHANGED << nextIndex, 
                                                                                                              matchIndex, 
                                                                                                              temp_i, 
                                                                                                              isDone, 
                                                                                                              maxAgreeIndex >>
                                                                                         ELSE /\ Assert(msg'[self].mterm = currentTerm'[self], 
                                                                                                        "Failure of assertion at line 288, column 21.")
                                                                                              /\ IF (msg'[self].msuccess)
                                                                                                    THEN /\ nextIndex' = [nextIndex EXCEPT ![self][msg'[self].msource] = msg'[self].mmatchIndex + 1]
                                                                                                         /\ matchIndex' = [matchIndex EXCEPT ![self][msg'[self].msource] = msg'[self].mmatchIndex]
                                                                                                    ELSE /\ IF ((nextIndex[self][msg'[self].msource] - 1) < 1)
                                                                                                               THEN /\ nextIndex' = [nextIndex EXCEPT ![self][msg'[self].msource] = nextIndex[self][msg'[self].msource] - 1]
                                                                                                               ELSE /\ nextIndex' = [nextIndex EXCEPT ![self][msg'[self].msource] = 1]
                                                                                                         /\ UNCHANGED matchIndex
                                                                                              /\ IF (role'[self] = "leader")
                                                                                                    THEN /\ maxAgreeIndex' = [maxAgreeIndex EXCEPT ![self] = 0]
                                                                                                         /\ temp_i' = [temp_i EXCEPT ![self] = Len(log[self])]
                                                                                                         /\ isDone' = [isDone EXCEPT ![self] = FALSE]
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "findMaxAgreeIndex"]
                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                                                         /\ UNCHANGED << temp_i, 
                                                                                                                         isDone, 
                                                                                                                         maxAgreeIndex >>
                                                                                   /\ log' = log
                                                                              ELSE /\ IF (msg'[self].mtype \in {"ClientGetRequest", "ClientPutRequest"})
                                                                                         THEN /\ PrintT(<<"HandleClientRequest", self, msg'[self].msource, currentTerm[self], role[self]>>)
                                                                                              /\ IF (role[self] = "leader")
                                                                                                    THEN /\ IF (msg'[self].mtype = "ClientGetRequest")
                                                                                                               THEN /\ pc' = [pc EXCEPT ![self] = "sendGetResponse"]
                                                                                                                    /\ log' = log
                                                                                                               ELSE /\ LET entry == [term |-> currentTerm[self], cmd  |-> msg'[self].mcmd, client |-> msg'[self].msource] IN
                                                                                                                         log' = [log EXCEPT ![self] = Append(log[self], entry)]
                                                                                                                    /\ \/ /\ FALSE
                                                                                                                       \/ /\ TRUE
                                                                                                                    /\ pc' = [pc EXCEPT ![self] = "iterateOverProcesses"]
                                                                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "setClientRequest"]
                                                                                                         /\ log' = log
                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                                              /\ log' = log
                                                                                   /\ UNCHANGED << role, 
                                                                                                   currentTerm, 
                                                                                                   votedFor, 
                                                                                                   leader, 
                                                                                                   nextIndex, 
                                                                                                   matchIndex, 
                                                                                                   temp_i, 
                                                                                                   isDone, 
                                                                                                   maxAgreeIndex >>
                                                                        /\ logOK' = logOK
                                                             /\ UNCHANGED << votesResponded, 
                                                                             votesGranted >>
                                                  /\ UNCHANGED << lastTermVar, 
                                                                  grant >>
                            /\ UNCHANGED << stateMachine, stateMachineDomain, 
                                            commitIndex, isQuorum, prevLogTerm, 
                                            newCommitIndex, responseType, 
                                            leaderId, reqId, req, reqs, resp, 
                                            timeoutMsg >>

checkCardinalityTimeout(self) == /\ pc[self] = "checkCardinalityTimeout"
                                 /\ IF (Cardinality(ServerSet) = 1)
                                       THEN /\ pc' = [pc EXCEPT ![self] = "becomeLeaderWhenAlone"]
                                            /\ UNCHANGED temp_i
                                       ELSE /\ temp_i' = [temp_i EXCEPT ![self] = 1]
                                            /\ pc' = [pc EXCEPT ![self] = "broadcastRequestVoteRequest"]
                                 /\ UNCHANGED << queues, stateMachine, 
                                                 stateMachineDomain, role, log, 
                                                 currentTerm, votedFor, 
                                                 votesResponded, votesGranted, 
                                                 leader, nextIndex, matchIndex, 
                                                 commitIndex, msg, lastTermVar, 
                                                 logOK, grant, isQuorum, 
                                                 isDone, prevLogTerm, 
                                                 newCommitIndex, maxAgreeIndex, 
                                                 responseType, leaderId, reqId, 
                                                 req, reqs, resp, timeoutMsg >>

becomeLeaderWhenAlone(self) == /\ pc[self] = "becomeLeaderWhenAlone"
                               /\ role' = [role EXCEPT ![self] = "leader"]
                               /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> Len(log[self]) + 1]]
                               /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                               /\ leader' = [leader EXCEPT ![self] = self]
                               /\ PrintT(<<"BecomeLeader", ToString(self)>>)
                               /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                               /\ UNCHANGED << queues, stateMachine, 
                                               stateMachineDomain, log, 
                                               currentTerm, votedFor, 
                                               votesResponded, votesGranted, 
                                               commitIndex, msg, lastTermVar, 
                                               logOK, grant, isQuorum, temp_i, 
                                               isDone, prevLogTerm, 
                                               newCommitIndex, maxAgreeIndex, 
                                               responseType, leaderId, reqId, 
                                               req, reqs, resp, timeoutMsg >>

broadcastRequestVoteRequest(self) == /\ pc[self] = "broadcastRequestVoteRequest"
                                     /\ IF (temp_i[self] <= Cardinality(ServerSet))
                                           THEN /\ IF (temp_i[self] # self)
                                                      THEN /\ \/ /\ queues' = [queues EXCEPT ![temp_i[self]] =  Append(queues[temp_i[self]],    [mtype         |-> "RequestVoteRequest",mterm         |-> currentTerm[self],mlastLogTerm  |-> lastTermVar[self],mlastLogIndex |-> Len(log[self]),msource       |-> self])]
                                                              \/ /\ TRUE
                                                                 /\ UNCHANGED queues
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED queues
                                                /\ temp_i' = [temp_i EXCEPT ![self] = temp_i[self] + 1]
                                                /\ pc' = [pc EXCEPT ![self] = "broadcastRequestVoteRequest"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                /\ UNCHANGED << queues, temp_i >>
                                     /\ UNCHANGED << stateMachine, 
                                                     stateMachineDomain, role, 
                                                     log, currentTerm, 
                                                     votedFor, votesResponded, 
                                                     votesGranted, leader, 
                                                     nextIndex, matchIndex, 
                                                     commitIndex, msg, 
                                                     lastTermVar, logOK, grant, 
                                                     isQuorum, isDone, 
                                                     prevLogTerm, 
                                                     newCommitIndex, 
                                                     maxAgreeIndex, 
                                                     responseType, leaderId, 
                                                     reqId, req, reqs, resp, 
                                                     timeoutMsg >>

sendRequestVoteResponse(self) == /\ pc[self] = "sendRequestVoteResponse"
                                 /\ \/ /\ queues' = [queues EXCEPT ![msg[self].msource] =  Append(queues[msg[self].msource],    [mtype        |-> "RequestVoteResponse",mterm        |-> currentTerm[self],mvoteGranted |-> grant[self],msource      |-> self])]
                                    \/ /\ TRUE
                                       /\ UNCHANGED queues
                                 /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                 /\ UNCHANGED << stateMachine, 
                                                 stateMachineDomain, role, log, 
                                                 currentTerm, votedFor, 
                                                 votesResponded, votesGranted, 
                                                 leader, nextIndex, matchIndex, 
                                                 commitIndex, msg, lastTermVar, 
                                                 logOK, grant, isQuorum, 
                                                 temp_i, isDone, prevLogTerm, 
                                                 newCommitIndex, maxAgreeIndex, 
                                                 responseType, leaderId, reqId, 
                                                 req, reqs, resp, timeoutMsg >>

writeVotedFor(self) == /\ pc[self] = "writeVotedFor"
                       /\ votedFor' = [votedFor EXCEPT ![self] = msg[self].msource]
                       /\ pc' = [pc EXCEPT ![self] = "sendRequestVoteResponse"]
                       /\ UNCHANGED << queues, stateMachine, 
                                       stateMachineDomain, role, log, 
                                       currentTerm, votesResponded, 
                                       votesGranted, leader, nextIndex, 
                                       matchIndex, commitIndex, msg, 
                                       lastTermVar, logOK, grant, isQuorum, 
                                       temp_i, isDone, prevLogTerm, 
                                       newCommitIndex, maxAgreeIndex, 
                                       responseType, leaderId, reqId, req, 
                                       reqs, resp, timeoutMsg >>

calculateQuorumHandleRequestVoteResponse(self) == /\ pc[self] = "calculateQuorumHandleRequestVoteResponse"
                                                  /\ isQuorum' = [isQuorum EXCEPT ![self] = Cardinality(votesGranted[self]) * 2 > NumRaftNodes]
                                                  /\ IF (role[self] = "candidate" /\ isQuorum'[self])
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "becomeLeader"]
                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                  /\ UNCHANGED << queues, 
                                                                  stateMachine, 
                                                                  stateMachineDomain, 
                                                                  role, log, 
                                                                  currentTerm, 
                                                                  votedFor, 
                                                                  votesResponded, 
                                                                  votesGranted, 
                                                                  leader, 
                                                                  nextIndex, 
                                                                  matchIndex, 
                                                                  commitIndex, 
                                                                  msg, 
                                                                  lastTermVar, 
                                                                  logOK, grant, 
                                                                  temp_i, 
                                                                  isDone, 
                                                                  prevLogTerm, 
                                                                  newCommitIndex, 
                                                                  maxAgreeIndex, 
                                                                  responseType, 
                                                                  leaderId, 
                                                                  reqId, req, 
                                                                  reqs, resp, 
                                                                  timeoutMsg >>

becomeLeader(self) == /\ pc[self] = "becomeLeader"
                      /\ role' = [role EXCEPT ![self] = "leader"]
                      /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> Len(log[self]) + 1]]
                      /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                      /\ leader' = [leader EXCEPT ![self] = self]
                      /\ PrintT(<<"BecomeLeader", ToString(self)>>)
                      /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                      /\ UNCHANGED << queues, stateMachine, stateMachineDomain, 
                                      log, currentTerm, votedFor, 
                                      votesResponded, votesGranted, 
                                      commitIndex, msg, lastTermVar, logOK, 
                                      grant, isQuorum, temp_i, isDone, 
                                      prevLogTerm, newCommitIndex, 
                                      maxAgreeIndex, responseType, leaderId, 
                                      reqId, req, reqs, resp, timeoutMsg >>

returnToFollowerHandleAppendEntriesRequest(self) == /\ pc[self] = "returnToFollowerHandleAppendEntriesRequest"
                                                    /\ IF (msg[self].mterm = currentTerm[self] /\ role[self] = "candidate")
                                                          THEN /\ role' = [role EXCEPT ![self] = "follower"]
                                                          ELSE /\ TRUE
                                                               /\ role' = role
                                                    /\ IF ((msg[self].mterm < currentTerm[self]) \/ (msg[self].mterm = currentTerm[self] /\ role'[self] = "follower" /\ (~ logOK[self])))
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "sendAppendEntriesResponseReject"]
                                                               /\ UNCHANGED << log, 
                                                                               temp_i >>
                                                          ELSE /\ Assert(msg[self].mterm = currentTerm[self] /\ role'[self] = "follower" /\ logOK[self], 
                                                                         "Failure of assertion at line 245, column 21.")
                                                               /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, msg[self].mprevLogIndex) \o msg[self].mentries]
                                                               /\ Assert(msg[self].mcommitIndex <= Len(log'[self]), 
                                                                         "Failure of assertion at line 247, column 21.")
                                                               /\ temp_i' = [temp_i EXCEPT ![self] = commitIndex[self] + 1]
                                                               /\ pc' = [pc EXCEPT ![self] = "applyLogFollower"]
                                                    /\ UNCHANGED << queues, 
                                                                    stateMachine, 
                                                                    stateMachineDomain, 
                                                                    currentTerm, 
                                                                    votedFor, 
                                                                    votesResponded, 
                                                                    votesGranted, 
                                                                    leader, 
                                                                    nextIndex, 
                                                                    matchIndex, 
                                                                    commitIndex, 
                                                                    msg, 
                                                                    lastTermVar, 
                                                                    logOK, 
                                                                    grant, 
                                                                    isQuorum, 
                                                                    isDone, 
                                                                    prevLogTerm, 
                                                                    newCommitIndex, 
                                                                    maxAgreeIndex, 
                                                                    responseType, 
                                                                    leaderId, 
                                                                    reqId, req, 
                                                                    reqs, resp, 
                                                                    timeoutMsg >>

sendAppendEntriesResponseReject(self) == /\ pc[self] = "sendAppendEntriesResponseReject"
                                         /\ \/ /\ queues' = [queues EXCEPT ![msg[self].msource] =  Append(queues[msg[self].msource],    [mtype       |-> "AppendEntriesResponse",mterm       |-> currentTerm[self],msuccess    |-> FALSE,mmatchIndex |-> 0,msource     |-> self,mdest       |-> msg[self].msource])]
                                            \/ /\ TRUE
                                               /\ UNCHANGED queues
                                         /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                         /\ UNCHANGED << stateMachine, 
                                                         stateMachineDomain, 
                                                         role, log, 
                                                         currentTerm, votedFor, 
                                                         votesResponded, 
                                                         votesGranted, leader, 
                                                         nextIndex, matchIndex, 
                                                         commitIndex, msg, 
                                                         lastTermVar, logOK, 
                                                         grant, isQuorum, 
                                                         temp_i, isDone, 
                                                         prevLogTerm, 
                                                         newCommitIndex, 
                                                         maxAgreeIndex, 
                                                         responseType, 
                                                         leaderId, reqId, req, 
                                                         reqs, resp, 
                                                         timeoutMsg >>

applyLogFollower(self) == /\ pc[self] = "applyLogFollower"
                          /\ IF (temp_i[self] <= msg[self].mcommitIndex)
                                THEN /\ LET cmd == log[self][temp_i[self]].cmd IN
                                          /\ IF (cmd.type = "Put")
                                                THEN /\ stateMachine' = [stateMachine EXCEPT ![self] = [comm \in {cmd.key} |-> cmd.value] @@ stateMachine[self]]
                                                     /\ stateMachineDomain' = [stateMachineDomain EXCEPT ![self] = stateMachineDomain[self] \cup {cmd.key}]
                                                     /\ commitIndex' = [commitIndex EXCEPT ![self] = temp_i[self]]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << stateMachine, 
                                                                     stateMachineDomain, 
                                                                     commitIndex >>
                                          /\ temp_i' = [temp_i EXCEPT ![self] = temp_i[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "applyLogFollower"]
                                ELSE /\ IF (commitIndex[self] < msg[self].mcommitIndex)
                                           THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = msg[self].mcommitIndex]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED commitIndex
                                     /\ pc' = [pc EXCEPT ![self] = "sendAppendEntriesResponse"]
                                     /\ UNCHANGED << stateMachine, 
                                                     stateMachineDomain, 
                                                     temp_i >>
                          /\ UNCHANGED << queues, role, log, currentTerm, 
                                          votedFor, votesResponded, 
                                          votesGranted, leader, nextIndex, 
                                          matchIndex, msg, lastTermVar, logOK, 
                                          grant, isQuorum, isDone, prevLogTerm, 
                                          newCommitIndex, maxAgreeIndex, 
                                          responseType, leaderId, reqId, req, 
                                          reqs, resp, timeoutMsg >>

sendAppendEntriesResponse(self) == /\ pc[self] = "sendAppendEntriesResponse"
                                   /\ \/ /\ queues' = [queues EXCEPT ![msg[self].msource] =  Append(queues[msg[self].msource],    [mtype       |-> "AppendEntriesResponse",mterm       |-> currentTerm[self],msuccess    |-> TRUE,mmatchIndex |-> msg[self].mprevLogIndex + Len(msg[self].mentries),msource     |-> self])]
                                      \/ /\ TRUE
                                         /\ UNCHANGED queues
                                   /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                   /\ UNCHANGED << stateMachine, 
                                                   stateMachineDomain, role, 
                                                   log, currentTerm, votedFor, 
                                                   votesResponded, 
                                                   votesGranted, leader, 
                                                   nextIndex, matchIndex, 
                                                   commitIndex, msg, 
                                                   lastTermVar, logOK, grant, 
                                                   isQuorum, temp_i, isDone, 
                                                   prevLogTerm, newCommitIndex, 
                                                   maxAgreeIndex, responseType, 
                                                   leaderId, reqId, req, reqs, 
                                                   resp, timeoutMsg >>

setLeaderHandleAppendEntriesRequest(self) == /\ pc[self] = "setLeaderHandleAppendEntriesRequest"
                                             /\ leader' = [leader EXCEPT ![self] = msg[self].msource]
                                             /\ pc' = [pc EXCEPT ![self] = "returnToFollowerHandleAppendEntriesRequest"]
                                             /\ UNCHANGED << queues, 
                                                             stateMachine, 
                                                             stateMachineDomain, 
                                                             role, log, 
                                                             currentTerm, 
                                                             votedFor, 
                                                             votesResponded, 
                                                             votesGranted, 
                                                             nextIndex, 
                                                             matchIndex, 
                                                             commitIndex, msg, 
                                                             lastTermVar, 
                                                             logOK, grant, 
                                                             isQuorum, temp_i, 
                                                             isDone, 
                                                             prevLogTerm, 
                                                             newCommitIndex, 
                                                             maxAgreeIndex, 
                                                             responseType, 
                                                             leaderId, reqId, 
                                                             req, reqs, resp, 
                                                             timeoutMsg >>

findMaxAgreeIndex(self) == /\ pc[self] = "findMaxAgreeIndex"
                           /\ IF ((temp_i[self] > 0) /\ (~ isDone[self]))
                                 THEN /\ pc' = [pc EXCEPT ![self] = "calculateQuorum"]
                                      /\ UNCHANGED newCommitIndex
                                 ELSE /\ IF (maxAgreeIndex[self] # 0 /\ log[self][maxAgreeIndex[self]].term = currentTerm[self])
                                            THEN /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = maxAgreeIndex[self]]
                                                 /\ Assert(newCommitIndex'[self] >= commitIndex[self], 
                                                           "Failure of assertion at line 319, column 29.")
                                            ELSE /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = commitIndex[self]]
                                      /\ pc' = [pc EXCEPT ![self] = "advanceCommitIndexLeader"]
                           /\ UNCHANGED << queues, stateMachine, 
                                           stateMachineDomain, role, log, 
                                           currentTerm, votedFor, 
                                           votesResponded, votesGranted, 
                                           leader, nextIndex, matchIndex, 
                                           commitIndex, msg, lastTermVar, 
                                           logOK, grant, isQuorum, temp_i, 
                                           isDone, prevLogTerm, maxAgreeIndex, 
                                           responseType, leaderId, reqId, req, 
                                           reqs, resp, timeoutMsg >>

calculateQuorum(self) == /\ pc[self] = "calculateQuorum"
                         /\ isQuorum' = [isQuorum EXCEPT ![self] = Cardinality(({self} \cup {k \in ServerSet : matchIndex[self][k] >= temp_i[self]})) * 2 > NumRaftNodes]
                         /\ IF (isQuorum'[self])
                               THEN /\ maxAgreeIndex' = [maxAgreeIndex EXCEPT ![self] = temp_i[self]]
                                    /\ isDone' = [isDone EXCEPT ![self] = TRUE]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << isDone, maxAgreeIndex >>
                         /\ temp_i' = [temp_i EXCEPT ![self] = temp_i[self] - 1]
                         /\ pc' = [pc EXCEPT ![self] = "findMaxAgreeIndex"]
                         /\ UNCHANGED << queues, stateMachine, 
                                         stateMachineDomain, role, log, 
                                         currentTerm, votedFor, votesResponded, 
                                         votesGranted, leader, nextIndex, 
                                         matchIndex, commitIndex, msg, 
                                         lastTermVar, logOK, grant, 
                                         prevLogTerm, newCommitIndex, 
                                         responseType, leaderId, reqId, req, 
                                         reqs, resp, timeoutMsg >>

advanceCommitIndexLeader(self) == /\ pc[self] = "advanceCommitIndexLeader"
                                  /\ IF (commitIndex[self] < newCommitIndex[self])
                                        THEN /\ \/ /\ FALSE
                                                \/ /\ TRUE
                                             /\ commitIndex' = [commitIndex EXCEPT ![self] = commitIndex[self] + 1]
                                             /\ LET entry == log[self][commitIndex'[self]] IN
                                                  LET command == entry.cmd IN
                                                    /\ IF (command.type = "Get")
                                                          THEN /\ IF (command.key \in stateMachineDomain[self])
                                                                     THEN /\ temp_i' = [temp_i EXCEPT ![self] = <<"ClientGetResponse", stateMachine[self][command.key]>>]
                                                                     ELSE /\ temp_i' = [temp_i EXCEPT ![self] = <<"ClientGetResponse", "null">>]
                                                               /\ UNCHANGED << stateMachine, 
                                                                               stateMachineDomain >>
                                                          ELSE /\ IF (command.type = "Put")
                                                                     THEN /\ stateMachine' = [stateMachine EXCEPT ![self] = [key \in {command.key} |-> command.value] @@ stateMachine[self]]
                                                                          /\ stateMachineDomain' = [stateMachineDomain EXCEPT ![self] = stateMachineDomain[self] \cup {command.key}]
                                                                          /\ temp_i' = [temp_i EXCEPT ![self] = <<"ClientPutResponse", stateMachine'[self][command.key]>>]
                                                                     ELSE /\ PrintT(<<"Unknown command", command>>)
                                                                          /\ Assert(FALSE, 
                                                                                    "Failure of assertion at line 81, column 21 of macro called at line 325, column 25.")
                                                                          /\ UNCHANGED << stateMachine, 
                                                                                          stateMachineDomain, 
                                                                                          temp_i >>
                                                    /\ LET reqOk == command.key \in stateMachineDomain'[self] IN
                                                         \/ /\ queues' = [queues EXCEPT ![entry.client] =  Append(queues[entry.client],     [mtype       |-> temp_i'[self][1],msuccess    |-> TRUE,mresponse   |-> [idx   |-> command.idx,key   |-> command.key,value |-> temp_i'[self][2],ok    |-> reqOk],mleaderHint  |-> self,msource      |-> self,mdest        |-> entry.client])]
                                                         \/ /\ TRUE
                                                            /\ UNCHANGED queues
                                             /\ pc' = [pc EXCEPT ![self] = "advanceCommitIndexLeader"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                             /\ UNCHANGED << queues, 
                                                             stateMachine, 
                                                             stateMachineDomain, 
                                                             commitIndex, 
                                                             temp_i >>
                                  /\ UNCHANGED << role, log, currentTerm, 
                                                  votedFor, votesResponded, 
                                                  votesGranted, leader, 
                                                  nextIndex, matchIndex, msg, 
                                                  lastTermVar, logOK, grant, 
                                                  isQuorum, isDone, 
                                                  prevLogTerm, newCommitIndex, 
                                                  maxAgreeIndex, responseType, 
                                                  leaderId, reqId, req, reqs, 
                                                  resp, timeoutMsg >>

setClientRequest(self) == /\ pc[self] = "setClientRequest"
                          /\ LET cmdData == msg[self].mcmd IN
                               IF (cmdData.type = "Get")
                                  THEN /\ responseType' = [responseType EXCEPT ![self] = "ClientGetResponse"]
                                  ELSE /\ IF (cmdData.type = "Put")
                                             THEN /\ responseType' = [responseType EXCEPT ![self] = "ClientPutResponse"]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 396, column 29.")
                                                  /\ UNCHANGED responseType
                          /\ pc' = [pc EXCEPT ![self] = "followerReplyGetOrPutRequest"]
                          /\ UNCHANGED << queues, stateMachine, 
                                          stateMachineDomain, role, log, 
                                          currentTerm, votedFor, 
                                          votesResponded, votesGranted, leader, 
                                          nextIndex, matchIndex, commitIndex, 
                                          msg, lastTermVar, logOK, grant, 
                                          isQuorum, temp_i, isDone, 
                                          prevLogTerm, newCommitIndex, 
                                          maxAgreeIndex, leaderId, reqId, req, 
                                          reqs, resp, timeoutMsg >>

followerReplyGetOrPutRequest(self) == /\ pc[self] = "followerReplyGetOrPutRequest"
                                      /\ \/ /\ queues' = [queues EXCEPT ![msg[self].msource] =  Append(queues[msg[self].msource],    [mtype       |-> responseType[self],msuccess    |-> FALSE,mresponse   |->  [idx |-> msg[self][mcmd][idx], key |-> msg[self][mcmd][key]],msource     |-> self,mleaderHint |-> leader[self],mdest       |-> msg[self].msource])]
                                         \/ /\ TRUE
                                            /\ UNCHANGED queues
                                      /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                      /\ UNCHANGED << stateMachine, 
                                                      stateMachineDomain, role, 
                                                      log, currentTerm, 
                                                      votedFor, votesResponded, 
                                                      votesGranted, leader, 
                                                      nextIndex, matchIndex, 
                                                      commitIndex, msg, 
                                                      lastTermVar, logOK, 
                                                      grant, isQuorum, temp_i, 
                                                      isDone, prevLogTerm, 
                                                      newCommitIndex, 
                                                      maxAgreeIndex, 
                                                      responseType, leaderId, 
                                                      reqId, req, reqs, resp, 
                                                      timeoutMsg >>

sendGetResponse(self) == /\ pc[self] = "sendGetResponse"
                         /\ LET command == msg[self][mcmd] IN
                              LET isFound == (command[key] \in stateMachineDomain[self]) IN
                                /\ IF (isFound)
                                      THEN /\ temp_i' = [temp_i EXCEPT ![self] = stateMachine[self][command.key]]
                                      ELSE /\ temp_i' = [temp_i EXCEPT ![self] = "null"]
                                /\ \/ /\ queues' = [queues EXCEPT ![msg[self].msource] =  Append(queues[msg[self].msource],    [mtype       |-> "ClientGetResponse",msuccess    |-> TRUE,mresponse   |-> [idx   |-> command.idx,key   |-> command.key,value |-> temp_i'[self],ok    |-> isFound],mleaderHint  |-> self,msource      |-> self,mdest        |-> msg[self].msource])]
                                   \/ /\ TRUE
                                      /\ UNCHANGED queues
                         /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                         /\ UNCHANGED << stateMachine, stateMachineDomain, 
                                         role, log, currentTerm, votedFor, 
                                         votesResponded, votesGranted, leader, 
                                         nextIndex, matchIndex, commitIndex, 
                                         msg, lastTermVar, logOK, grant, 
                                         isQuorum, isDone, prevLogTerm, 
                                         newCommitIndex, maxAgreeIndex, 
                                         responseType, leaderId, reqId, req, 
                                         reqs, resp, timeoutMsg >>

iterateOverProcesses(self) == /\ pc[self] = "iterateOverProcesses"
                              /\ temp_i' = [temp_i EXCEPT ![self] = 1]
                              /\ pc' = [pc EXCEPT ![self] = "assign_i"]
                              /\ UNCHANGED << queues, stateMachine, 
                                              stateMachineDomain, role, log, 
                                              currentTerm, votedFor, 
                                              votesResponded, votesGranted, 
                                              leader, nextIndex, matchIndex, 
                                              commitIndex, msg, lastTermVar, 
                                              logOK, grant, isQuorum, isDone, 
                                              prevLogTerm, newCommitIndex, 
                                              maxAgreeIndex, responseType, 
                                              leaderId, reqId, req, reqs, resp, 
                                              timeoutMsg >>

assign_i(self) == /\ pc[self] = "assign_i"
                  /\ IF (temp_i[self] <= Cardinality(ServerSet))
                        THEN /\ IF (temp_i[self] # self)
                                   THEN /\ LET prevLogIndex == nextIndex[self][temp_i[self]] - 1 IN
                                             LET entries == SubSeq(log[self], nextIndex[self][temp_i[self]], Len(log[self])) IN
                                               /\ IF prevLogIndex > 0
                                                     THEN /\ prevLogTerm' = [prevLogTerm EXCEPT ![self] = log[self][prevLogIndex].term]
                                                     ELSE /\ prevLogTerm' = [prevLogTerm EXCEPT ![self] = 0]
                                               /\ \/ /\ queues' = [queues EXCEPT ![temp_i[self]] =  Append(queues[temp_i[self]],    [mtype         |-> "AppendEntriesRequest",mterm         |-> currentTerm[self],mprevLogIndex |-> prevLogIndex,mprevLogTerm  |-> prevLogTerm'[self],mentries      |-> entries,mcommitIndex  |-> commitIndex[self],msource       |-> self])]
                                                  \/ /\ TRUE
                                                     /\ UNCHANGED queues
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << queues, prevLogTerm >>
                             /\ temp_i' = [temp_i EXCEPT ![self] = temp_i[self] + 1]
                             /\ pc' = [pc EXCEPT ![self] = "assign_i"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                             /\ UNCHANGED << queues, temp_i, prevLogTerm >>
                  /\ UNCHANGED << stateMachine, stateMachineDomain, role, log, 
                                  currentTerm, votedFor, votesResponded, 
                                  votesGranted, leader, nextIndex, matchIndex, 
                                  commitIndex, msg, lastTermVar, logOK, grant, 
                                  isQuorum, isDone, newCommitIndex, 
                                  maxAgreeIndex, responseType, leaderId, reqId, 
                                  req, reqs, resp, timeoutMsg >>

raftNode(self) == leaderElectionLoop(self) \/ checkCardinalityTimeout(self)
                     \/ becomeLeaderWhenAlone(self)
                     \/ broadcastRequestVoteRequest(self)
                     \/ sendRequestVoteResponse(self)
                     \/ writeVotedFor(self)
                     \/ calculateQuorumHandleRequestVoteResponse(self)
                     \/ becomeLeader(self)
                     \/ returnToFollowerHandleAppendEntriesRequest(self)
                     \/ sendAppendEntriesResponseReject(self)
                     \/ applyLogFollower(self)
                     \/ sendAppendEntriesResponse(self)
                     \/ setLeaderHandleAppendEntriesRequest(self)
                     \/ findMaxAgreeIndex(self) \/ calculateQuorum(self)
                     \/ advanceCommitIndexLeader(self)
                     \/ setClientRequest(self)
                     \/ followerReplyGetOrPutRequest(self)
                     \/ sendGetResponse(self) \/ iterateOverProcesses(self)
                     \/ assign_i(self)

propose(self) == /\ pc[self] = "propose"
                 /\ IF (reqId[self] <= Len(reqs[self]))
                       THEN /\ req' = [req EXCEPT ![self] = reqs[self][reqId[self]]]
                            /\ IF (req'[self].type = "Put")
                                  THEN /\ \/ /\ queues' = [queues EXCEPT ![leaderId[self]] =  Append(queues[leaderId[self]],    [mtype   |-> "ClientPutRequest",mcmd    |-> [idx   |-> reqId[self],type  |-> "Put",key   |-> req'[self].key,value |-> req'[self].value],msource |-> self])]
                                          \/ /\ TRUE
                                             /\ UNCHANGED queues
                                  ELSE /\ \/ /\ queues' = [queues EXCEPT ![leaderId[self]] =  Append(queues[leaderId[self]],    [mtype   |-> "ClientGetRequest",mcmd    |-> [idx   |-> reqId[self],type  |-> "Get",key   |-> req'[self].key],msource |-> self])]
                                          \/ /\ TRUE
                                             /\ UNCHANGED queues
                            /\ pc' = [pc EXCEPT ![self] = "receiveResponseClient"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << queues, req >>
                 /\ UNCHANGED << stateMachine, stateMachineDomain, role, log, 
                                 currentTerm, votedFor, votesResponded, 
                                 votesGranted, leader, nextIndex, matchIndex, 
                                 commitIndex, msg, lastTermVar, logOK, grant, 
                                 isQuorum, temp_i, isDone, prevLogTerm, 
                                 newCommitIndex, maxAgreeIndex, responseType, 
                                 leaderId, reqId, reqs, resp, timeoutMsg >>

receiveResponseClient(self) == /\ pc[self] = "receiveResponseClient"
                               /\ Len(queues[self]) > 0 
                               /\ resp' = [resp EXCEPT ![self] = Head(queues[self])]
                               /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                               /\ Assert(resp'[self].mdest = self, 
                                         "Failure of assertion at line 452, column 13.")
                               /\ IF (resp'[self].mleaderHint # 0)
                                     THEN /\ leaderId' = [leaderId EXCEPT ![self] = resp'[self].mleaderHint]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED leaderId
                               /\ PrintT(<<"Response", resp'[self]>>)
                               /\ Assert((req[self].type = "Get" => resp'[self].mtype = "ClientGetResponse") /\ (req[self].type = "Put" => resp'[self].mtype = "ClientPutResponse"), 
                                         "Failure of assertion at line 458, column 13.")
                               /\ IF (resp'[self].msuccess)
                                     THEN /\ LET data == resp'[self].mresponse IN
                                               /\ Assert(data.idx = reqId[self] /\ data.key = req[self].key, 
                                                         "Failure of assertion at line 462, column 21.")
                                               /\ IF (req[self].type = "Get")
                                                     THEN /\ PrintT(<<"Get response received", data.key, data.value>>)
                                                     ELSE /\ PrintT(<<"Put response received", data.key>>)
                                     ELSE /\ TRUE
                               /\ reqId' = [reqId EXCEPT ![self] = reqId[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "propose"]
                               /\ UNCHANGED << stateMachine, 
                                               stateMachineDomain, role, log, 
                                               currentTerm, votedFor, 
                                               votesResponded, votesGranted, 
                                               leader, nextIndex, matchIndex, 
                                               commitIndex, msg, lastTermVar, 
                                               logOK, grant, isQuorum, temp_i, 
                                               isDone, prevLogTerm, 
                                               newCommitIndex, maxAgreeIndex, 
                                               responseType, req, reqs, 
                                               timeoutMsg >>

client(self) == propose(self) \/ receiveResponseClient(self)

sendTimeout(self) == /\ pc[self] = "sendTimeout"
                     /\ \/ /\ FALSE
                        \/ /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "getRaftNodes4"]
                     /\ UNCHANGED << queues, stateMachine, stateMachineDomain, 
                                     role, log, currentTerm, votedFor, 
                                     votesResponded, votesGranted, leader, 
                                     nextIndex, matchIndex, commitIndex, msg, 
                                     lastTermVar, logOK, grant, isQuorum, 
                                     temp_i, isDone, prevLogTerm, 
                                     newCommitIndex, maxAgreeIndex, 
                                     responseType, leaderId, reqId, req, reqs, 
                                     resp, timeoutMsg >>

getRaftNodes4(self) == /\ pc[self] = "getRaftNodes4"
                       /\ \/ /\ queues' = [queues EXCEPT ![(((self - 1) % Cardinality(ServerSet)) + 1)] =  Append(queues[(((self - 1) % Cardinality(ServerSet)) + 1)], timeoutMsg[self])]
                          \/ /\ TRUE
                             /\ UNCHANGED queues
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << stateMachine, stateMachineDomain, role, 
                                       log, currentTerm, votedFor, 
                                       votesResponded, votesGranted, leader, 
                                       nextIndex, matchIndex, commitIndex, msg, 
                                       lastTermVar, logOK, grant, isQuorum, 
                                       temp_i, isDone, prevLogTerm, 
                                       newCommitIndex, maxAgreeIndex, 
                                       responseType, leaderId, reqId, req, 
                                       reqs, resp, timeoutMsg >>

timeouter(self) == sendTimeout(self) \/ getRaftNodes4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: raftNode(self))
           \/ (\E self \in ClientSet: client(self))
           \/ (\E self \in TimeouterSet: timeouter(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(raftNode(self))
        /\ \A self \in ClientSet : WF_vars(client(self))
        /\ \A self \in TimeouterSet : WF_vars(timeouter(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

ElectionSafety == \lnot (\E i, j \in ServerSet:
                                        /\ i /= j
                                        /\ currentTerm[i] = currentTerm[j]
                                        /\ role[i] = "leader"
                                        /\ role[j] = "leader")
LogMatching == \A i, j \in ServerSet:
                        \A k \in 1..Min({Len(log[i]), Len(log[j])}):
                            log[i][k].term = log[j][k].term
                               => SubSeq(log[i], 1, k) = SubSeq(log[j], 1, k)

LeaderCompleteness == \A i \in ServerSet:
                        \A logIdx \in DOMAIN log[i]:
                          logIdx <= commitIndex[i] =>
                            \A j \in ServerSet:
                              role[j] = "leader" /\ currentTerm[j] >= log[i][logIdx].term =>
                                /\ logIdx \in DOMAIN log[j]
                                /\ log[i][logIdx] = log[j][logIdx]

StateMachineSafety == \A i, j \in ServerSet:
                            \A k \in 1..Min({commitIndex[i], commitIndex[j]}):
                                        log[i][k] = log[j][k]

ApplyLogOK == \A i, j \in ServerSet:
                    commitIndex[i] = commitIndex[j] =>
                        /\ stateMachine[i] = stateMachine[j]
                        /\ stateMachineDomain[i] = stateMachineDomain[j]

\* Properties

LeaderAppendOnly == [][\A i \in ServerSet:
                        (role[i] = "leader" /\ role'[i] = "leader")
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

\*LeaderExists == \E i \in ServerSet: role[i] = "leader"
====
