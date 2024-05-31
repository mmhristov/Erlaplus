---- MODULE Raft_Erla ----

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


(*--algorithm Raft_Erla

    variables queues = [id \in NodeSet |-> <<>>];
    define
        ClientSet == {666}
        ServerSet == 1 .. NumRaftNodes
        TimeouterSet == (1 * NumRaftNodes + 1) .. (2 * NumRaftNodes)
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

    macro AdvanceCommitIndex(commitIndex, newCommitIndex, log, stateMachine)
    begin
        while (commitIndex < newCommitIndex) do
            maybeFail();
            commitIndex := commitIndex + 1;
            with entry = log[commitIndex], cmd = entry.cmd do
                print <<"ServerAccept", self, role, cmd>>;
                stateMachine := Append(stateMachine, [mtype |-> "AcceptMessage", mcmd  |-> cmd]);
            end with;
        end while;
    end macro;

    fair process raftNode \in ServerSet
    variables
        \* State
        stateMachine = <<>>;
        role = "follower";
        log = <<>>;
        currentTerm = 0;
        votedFor = 0; votesResponded = {}; votesGranted = {};
        leader = 0;
        nextIndex = <<>>;
        matchIndex = <<>>;
        commitIndex = 0;
        fAdvCommitIdxCh = <<>>;

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
                        msource     |-> self
                    ], msg.msource);
                else
                    \* accept request
                    assert msg.mterm = currentTerm /\ role = "follower" /\ logOK;
                    log  := SubSeq(log, 1, msg.mprevLogIndex) \o msg.mentries;

                    assert msg.mcommitIndex <= Len(log);
                    fAdvCommitIdxCh := msg;
                advanceCommitIndexFollower:
                    AdvanceCommitIndex(commitIndex, msg.mcommitIndex, log, stateMachine); \* commit
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
                        if ((nextIndex[msg.msource] - 1) < 1) then
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
                        AdvanceCommitIndex(commitIndex, newCommitIndex, log, stateMachine); \* commit
                    end if;
                end if;
            elsif (msg.mtype = "ProposeMessage") then
                print <<"Handle ProposeMessage", self>>;

                if (role = "leader") then
                    with entry = [term |-> currentTerm, cmd  |-> msg.mcmd] do
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
                elsif (leader # 0) then
                    redirectProposeMessageToLeader:
                    send([
                        mtype   |-> "ProposeMessage",
                        mcmd    |-> msg.mcmd,
                        msource |-> self
                    ], leader);
                end if;
            end if;
        end while;
    end process;

    fair process client \in ClientSet
    variables
        msg = [mtype |-> "ProposeMessage", mcmd |-> [data |-> "hello"]];
    begin
    propose:
        send(msg, 1); \* send message to raft node 1
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
\* BEGIN TRANSLATION (chksum(pcal) = "a5173e68" /\ chksum(tla) = "a567926e")
\* Process variable msg of process raftNode at line 90 col 9 changed to msg_
VARIABLES queues, pc

(* define statement *)
ClientSet == {666}
ServerSet == 1 .. NumRaftNodes
TimeouterSet == (1 * NumRaftNodes + 1) .. (2 * NumRaftNodes)
NodeSet == ClientSet \union ServerSet

VARIABLES stateMachine, role, log, currentTerm, votedFor, votesResponded, 
          votesGranted, leader, nextIndex, matchIndex, commitIndex, 
          fAdvCommitIdxCh, msg_, lastTermVar, logOK, grant, isQuorum, temp_i, 
          isDone, prevLogTerm, newCommitIndex, maxAgreeIndex, msg, timeoutMsg

vars == << queues, pc, stateMachine, role, log, currentTerm, votedFor, 
           votesResponded, votesGranted, leader, nextIndex, matchIndex, 
           commitIndex, fAdvCommitIdxCh, msg_, lastTermVar, logOK, grant, 
           isQuorum, temp_i, isDone, prevLogTerm, newCommitIndex, 
           maxAgreeIndex, msg, timeoutMsg >>

ProcSet == (ServerSet) \cup (ClientSet) \cup (TimeouterSet)

Init == (* Global variables *)
        /\ queues = [id \in NodeSet |-> <<>>]
        (* Process raftNode *)
        /\ stateMachine = [self \in ServerSet |-> <<>>]
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
        /\ fAdvCommitIdxCh = [self \in ServerSet |-> <<>>]
        /\ msg_ = [self \in ServerSet |-> <<>>]
        /\ lastTermVar = [self \in ServerSet |-> 0]
        /\ logOK = [self \in ServerSet |-> FALSE]
        /\ grant = [self \in ServerSet |-> FALSE]
        /\ isQuorum = [self \in ServerSet |-> FALSE]
        /\ temp_i = [self \in ServerSet |-> 0]
        /\ isDone = [self \in ServerSet |-> FALSE]
        /\ prevLogTerm = [self \in ServerSet |-> 0]
        /\ newCommitIndex = [self \in ServerSet |-> 0]
        /\ maxAgreeIndex = [self \in ServerSet |-> 0]
        (* Process client *)
        /\ msg = [self \in ClientSet |-> [mtype |-> "ProposeMessage", mcmd |-> [data |-> "hello"]]]
        (* Process timeouter *)
        /\ timeoutMsg = [self \in TimeouterSet |-> [mtype |-> "timeout"]]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "leaderElectionLoop"
                                        [] self \in ClientSet -> "propose"
                                        [] self \in TimeouterSet -> "sendTimeout"]

leaderElectionLoop(self) == /\ pc[self] = "leaderElectionLoop"
                            /\ \/ /\ FALSE
                               \/ /\ TRUE
                            /\ Len(queues[self]) > 0 
                            /\ msg_' = [msg_ EXCEPT ![self] = Head(queues[self])]
                            /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                            /\ IF (msg_'[self].mtype = "timeout")
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
                                  ELSE /\ IF (msg_'[self].mtype = "RequestVoteRequest")
                                             THEN /\ IF (msg_'[self].msource = self)
                                                        THEN /\ TRUE
                                                             /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                             /\ UNCHANGED << role, 
                                                                             currentTerm, 
                                                                             votedFor, 
                                                                             leader, 
                                                                             lastTermVar, 
                                                                             logOK, 
                                                                             grant >>
                                                        ELSE /\ IF (msg_'[self].mterm > currentTerm[self])
                                                                   THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg_'[self].mterm]
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
                                                             /\ logOK' = [logOK EXCEPT ![self] = (msg_'[self].mlastLogTerm > lastTermVar'[self]) \/ (msg_'[self].mlastLogTerm = lastTermVar'[self] /\ msg_'[self].mlastLogIndex >= Len(log[self]))]
                                                             /\ grant' = [grant EXCEPT ![self] = (msg_'[self].mterm = currentTerm'[self]) /\ logOK'[self] /\ (votedFor'[self] \in {0, msg_'[self].msource})]
                                                             /\ Assert(msg_'[self].mterm <= currentTerm'[self], 
                                                                       "Failure of assertion at line 150, column 21.")
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
                                             ELSE /\ IF (msg_'[self].mtype = "RequestVoteResponse")
                                                        THEN /\ IF (msg_'[self].mterm > currentTerm[self])
                                                                   THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg_'[self].mterm]
                                                                        /\ role' = [role EXCEPT ![self] = "follower"]
                                                                        /\ votedFor' = [votedFor EXCEPT ![self] = 0]
                                                                        /\ leader' = [leader EXCEPT ![self] = 0]
                                                                   ELSE /\ TRUE
                                                                        /\ UNCHANGED << role, 
                                                                                        currentTerm, 
                                                                                        votedFor, 
                                                                                        leader >>
                                                             /\ IF (msg_'[self].mterm < currentTerm'[self])
                                                                   THEN /\ TRUE
                                                                        /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                        /\ UNCHANGED << votesResponded, 
                                                                                        votesGranted >>
                                                                   ELSE /\ Assert(msg_'[self].mterm = currentTerm'[self], 
                                                                                  "Failure of assertion at line 171, column 21.")
                                                                        /\ votesResponded' = [votesResponded EXCEPT ![self] = votesResponded[self] \cup {self}]
                                                                        /\ IF (msg_'[self].mvoteGranted)
                                                                              THEN /\ votesGranted' = [votesGranted EXCEPT ![self] = votesGranted[self] \cup {msg_'[self].msource}]
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
                                                        ELSE /\ IF (msg_'[self].mtype = "AppendEntriesRequest")
                                                                   THEN /\ IF (msg_'[self].mterm > currentTerm[self])
                                                                              THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg_'[self].mterm]
                                                                                   /\ role' = [role EXCEPT ![self] = "follower"]
                                                                                   /\ votedFor' = [votedFor EXCEPT ![self] = 0]
                                                                                   /\ leader' = [leader EXCEPT ![self] = 0]
                                                                              ELSE /\ TRUE
                                                                                   /\ UNCHANGED << role, 
                                                                                                   currentTerm, 
                                                                                                   votedFor, 
                                                                                                   leader >>
                                                                        /\ logOK' = [logOK EXCEPT ![self] = msg_'[self].mprevLogIndex = 0 \/ (msg_'[self].mprevLogIndex > 0 /\ msg_'[self].mprevLogIndex <= Len(log[self]) /\ msg_'[self].mprevLogTerm = log[self][msg_'[self].mprevLogIndex].term)]
                                                                        /\ Assert(msg_'[self].mterm <= currentTerm'[self], 
                                                                                  "Failure of assertion at line 193, column 17.")
                                                                        /\ IF (msg_'[self].mterm = currentTerm'[self])
                                                                              THEN /\ pc' = [pc EXCEPT ![self] = "setLeaderHandleAppendEntriesRequest"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "returnToFollowerHandleAppendEntriesRequest"]
                                                                        /\ UNCHANGED << log, 
                                                                                        nextIndex, 
                                                                                        matchIndex, 
                                                                                        temp_i, 
                                                                                        isDone, 
                                                                                        maxAgreeIndex >>
                                                                   ELSE /\ IF (msg_'[self].mtype = "AppendEntriesResponse")
                                                                              THEN /\ IF (msg_'[self].mterm > currentTerm[self])
                                                                                         THEN /\ currentTerm' = [currentTerm EXCEPT ![self] = msg_'[self].mterm]
                                                                                              /\ role' = [role EXCEPT ![self] = "follower"]
                                                                                              /\ votedFor' = [votedFor EXCEPT ![self] = 0]
                                                                                              /\ leader' = [leader EXCEPT ![self] = 0]
                                                                                         ELSE /\ TRUE
                                                                                              /\ UNCHANGED << role, 
                                                                                                              currentTerm, 
                                                                                                              votedFor, 
                                                                                                              leader >>
                                                                                   /\ PrintT(<<"Handle AppendEntriesResponse", msg_'[self].msource, msg_'[self].msuccess, msg_'[self].mmatchIndex, msg_'[self].mterm>>)
                                                                                   /\ IF (msg_'[self].mterm < currentTerm'[self])
                                                                                         THEN /\ TRUE
                                                                                              /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                                                              /\ UNCHANGED << nextIndex, 
                                                                                                              matchIndex, 
                                                                                                              temp_i, 
                                                                                                              isDone, 
                                                                                                              maxAgreeIndex >>
                                                                                         ELSE /\ Assert(msg_'[self].mterm = currentTerm'[self], 
                                                                                                        "Failure of assertion at line 240, column 21.")
                                                                                              /\ IF (msg_'[self].msuccess)
                                                                                                    THEN /\ nextIndex' = [nextIndex EXCEPT ![self][msg_'[self].msource] = msg_'[self].mmatchIndex + 1]
                                                                                                         /\ matchIndex' = [matchIndex EXCEPT ![self][msg_'[self].msource] = msg_'[self].mmatchIndex]
                                                                                                    ELSE /\ IF ((nextIndex[self][msg_'[self].msource] - 1) < 1)
                                                                                                               THEN /\ nextIndex' = [nextIndex EXCEPT ![self][msg_'[self].msource] = nextIndex[self][msg_'[self].msource] - 1]
                                                                                                               ELSE /\ nextIndex' = [nextIndex EXCEPT ![self][msg_'[self].msource] = 1]
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
                                                                              ELSE /\ IF (msg_'[self].mtype = "ProposeMessage")
                                                                                         THEN /\ PrintT(<<"Handle ProposeMessage", self>>)
                                                                                              /\ IF (role[self] = "leader")
                                                                                                    THEN /\ LET entry == [term |-> currentTerm[self], cmd  |-> msg_'[self].mcmd] IN
                                                                                                              log' = [log EXCEPT ![self] = Append(log[self], entry)]
                                                                                                         /\ \/ /\ FALSE
                                                                                                            \/ /\ TRUE
                                                                                                         /\ pc' = [pc EXCEPT ![self] = "iterateOverProcesses"]
                                                                                                    ELSE /\ IF (leader[self] # 0)
                                                                                                               THEN /\ pc' = [pc EXCEPT ![self] = "redirectProposeMessageToLeader"]
                                                                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
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
                            /\ UNCHANGED << stateMachine, commitIndex, 
                                            fAdvCommitIdxCh, isQuorum, 
                                            prevLogTerm, newCommitIndex, msg, 
                                            timeoutMsg >>

checkCardinalityTimeout(self) == /\ pc[self] = "checkCardinalityTimeout"
                                 /\ IF (Cardinality(ServerSet) = 1)
                                       THEN /\ pc' = [pc EXCEPT ![self] = "becomeLeaderWhenAlone"]
                                            /\ UNCHANGED temp_i
                                       ELSE /\ temp_i' = [temp_i EXCEPT ![self] = 1]
                                            /\ pc' = [pc EXCEPT ![self] = "broadcastRequestVoteRequest"]
                                 /\ UNCHANGED << queues, stateMachine, role, 
                                                 log, currentTerm, votedFor, 
                                                 votesResponded, votesGranted, 
                                                 leader, nextIndex, matchIndex, 
                                                 commitIndex, fAdvCommitIdxCh, 
                                                 msg_, lastTermVar, logOK, 
                                                 grant, isQuorum, isDone, 
                                                 prevLogTerm, newCommitIndex, 
                                                 maxAgreeIndex, msg, 
                                                 timeoutMsg >>

becomeLeaderWhenAlone(self) == /\ pc[self] = "becomeLeaderWhenAlone"
                               /\ role' = [role EXCEPT ![self] = "leader"]
                               /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> Len(log[self]) + 1]]
                               /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                               /\ leader' = [leader EXCEPT ![self] = self]
                               /\ PrintT(<<"BecomeLeader", ToString(self)>>)
                               /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                               /\ UNCHANGED << queues, stateMachine, log, 
                                               currentTerm, votedFor, 
                                               votesResponded, votesGranted, 
                                               commitIndex, fAdvCommitIdxCh, 
                                               msg_, lastTermVar, logOK, grant, 
                                               isQuorum, temp_i, isDone, 
                                               prevLogTerm, newCommitIndex, 
                                               maxAgreeIndex, msg, timeoutMsg >>

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
                                     /\ UNCHANGED << stateMachine, role, log, 
                                                     currentTerm, votedFor, 
                                                     votesResponded, 
                                                     votesGranted, leader, 
                                                     nextIndex, matchIndex, 
                                                     commitIndex, 
                                                     fAdvCommitIdxCh, msg_, 
                                                     lastTermVar, logOK, grant, 
                                                     isQuorum, isDone, 
                                                     prevLogTerm, 
                                                     newCommitIndex, 
                                                     maxAgreeIndex, msg, 
                                                     timeoutMsg >>

sendRequestVoteResponse(self) == /\ pc[self] = "sendRequestVoteResponse"
                                 /\ \/ /\ queues' = [queues EXCEPT ![msg_[self].msource] =  Append(queues[msg_[self].msource],    [mtype        |-> "RequestVoteResponse",mterm        |-> currentTerm[self],mvoteGranted |-> grant[self],msource      |-> self])]
                                    \/ /\ TRUE
                                       /\ UNCHANGED queues
                                 /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                 /\ UNCHANGED << stateMachine, role, log, 
                                                 currentTerm, votedFor, 
                                                 votesResponded, votesGranted, 
                                                 leader, nextIndex, matchIndex, 
                                                 commitIndex, fAdvCommitIdxCh, 
                                                 msg_, lastTermVar, logOK, 
                                                 grant, isQuorum, temp_i, 
                                                 isDone, prevLogTerm, 
                                                 newCommitIndex, maxAgreeIndex, 
                                                 msg, timeoutMsg >>

writeVotedFor(self) == /\ pc[self] = "writeVotedFor"
                       /\ votedFor' = [votedFor EXCEPT ![self] = msg_[self].msource]
                       /\ pc' = [pc EXCEPT ![self] = "sendRequestVoteResponse"]
                       /\ UNCHANGED << queues, stateMachine, role, log, 
                                       currentTerm, votesResponded, 
                                       votesGranted, leader, nextIndex, 
                                       matchIndex, commitIndex, 
                                       fAdvCommitIdxCh, msg_, lastTermVar, 
                                       logOK, grant, isQuorum, temp_i, isDone, 
                                       prevLogTerm, newCommitIndex, 
                                       maxAgreeIndex, msg, timeoutMsg >>

calculateQuorumHandleRequestVoteResponse(self) == /\ pc[self] = "calculateQuorumHandleRequestVoteResponse"
                                                  /\ isQuorum' = [isQuorum EXCEPT ![self] = Cardinality(votesGranted[self]) * 2 > NumRaftNodes]
                                                  /\ IF (role[self] = "candidate" /\ isQuorum'[self])
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "becomeLeader"]
                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                                  /\ UNCHANGED << queues, 
                                                                  stateMachine, 
                                                                  role, log, 
                                                                  currentTerm, 
                                                                  votedFor, 
                                                                  votesResponded, 
                                                                  votesGranted, 
                                                                  leader, 
                                                                  nextIndex, 
                                                                  matchIndex, 
                                                                  commitIndex, 
                                                                  fAdvCommitIdxCh, 
                                                                  msg_, 
                                                                  lastTermVar, 
                                                                  logOK, grant, 
                                                                  temp_i, 
                                                                  isDone, 
                                                                  prevLogTerm, 
                                                                  newCommitIndex, 
                                                                  maxAgreeIndex, 
                                                                  msg, 
                                                                  timeoutMsg >>

becomeLeader(self) == /\ pc[self] = "becomeLeader"
                      /\ role' = [role EXCEPT ![self] = "leader"]
                      /\ nextIndex' = [nextIndex EXCEPT ![self] = [j \in ServerSet |-> Len(log[self]) + 1]]
                      /\ matchIndex' = [matchIndex EXCEPT ![self] = [j \in ServerSet |-> 0]]
                      /\ leader' = [leader EXCEPT ![self] = self]
                      /\ PrintT(<<"BecomeLeader", ToString(self)>>)
                      /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                      /\ UNCHANGED << queues, stateMachine, log, currentTerm, 
                                      votedFor, votesResponded, votesGranted, 
                                      commitIndex, fAdvCommitIdxCh, msg_, 
                                      lastTermVar, logOK, grant, isQuorum, 
                                      temp_i, isDone, prevLogTerm, 
                                      newCommitIndex, maxAgreeIndex, msg, 
                                      timeoutMsg >>

returnToFollowerHandleAppendEntriesRequest(self) == /\ pc[self] = "returnToFollowerHandleAppendEntriesRequest"
                                                    /\ IF (msg_[self].mterm = currentTerm[self] /\ role[self] = "candidate")
                                                          THEN /\ role' = [role EXCEPT ![self] = "follower"]
                                                          ELSE /\ TRUE
                                                               /\ role' = role
                                                    /\ IF ((msg_[self].mterm < currentTerm[self]) \/ (msg_[self].mterm = currentTerm[self] /\ role'[self] = "follower" /\ (~ logOK[self])))
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "sendAppendEntriesResponseReject"]
                                                               /\ UNCHANGED << log, 
                                                                               fAdvCommitIdxCh >>
                                                          ELSE /\ Assert(msg_[self].mterm = currentTerm[self] /\ role'[self] = "follower" /\ logOK[self], 
                                                                         "Failure of assertion at line 215, column 21.")
                                                               /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, msg_[self].mprevLogIndex) \o msg_[self].mentries]
                                                               /\ Assert(msg_[self].mcommitIndex <= Len(log'[self]), 
                                                                         "Failure of assertion at line 218, column 21.")
                                                               /\ fAdvCommitIdxCh' = [fAdvCommitIdxCh EXCEPT ![self] = msg_[self]]
                                                               /\ pc' = [pc EXCEPT ![self] = "advanceCommitIndexFollower"]
                                                    /\ UNCHANGED << queues, 
                                                                    stateMachine, 
                                                                    currentTerm, 
                                                                    votedFor, 
                                                                    votesResponded, 
                                                                    votesGranted, 
                                                                    leader, 
                                                                    nextIndex, 
                                                                    matchIndex, 
                                                                    commitIndex, 
                                                                    msg_, 
                                                                    lastTermVar, 
                                                                    logOK, 
                                                                    grant, 
                                                                    isQuorum, 
                                                                    temp_i, 
                                                                    isDone, 
                                                                    prevLogTerm, 
                                                                    newCommitIndex, 
                                                                    maxAgreeIndex, 
                                                                    msg, 
                                                                    timeoutMsg >>

sendAppendEntriesResponseReject(self) == /\ pc[self] = "sendAppendEntriesResponseReject"
                                         /\ \/ /\ queues' = [queues EXCEPT ![msg_[self].msource] =  Append(queues[msg_[self].msource],    [mtype       |-> "AppendEntriesResponse",mterm       |-> currentTerm[self],msuccess    |-> FALSE,mmatchIndex |-> 0,msource     |-> self])]
                                            \/ /\ TRUE
                                               /\ UNCHANGED queues
                                         /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                         /\ UNCHANGED << stateMachine, role, 
                                                         log, currentTerm, 
                                                         votedFor, 
                                                         votesResponded, 
                                                         votesGranted, leader, 
                                                         nextIndex, matchIndex, 
                                                         commitIndex, 
                                                         fAdvCommitIdxCh, msg_, 
                                                         lastTermVar, logOK, 
                                                         grant, isQuorum, 
                                                         temp_i, isDone, 
                                                         prevLogTerm, 
                                                         newCommitIndex, 
                                                         maxAgreeIndex, msg, 
                                                         timeoutMsg >>

advanceCommitIndexFollower(self) == /\ pc[self] = "advanceCommitIndexFollower"
                                    /\ IF (commitIndex[self] < (msg_[self].mcommitIndex))
                                          THEN /\ \/ /\ FALSE
                                                  \/ /\ TRUE
                                               /\ commitIndex' = [commitIndex EXCEPT ![self] = commitIndex[self] + 1]
                                               /\ LET entry == log[self][commitIndex'[self]] IN
                                                    LET cmd == entry.cmd IN
                                                      /\ PrintT(<<"ServerAccept", self, role[self], cmd>>)
                                                      /\ stateMachine' = [stateMachine EXCEPT ![self] = Append(stateMachine[self], [mtype |-> "AcceptMessage", mcmd  |-> cmd])]
                                               /\ pc' = [pc EXCEPT ![self] = "advanceCommitIndexFollower"]
                                               /\ UNCHANGED queues
                                          ELSE /\ \/ /\ queues' = [queues EXCEPT ![msg_[self].msource] =  Append(queues[msg_[self].msource],    [mtype       |-> "AppendEntriesResponse",mterm       |-> currentTerm[self],msuccess    |-> TRUE,mmatchIndex |-> msg_[self].mprevLogIndex + Len(msg_[self].mentries),msource     |-> self])]
                                                  \/ /\ TRUE
                                                     /\ UNCHANGED queues
                                               /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                               /\ UNCHANGED << stateMachine, 
                                                               commitIndex >>
                                    /\ UNCHANGED << role, log, currentTerm, 
                                                    votedFor, votesResponded, 
                                                    votesGranted, leader, 
                                                    nextIndex, matchIndex, 
                                                    fAdvCommitIdxCh, msg_, 
                                                    lastTermVar, logOK, grant, 
                                                    isQuorum, temp_i, isDone, 
                                                    prevLogTerm, 
                                                    newCommitIndex, 
                                                    maxAgreeIndex, msg, 
                                                    timeoutMsg >>

setLeaderHandleAppendEntriesRequest(self) == /\ pc[self] = "setLeaderHandleAppendEntriesRequest"
                                             /\ leader' = [leader EXCEPT ![self] = msg_[self].msource]
                                             /\ pc' = [pc EXCEPT ![self] = "returnToFollowerHandleAppendEntriesRequest"]
                                             /\ UNCHANGED << queues, 
                                                             stateMachine, 
                                                             role, log, 
                                                             currentTerm, 
                                                             votedFor, 
                                                             votesResponded, 
                                                             votesGranted, 
                                                             nextIndex, 
                                                             matchIndex, 
                                                             commitIndex, 
                                                             fAdvCommitIdxCh, 
                                                             msg_, lastTermVar, 
                                                             logOK, grant, 
                                                             isQuorum, temp_i, 
                                                             isDone, 
                                                             prevLogTerm, 
                                                             newCommitIndex, 
                                                             maxAgreeIndex, 
                                                             msg, timeoutMsg >>

findMaxAgreeIndex(self) == /\ pc[self] = "findMaxAgreeIndex"
                           /\ IF ((temp_i[self] > 0) /\ (~ isDone[self]))
                                 THEN /\ pc' = [pc EXCEPT ![self] = "calculateQuorum"]
                                      /\ UNCHANGED newCommitIndex
                                 ELSE /\ IF (maxAgreeIndex[self] # 0 /\ log[self][maxAgreeIndex[self]].term = currentTerm[self])
                                            THEN /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = maxAgreeIndex[self]]
                                                 /\ Assert(newCommitIndex'[self] >= commitIndex[self], 
                                                           "Failure of assertion at line 271, column 29.")
                                            ELSE /\ newCommitIndex' = [newCommitIndex EXCEPT ![self] = commitIndex[self]]
                                      /\ pc' = [pc EXCEPT ![self] = "advanceCommitIndexLeader"]
                           /\ UNCHANGED << queues, stateMachine, role, log, 
                                           currentTerm, votedFor, 
                                           votesResponded, votesGranted, 
                                           leader, nextIndex, matchIndex, 
                                           commitIndex, fAdvCommitIdxCh, msg_, 
                                           lastTermVar, logOK, grant, isQuorum, 
                                           temp_i, isDone, prevLogTerm, 
                                           maxAgreeIndex, msg, timeoutMsg >>

calculateQuorum(self) == /\ pc[self] = "calculateQuorum"
                         /\ isQuorum' = [isQuorum EXCEPT ![self] = Cardinality(({self} \cup {k \in ServerSet : matchIndex[self][k] >= temp_i[self]})) * 2 > NumRaftNodes]
                         /\ IF (isQuorum'[self])
                               THEN /\ maxAgreeIndex' = [maxAgreeIndex EXCEPT ![self] = temp_i[self]]
                                    /\ isDone' = [isDone EXCEPT ![self] = TRUE]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << isDone, maxAgreeIndex >>
                         /\ temp_i' = [temp_i EXCEPT ![self] = temp_i[self] - 1]
                         /\ pc' = [pc EXCEPT ![self] = "findMaxAgreeIndex"]
                         /\ UNCHANGED << queues, stateMachine, role, log, 
                                         currentTerm, votedFor, votesResponded, 
                                         votesGranted, leader, nextIndex, 
                                         matchIndex, commitIndex, 
                                         fAdvCommitIdxCh, msg_, lastTermVar, 
                                         logOK, grant, prevLogTerm, 
                                         newCommitIndex, msg, timeoutMsg >>

advanceCommitIndexLeader(self) == /\ pc[self] = "advanceCommitIndexLeader"
                                  /\ IF (commitIndex[self] < newCommitIndex[self])
                                        THEN /\ \/ /\ FALSE
                                                \/ /\ TRUE
                                             /\ commitIndex' = [commitIndex EXCEPT ![self] = commitIndex[self] + 1]
                                             /\ LET entry == log[self][commitIndex'[self]] IN
                                                  LET cmd == entry.cmd IN
                                                    /\ PrintT(<<"ServerAccept", self, role[self], cmd>>)
                                                    /\ stateMachine' = [stateMachine EXCEPT ![self] = Append(stateMachine[self], [mtype |-> "AcceptMessage", mcmd  |-> cmd])]
                                             /\ pc' = [pc EXCEPT ![self] = "advanceCommitIndexLeader"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                             /\ UNCHANGED << stateMachine, 
                                                             commitIndex >>
                                  /\ UNCHANGED << queues, role, log, 
                                                  currentTerm, votedFor, 
                                                  votesResponded, votesGranted, 
                                                  leader, nextIndex, 
                                                  matchIndex, fAdvCommitIdxCh, 
                                                  msg_, lastTermVar, logOK, 
                                                  grant, isQuorum, temp_i, 
                                                  isDone, prevLogTerm, 
                                                  newCommitIndex, 
                                                  maxAgreeIndex, msg, 
                                                  timeoutMsg >>

iterateOverProcesses(self) == /\ pc[self] = "iterateOverProcesses"
                              /\ temp_i' = [temp_i EXCEPT ![self] = 1]
                              /\ pc' = [pc EXCEPT ![self] = "assign_i"]
                              /\ UNCHANGED << queues, stateMachine, role, log, 
                                              currentTerm, votedFor, 
                                              votesResponded, votesGranted, 
                                              leader, nextIndex, matchIndex, 
                                              commitIndex, fAdvCommitIdxCh, 
                                              msg_, lastTermVar, logOK, grant, 
                                              isQuorum, isDone, prevLogTerm, 
                                              newCommitIndex, maxAgreeIndex, 
                                              msg, timeoutMsg >>

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
                  /\ UNCHANGED << stateMachine, role, log, currentTerm, 
                                  votedFor, votesResponded, votesGranted, 
                                  leader, nextIndex, matchIndex, commitIndex, 
                                  fAdvCommitIdxCh, msg_, lastTermVar, logOK, 
                                  grant, isQuorum, isDone, newCommitIndex, 
                                  maxAgreeIndex, msg, timeoutMsg >>

redirectProposeMessageToLeader(self) == /\ pc[self] = "redirectProposeMessageToLeader"
                                        /\ \/ /\ queues' = [queues EXCEPT ![leader[self]] =  Append(queues[leader[self]],    [mtype   |-> "ProposeMessage",mcmd    |-> msg_[self].mcmd,msource |-> self])]
                                           \/ /\ TRUE
                                              /\ UNCHANGED queues
                                        /\ pc' = [pc EXCEPT ![self] = "leaderElectionLoop"]
                                        /\ UNCHANGED << stateMachine, role, 
                                                        log, currentTerm, 
                                                        votedFor, 
                                                        votesResponded, 
                                                        votesGranted, leader, 
                                                        nextIndex, matchIndex, 
                                                        commitIndex, 
                                                        fAdvCommitIdxCh, msg_, 
                                                        lastTermVar, logOK, 
                                                        grant, isQuorum, 
                                                        temp_i, isDone, 
                                                        prevLogTerm, 
                                                        newCommitIndex, 
                                                        maxAgreeIndex, msg, 
                                                        timeoutMsg >>

raftNode(self) == leaderElectionLoop(self) \/ checkCardinalityTimeout(self)
                     \/ becomeLeaderWhenAlone(self)
                     \/ broadcastRequestVoteRequest(self)
                     \/ sendRequestVoteResponse(self)
                     \/ writeVotedFor(self)
                     \/ calculateQuorumHandleRequestVoteResponse(self)
                     \/ becomeLeader(self)
                     \/ returnToFollowerHandleAppendEntriesRequest(self)
                     \/ sendAppendEntriesResponseReject(self)
                     \/ advanceCommitIndexFollower(self)
                     \/ setLeaderHandleAppendEntriesRequest(self)
                     \/ findMaxAgreeIndex(self) \/ calculateQuorum(self)
                     \/ advanceCommitIndexLeader(self)
                     \/ iterateOverProcesses(self) \/ assign_i(self)
                     \/ redirectProposeMessageToLeader(self)

propose(self) == /\ pc[self] = "propose"
                 /\ \/ /\ queues' = [queues EXCEPT ![1] =  Append(queues[1], msg[self])]
                    \/ /\ TRUE
                       /\ UNCHANGED queues
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << stateMachine, role, log, currentTerm, 
                                 votedFor, votesResponded, votesGranted, 
                                 leader, nextIndex, matchIndex, commitIndex, 
                                 fAdvCommitIdxCh, msg_, lastTermVar, logOK, 
                                 grant, isQuorum, temp_i, isDone, prevLogTerm, 
                                 newCommitIndex, maxAgreeIndex, msg, 
                                 timeoutMsg >>

client(self) == propose(self)

sendTimeout(self) == /\ pc[self] = "sendTimeout"
                     /\ \/ /\ FALSE
                        \/ /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "getRaftNodes4"]
                     /\ UNCHANGED << queues, stateMachine, role, log, 
                                     currentTerm, votedFor, votesResponded, 
                                     votesGranted, leader, nextIndex, 
                                     matchIndex, commitIndex, fAdvCommitIdxCh, 
                                     msg_, lastTermVar, logOK, grant, isQuorum, 
                                     temp_i, isDone, prevLogTerm, 
                                     newCommitIndex, maxAgreeIndex, msg, 
                                     timeoutMsg >>

getRaftNodes4(self) == /\ pc[self] = "getRaftNodes4"
                       /\ \/ /\ queues' = [queues EXCEPT ![(((self - 1) % Cardinality(ServerSet)) + 1)] =  Append(queues[(((self - 1) % Cardinality(ServerSet)) + 1)], timeoutMsg[self])]
                          \/ /\ TRUE
                             /\ UNCHANGED queues
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << stateMachine, role, log, currentTerm, 
                                       votedFor, votesResponded, votesGranted, 
                                       leader, nextIndex, matchIndex, 
                                       commitIndex, fAdvCommitIdxCh, msg_, 
                                       lastTermVar, logOK, grant, isQuorum, 
                                       temp_i, isDone, prevLogTerm, 
                                       newCommitIndex, maxAgreeIndex, msg, 
                                       timeoutMsg >>

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
                                        /\ log[i][k] = log[j][k]
                                        /\ stateMachine[i][k] = stateMachine[j][k]

\* Properties

LeaderAppendOnly == [][\A i \in ServerSet:
                        (role[i] = "leader" /\ role'[i] = "leader")
                            => log[i] = SubSeq(log'[i], 1, Len(log[i]))]_vars

LeaderExists == \E i \in ServerSet: role[i] = "leader"
====
