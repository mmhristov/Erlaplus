------------------------------- MODULE locksvc -------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumClients

(*
--algorithm locksvc

  variables queues = [id \in NodeSet |-> <<>>];
  define
    ServerID == 0
    ServerSet == {ServerID}
    ClientSet == 1 .. (NumClients)
    NodeSet == (ServerSet) \union (ClientSet)
  end define;

  fair process Server \in ServerSet
    variables msg = <<>>; q = <<>>;
  begin
    serverLoop:
    while (TRUE) do
        receive(msg);
        if (msg.type = "lock") then
            if (q = <<>>) then
            respondLock:
                send("grant", msg.sender);
            end if;
        addToQ:
            q := Append(q, (msg).sender);
        elsif (msg.type = "unlock") then
            q := Tail(q);
            if (q # <<>>) then
            respond_Unlock:
                send("grant", Head(q));
           end if;
        end if;
    end while;
  end process;

  fair process Client \in ClientSet
   variables
    req = <<>>, resp = "", hasLock = FALSE;
  begin
  acquireLock:
    req := [sender |-> self, type |-> "lock"];
    (* send lock request to server *)
    send(req, ServerID);
  criticalSection:
    (* receive response *)
    receive(resp);
    assert(resp = "grant");
    hasLock := TRUE;
  unlock:
    req := [sender |-> self, type |-> "unlock"];
    (* send unlock request *)
    send(req, ServerID);
    hasLock := FALSE;
  end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "10f9d442" /\ chksum(tla) = "732df5bb")
VARIABLES queues, pc

(* define statement *)
ServerID == 0
ServerSet == {ServerID}
ClientSet == 1 .. (NumClients)
NodeSet == (ServerSet) \union (ClientSet)

VARIABLES msg, q, req, resp, hasLock

vars == << queues, pc, msg, q, req, resp, hasLock >>

ProcSet == (ServerSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ queues = [id \in NodeSet |-> <<>>]
        (* Process Server *)
        /\ msg = [self \in ServerSet |-> <<>>]
        /\ q = [self \in ServerSet |-> <<>>]
        (* Process Client *)
        /\ req = [self \in ClientSet |-> <<>>]
        /\ resp = [self \in ClientSet |-> ""]
        /\ hasLock = [self \in ClientSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ClientSet -> "acquireLock"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ Len(queues[self]) > 0 
                    /\ msg' = [msg EXCEPT ![self] = Head(queues[self])]
                    /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                    /\ IF (msg'[self].type = "lock")
                          THEN /\ IF (q[self] = <<>>)
                                     THEN /\ pc' = [pc EXCEPT ![self] = "respondLock"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "addToQ"]
                               /\ q' = q
                          ELSE /\ IF (msg'[self].type = "unlock")
                                     THEN /\ q' = [q EXCEPT ![self] = Tail(q[self])]
                                          /\ IF (q'[self] # <<>>)
                                                THEN /\ pc' = [pc EXCEPT ![self] = "respond_Unlock"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                          /\ q' = q
                    /\ UNCHANGED << req, resp, hasLock >>

addToQ(self) == /\ pc[self] = "addToQ"
                /\ q' = [q EXCEPT ![self] = Append(q[self], (msg[self]).sender)]
                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                /\ UNCHANGED << queues, msg, req, resp, hasLock >>

respondLock(self) == /\ pc[self] = "respondLock"
                     /\ \/ /\ queues' = [queues EXCEPT ![msg[self].sender] =  Append(queues[msg[self].sender], "grant")]
                        \/ /\ TRUE
                           /\ UNCHANGED queues
                     /\ pc' = [pc EXCEPT ![self] = "addToQ"]
                     /\ UNCHANGED << msg, q, req, resp, hasLock >>

respond_Unlock(self) == /\ pc[self] = "respond_Unlock"
                        /\ \/ /\ queues' = [queues EXCEPT ![Head(q[self])] =  Append(queues[Head(q[self])], "grant")]
                           \/ /\ TRUE
                              /\ UNCHANGED queues
                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                        /\ UNCHANGED << msg, q, req, resp, hasLock >>

Server(self) == serverLoop(self) \/ addToQ(self) \/ respondLock(self)
                   \/ respond_Unlock(self)

acquireLock(self) == /\ pc[self] = "acquireLock"
                     /\ req' = [req EXCEPT ![self] = [sender |-> self, type |-> "lock"]]
                     /\ \/ /\ queues' = [queues EXCEPT ![ServerID] =  Append(queues[ServerID], req'[self])]
                        \/ /\ TRUE
                           /\ UNCHANGED queues
                     /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                     /\ UNCHANGED << msg, q, resp, hasLock >>

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ Len(queues[self]) > 0 
                         /\ resp' = [resp EXCEPT ![self] = Head(queues[self])]
                         /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                         /\ Assert((resp'[self] = "grant"), 
                                   "Failure of assertion at line 52, column 5.")
                         /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "unlock"]
                         /\ UNCHANGED << msg, q, req >>

unlock(self) == /\ pc[self] = "unlock"
                /\ req' = [req EXCEPT ![self] = [sender |-> self, type |-> "unlock"]]
                /\ \/ /\ queues' = [queues EXCEPT ![ServerID] =  Append(queues[ServerID], req'[self])]
                   \/ /\ TRUE
                      /\ UNCHANGED queues
                /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << msg, q, resp >>

Client(self) == acquireLock(self) \/ criticalSection(self) \/ unlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ServerSet: Server(self))
           \/ (\E self \in ClientSet: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ServerSet : WF_vars(Server(self))
        /\ \A self \in ClientSet : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants

Safety == \lnot (\A i, j \in ClientSet:
                            /\ i /= j
                            /\ hasLock[i]
                            /\ hasLock[j])

\* Properties

ProgressOK(i) == pc[i] = "acquireLock" ~> pc[i] = "criticalSection"
Liveness == \A i \in NodeSet: ProgressOK(i)

=====
