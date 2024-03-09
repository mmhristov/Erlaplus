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
    variables msg; q = <<>>, response_message = <<>>;
  begin
    serverLoop:
    while (TRUE) do
        receive(msg);
        if (msg.type = "lock") then
            if (q = <<>>) then
                response_message := "grant";
                print Append("Granted lock to proc ", ToString(msg.from));
                respondLock:
                send(response_message, msg.from);
            end if;
            addToQ:
            q := Append(q, (msg).from);
        elsif (msg.type = "unlock") then
            q := Tail(q);
            print Append("Granted unlock to proc ", ToString(msg.from));
            if (q # <<>>) then
                response_message := "grant";
                respond_Unlock:
                send(response_message, Head(q));
           end if;
        end if;
    end while;
  end process;

  fair process Client \in ClientSet
   variables request = <<>>, response = <<>>, hasLock = FALSE;
  begin
  acquireLock:
    request := [from |-> self, type |-> "lock"];
    send(request, 0); \* send to server
  criticalSection:
    receive(response);
    assert(response = "grant");
    hasLock := TRUE;
  unlock:
    request := [from |-> self, type |-> "unlock"];
    send(request, 0);
    hasLock := FALSE;
  end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "de7b9bc8" /\ chksum(tla) = "ce19237d")
CONSTANT defaultInitValue
VARIABLES queues, pc

(* define statement *)
ServerID == 0
ServerSet == {ServerID}
ClientSet == 1 .. (NumClients)
NodeSet == (ServerSet) \union (ClientSet)

VARIABLES msg, q, response_message, request, response, hasLock

vars == << queues, pc, msg, q, response_message, request, response, hasLock
        >>

ProcSet == (ServerSet) \cup (ClientSet)

Init == (* Global variables *)
        /\ queues = [id \in NodeSet |-> <<>>]
        (* Process Server *)
        /\ msg = [self \in ServerSet |-> defaultInitValue]
        /\ q = [self \in ServerSet |-> <<>>]
        /\ response_message = [self \in ServerSet |-> <<>>]
        (* Process Client *)
        /\ request = [self \in ClientSet |-> <<>>]
        /\ response = [self \in ClientSet |-> <<>>]
        /\ hasLock = [self \in ClientSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in ServerSet -> "serverLoop"
                                        [] self \in ClientSet -> "acquireLock"]

serverLoop(self) == /\ pc[self] = "serverLoop"
                    /\ Len(queues[self]) > 0 
                    /\ msg' = [msg EXCEPT ![self] = Head(queues[self])]
                    /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                    /\ IF (msg'[self].type = "lock")
                          THEN /\ IF (q[self] = <<>>)
                                     THEN /\ response_message' = [response_message EXCEPT ![self] = "grant"]
                                          /\ PrintT(Append("Granted lock to proc ", ToString(msg'[self].from)))
                                          /\ pc' = [pc EXCEPT ![self] = "respondLock"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "addToQ"]
                                          /\ UNCHANGED response_message
                               /\ q' = q
                          ELSE /\ IF (msg'[self].type = "unlock")
                                     THEN /\ q' = [q EXCEPT ![self] = Tail(q[self])]
                                          /\ PrintT(Append("Granted unlock to proc ", ToString(msg'[self].from)))
                                          /\ IF (q'[self] # <<>>)
                                                THEN /\ response_message' = [response_message EXCEPT ![self] = "grant"]
                                                     /\ pc' = [pc EXCEPT ![self] = "respond_Unlock"]
                                                ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                                     /\ UNCHANGED response_message
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                                          /\ UNCHANGED << q, response_message >>
                    /\ UNCHANGED << request, response, hasLock >>

addToQ(self) == /\ pc[self] = "addToQ"
                /\ q' = [q EXCEPT ![self] = Append(q[self], (msg[self]).from)]
                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                /\ UNCHANGED << queues, msg, response_message, request, 
                                response, hasLock >>

respondLock(self) == /\ pc[self] = "respondLock"
                     /\ \/ /\ queues' = [queues EXCEPT ![msg[self].from] =  Append(queues[msg[self].from], response_message[self])]
                        \/ /\ TRUE
                           /\ UNCHANGED queues
                     /\ pc' = [pc EXCEPT ![self] = "addToQ"]
                     /\ UNCHANGED << msg, q, response_message, request, 
                                     response, hasLock >>

respond_Unlock(self) == /\ pc[self] = "respond_Unlock"
                        /\ \/ /\ queues' = [queues EXCEPT ![Head(q[self])] =  Append(queues[Head(q[self])], response_message[self])]
                           \/ /\ TRUE
                              /\ UNCHANGED queues
                        /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                        /\ UNCHANGED << msg, q, response_message, request, 
                                        response, hasLock >>

Server(self) == serverLoop(self) \/ addToQ(self) \/ respondLock(self)
                   \/ respond_Unlock(self)

acquireLock(self) == /\ pc[self] = "acquireLock"
                     /\ request' = [request EXCEPT ![self] = [from |-> self, type |-> "lock"]]
                     /\ \/ /\ queues' = [queues EXCEPT ![0] =  Append(queues[0], request'[self])]
                        \/ /\ TRUE
                           /\ UNCHANGED queues
                     /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                     /\ UNCHANGED << msg, q, response_message, response, 
                                     hasLock >>

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ Len(queues[self]) > 0 
                         /\ response' = [response EXCEPT ![self] = Head(queues[self])]
                         /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                         /\ Assert((response'[self] = "grant"), 
                                   "Failure of assertion at line 53, column 5.")
                         /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "unlock"]
                         /\ UNCHANGED << msg, q, response_message, request >>

unlock(self) == /\ pc[self] = "unlock"
                /\ request' = [request EXCEPT ![self] = [from |-> self, type |-> "unlock"]]
                /\ \/ /\ queues' = [queues EXCEPT ![0] =  Append(queues[0], request'[self])]
                   \/ /\ TRUE
                      /\ UNCHANGED queues
                /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << msg, q, response_message, response >>

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
