------------------------ MODULE Test_Broadcast ------------------------
EXTENDS Integers, Sequences, TLC

\* The number of servers and clients in the model checking setup
CONSTANTS NUM_SERVERS, NUM_CLIENTS

ASSUME NUM_SERVERS > 0 /\ NUM_CLIENTS > 0

(*
--algorithm Test_Broadcast

variables
    queues = [id \in 1 .. NUM_NODES |-> <<>>];
    define
        NUM_NODES == NUM_CLIENTS + NUM_SERVERS
    end define;

\*    macro Broadcast(message)
\*    begin
\*         queues := [i \in DOMAIN queues |-> Append(queues[i], message)];
\*    end macro;
\*
\*    macro Send(message, proc)
\*    begin
\*        either
\*            queues[proc] := Append(queues[proc], message)
\*         or
\*            skip;
\*        end either;
\*    end macro;
\*
\*    macro Receive(message)
\*    begin
\*        await queues[self] # <<>>;
\*        message := Head(queues[self]);
\*        queues[self] := Tail(queues[self]);
\*    end macro;

    fair process Server \in (1 .. NUM_SERVERS)
    variable current_message = <<>>, a = 1, b = 2;
    begin
        label1:
        while (TRUE) do
            receive(current_message);
            handleMsgs:
                if (current_message.type = "type1") then
                    (* Handle type1 *)
                    print "Received type1";
                elsif (current_message.type = "greetMe") then
                    (* Handle greetMe *)
                    print "Received greetMe";
                    send(Append("hi, ", current_message.name), current_message.sender);
                elsif (current_message.type = "type3") then
                    (* Handle type3 *)
                    print "Received type3";
                end if;
        end while;

    end process;


    fair process Client \in (NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS))
    variable message_1 = <<>>, message_2 = <<>>, response_message = <<>>;
    begin
        create_Messages:
            message_1 := [type |-> "type1", value |-> 500, receiver |-> 2];
        send1:
            broadcast(message_1);
        receive:
            receive(response_message);
        print_res:
            print response_message;
    end process;
 end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "bccc7f69" /\ chksum(tla) = "e5e88879")
VARIABLES queues, pc

(* define statement *)
NUM_NODES == NUM_CLIENTS + NUM_SERVERS

VARIABLES current_message, a, b, message_1, message_2, response_message

vars == << queues, pc, current_message, a, b, message_1, message_2, 
           response_message >>

ProcSet == ((1 .. NUM_SERVERS)) \cup ((NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS)))

Init == (* Global variables *)
        /\ queues = [id \in 1 .. NUM_NODES |-> <<>>]
        (* Process Server *)
        /\ current_message = [self \in (1 .. NUM_SERVERS) |-> <<>>]
        /\ a = [self \in (1 .. NUM_SERVERS) |-> 1]
        /\ b = [self \in (1 .. NUM_SERVERS) |-> 2]
        (* Process Client *)
        /\ message_1 = [self \in (NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS)) |-> <<>>]
        /\ message_2 = [self \in (NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS)) |-> <<>>]
        /\ response_message = [self \in (NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS)) |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in (1 .. NUM_SERVERS) -> "label1"
                                        [] self \in (NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS)) -> "create_Messages"]

label1(self) == /\ pc[self] = "label1"
                /\ Len(queues[self]) > 0 
                /\ current_message' = [current_message EXCEPT ![self] = Head(queues[self])]
                /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                /\ pc' = [pc EXCEPT ![self] = "send"]
                /\ UNCHANGED << a, b, message_1, message_2, response_message >>

send(self) == /\ pc[self] = "send"
              /\ IF (current_message[self].type = "type1")
                    THEN /\ PrintT("Received type1")
                         /\ UNCHANGED << queues, a, b >>
                    ELSE /\ IF (current_message[self].type = "greetMe")
                               THEN /\ a' = [a EXCEPT ![self] = 10]
                                    /\ b' = [b EXCEPT ![self] = 20]
                                    /\ PrintT("Received type2")
                                    /\ \/ /\ queues' = [queues EXCEPT ![current_message[self].sender] =  Append(queues[current_message[self].sender], Append("hi, ", current_message[self].name))]
                                       \/ /\ TRUE
                                          /\ UNCHANGED queues
                               ELSE /\ IF (current_message[self].type = "type3")
                                          THEN /\ PrintT("Received type3")
                                          ELSE /\ TRUE
                                    /\ UNCHANGED << queues, a, b >>
              /\ pc' = [pc EXCEPT ![self] = "label1"]
              /\ UNCHANGED << current_message, message_1, message_2, 
                              response_message >>

Server(self) == label1(self) \/ send(self)

create_Messages(self) == /\ pc[self] = "create_Messages"
                         /\ message_1' = [message_1 EXCEPT ![self] = [type |-> "type1", value |-> 500, receiver |-> 2]]
                         /\ message_2' = [message_2 EXCEPT ![self] = [type |-> "greetMe", name |-> "Tarzan", sender |-> self]]
                         /\ pc' = [pc EXCEPT ![self] = "send1"]
                         /\ UNCHANGED << queues, current_message, a, b, 
                                         response_message >>

send1(self) == /\ pc[self] = "send1"
               /\ \/ /\ queues' = [i\inDOMAINqueues|->Append(queues[i],message_1[self])]
                  \/ /\ TRUE
                     /\ UNCHANGED queues
               /\ pc' = [pc EXCEPT ![self] = "receive"]
               /\ UNCHANGED << current_message, a, b, message_1, message_2, 
                               response_message >>

receive(self) == /\ pc[self] = "receive"
                 /\ Len(queues[self]) > 0 
                 /\ response_message' = [response_message EXCEPT ![self] = Head(queues[self])]
                 /\ queues' = [queues EXCEPT ![self] =  Tail(queues[self]) ]
                 /\ pc' = [pc EXCEPT ![self] = "print_res"]
                 /\ UNCHANGED << current_message, a, b, message_1, message_2 >>

print_res(self) == /\ pc[self] = "print_res"
                   /\ PrintT(response_message[self])
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << queues, current_message, a, b, message_1, 
                                   message_2, response_message >>

Client(self) == create_Messages(self) \/ send1(self) \/ receive(self)
                   \/ print_res(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in (1 .. NUM_SERVERS): Server(self))
           \/ (\E self \in (NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS)): Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in (1 .. NUM_SERVERS) : WF_vars(Server(self))
        /\ \A self \in (NUM_SERVERS + 1 .. (NUM_SERVERS + NUM_CLIENTS)) : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
