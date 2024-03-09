---------------------------- MODULE Test_Multiprocess ----------------------------
EXTENDS
    TLC, Integers

(* --algorithm test_multiprocess
    fair process p1 = 1
        variables
            A = 0;
    begin
    label:
        while A < 1 do
            A := 1;
        end while;
    end process;

    fair process p2 = 2
    variables
        A = 0;
    begin
    label:
         while A < 2 do
            A := 2;
         end while;
    end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "667205e4" /\ chksum(tla) = "72031917")
\* Label label of process p1 at line 11 col 9 changed to label_
\* Process variable A of process p1 at line 8 col 13 changed to A_
VARIABLES pc, A_, A

vars == << pc, A_, A >>

ProcSet == {1} \cup {2}

Init == (* Process p1 *)
        /\ A_ = 0
        (* Process p2 *)
        /\ A = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "label_"
                                        [] self = 2 -> "label"]

label_ == /\ pc[1] = "label_"
          /\ IF A_ < 1
                THEN /\ A_' = 1
                     /\ pc' = [pc EXCEPT ![1] = "label_"]
                ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                     /\ A_' = A_
          /\ A' = A

p1 == label_

label == /\ pc[2] = "label"
         /\ IF A < 2
               THEN /\ A' = 2
                    /\ pc' = [pc EXCEPT ![2] = "label"]
               ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
                    /\ A' = A
         /\ A_' = A_

p2 == label

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == p1 \/ p2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(p1)
        /\ WF_vars(p2)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
========================
