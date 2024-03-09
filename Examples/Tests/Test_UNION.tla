-------------------- MODULE Test_UNION ------------------------
EXTENDS Integers, TLC

(* --algorithm test_union 
    variables 
        A = {1 .. 10};
        B = {2, {3, 8, 9}, 4, {5,6}, 7}
        
    begin 
        if (B \in A)
        then
           print UNION B
        else 
            print 0
        end if;
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "15139430" /\ chksum(tla) = "413ff5")
VARIABLES A, B, pc

vars == << A, B, pc >>

Init == (* Global variables *)
        /\ A = {1 .. 10}
        /\ B = {2, {3, 8, 9}, 4, {5,6}, 7}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF (B \in A)
               THEN /\ PrintT(UNION B)
               ELSE /\ PrintT(0)
         /\ pc' = "Done"
         /\ UNCHANGED << A, B >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
