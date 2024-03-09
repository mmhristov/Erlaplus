-------------------- MODULE Test_Comm ------------------------
EXTENDS Integers, TLC

(* --algorithm test_comm 
    variables 
        A = 5;
        B = 6;
        
    begin 
        if A <= 5
        then
           print A + B ^ 2
        else 
            print B ^ 2 + A
        end if;
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f263a893" /\ chksum(tla) = "18d651ef")
VARIABLES A, B, pc

vars == << A, B, pc >>

Init == (* Global variables *)
        /\ A = 5
        /\ B = 6
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF A <= 5
               THEN /\ PrintT(A + B ^ 2)
               ELSE /\ PrintT(B ^ 2 + A)
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
