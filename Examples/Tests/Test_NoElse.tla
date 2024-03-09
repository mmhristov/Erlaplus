-------------------- MODULE Test_If ------------------------
EXTENDS Integers, TLC

(* --algorithm test_if 
    variables 
        A = 5, IsPositive = FALSE;
        
    begin
        if A > 0
        then
            A := 10;
            IsPositive := TRUE;
        elsif A < 0
        then
            A := -10
        end if;
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "75269bc7" /\ chksum(tla) = "a527e372")
VARIABLES A, IsPositive, pc

vars == << A, IsPositive, pc >>

Init == (* Global variables *)
        /\ A = 5
        /\ IsPositive = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF A > 0
               THEN /\ A' = 10
                    /\ IsPositive' = TRUE
               ELSE /\ IF A < 0
                          THEN /\ A' = -10
                          ELSE /\ TRUE
                               /\ A' = A
                    /\ UNCHANGED IsPositive
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
