-------------------- MODULE Test_If ------------------------
EXTENDS Integers, TLC

(* --algorithm test_if 
    variables 
        A = 5, IsPositive = FALSE, IsZero = FALSE;
        
    begin
        if A > 0
        then
            A := 10;
            IsPositive := TRUE;
        elsif A < 0
        then
            A := -10
        else
            A := 0;
            IsPositive := TRUE;
            IsZero := TRUE
        end if;
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "6d2fa53b" /\ chksum(tla) = "e6cc765f")
VARIABLES A, IsPositive, IsZero, pc

vars == << A, IsPositive, IsZero, pc >>

Init == (* Global variables *)
        /\ A = 5
        /\ IsPositive = FALSE
        /\ IsZero = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF A > 0
               THEN /\ A' = 10
                    /\ IsPositive' = TRUE
                    /\ UNCHANGED IsZero
               ELSE /\ IF A < 0
                          THEN /\ A' = -10
                               /\ UNCHANGED << IsPositive, IsZero >>
                          ELSE /\ A' = 0
                               /\ IsPositive' = TRUE
                               /\ IsZero' = TRUE
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
