-------------------- MODULE Test_LabeledIf ------------------------
EXTENDS Integers, TLC

(* --algorithm test_labeledIf 
    variables 
        A = 5, IsPositive = FALSE;
        
    begin
        label3:
        if A > 0
        then
        label:
            A := 10;
            IsPositive := TRUE;
        else
            A := -10;
        end if;
        label5:
        A := 39;
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "293f3a17" /\ chksum(tla) = "35435652")
VARIABLES A, IsPositive, pc

vars == << A, IsPositive, pc >>

Init == (* Global variables *)
        /\ A = 5
        /\ IsPositive = FALSE
        /\ pc = "label3"

label3 == /\ pc = "label3"
          /\ IF A > 0
                THEN /\ pc' = "label"
                     /\ A' = A
                ELSE /\ A' = -10
                     /\ pc' = "label5"
          /\ UNCHANGED IsPositive

label == /\ pc = "label"
         /\ A' = 10
         /\ IsPositive' = TRUE
         /\ pc' = "label5"

label5 == /\ pc = "label5"
          /\ A' = 39
          /\ pc' = "Done"
          /\ UNCHANGED IsPositive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == label3 \/ label \/ label5
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
