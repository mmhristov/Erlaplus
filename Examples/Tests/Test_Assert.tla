------------------------ MODULE Test_Assert ----------------------------
EXTENDS Naturals, TLC

(*--algorithm test_Assert
variables balance = 42;

begin
    assert balance >= 0;
    assert balance <= 50;
end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a628f8ec" /\ chksum(tla) = "20087494")
VARIABLES balance, pc

vars == << balance, pc >>

Init == (* Global variables *)
        /\ balance = 42
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(balance >= 0, "Failure of assertion at line 8, column 5.")
         /\ Assert(balance <= 50, 
                   "Failure of assertion at line 9, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED balance

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
========================================================================
