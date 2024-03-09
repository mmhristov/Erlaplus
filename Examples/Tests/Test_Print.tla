---------------------------- MODULE Test_Print ----------------------------
EXTENDS
    TLC

(* --algorithm test_print
    variables
        Counter = 0;
    begin
        Counter := 1;
        print Counter;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "336be1b2" /\ chksum(tla) = "d022cf87")
VARIABLES Counter, pc

vars == << Counter, pc >>

Init == (* Global variables *)
        /\ Counter = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Counter' = 1
         /\ PrintT(Counter')
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
