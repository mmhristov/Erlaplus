-------------------- MODULE Test_Functions ------------------------
EXTENDS Integers, TLC

(* --algorithm test_functions 
    variables 
        A = {1,2,3,{4 .. 8}};
        F = [ Name |-> "Gabriel" , Age |-> 23];
        B = [c \in {1,2,3}, n \in {1, 2, 3, 4, 5, 6} |-> c * n];
        D = << <<1,2,3>>,<<2,5,4>>, <<4,3,7>> >>;
        
        
    begin 
        
        print B[1,3];
        print D[1,3]
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d1b9faca" /\ chksum(tla) = "95354b0b")
VARIABLES A, F, B, D, pc

vars == << A, F, B, D, pc >>

Init == (* Global variables *)
        /\ A = {1,2,3,{4 .. 8}}
        /\ F = [ Name |-> "Gabriel" , Age |-> 23]
        /\ B = [c \in {1,2,3}, n \in {1, 2, 3, 4, 5, 6} |-> c * n]
        /\ D = << <<1,2,3>>,<<2,5,4>>, <<4,3,7>> >>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(B[1,3])
         /\ PrintT(D[1,3])
         /\ pc' = "Done"
         /\ UNCHANGED << A, F, B, D >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
