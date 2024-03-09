-------------------- MODULE Test_While ------------------------
EXTENDS Integers

(* --algorithm test_While 
    variables 
        A = 5;
        
    begin
        while1:
        while A <= 5 do
            A := A + 1;
            print_A:
            print A;
        end while;

        while2:
        while A <= 10 do
            set_A:
            A := A + 1;
            print_A2:
            print A;
        end while;

        while3:
        while A <= 10 do
            A := A + 1;
        end while;
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cfcbceda" /\ chksum(tla) = "8ae5f8cf")
VARIABLES A, pc

vars == << A, pc >>

Init == (* Global variables *)
        /\ A = 5
        /\ pc = "while1"

while1 == /\ pc = "while1"
          /\ IF A <= 5
                THEN /\ A' = A + 1
                     /\ pc' = "print_A"
                ELSE /\ pc' = "while2"
                     /\ A' = A

print_A == /\ pc = "print_A"
           /\ PrintT(A)
           /\ pc' = "while1"
           /\ A' = A

while2 == /\ pc = "while2"
          /\ IF A <= 10
                THEN /\ pc' = "set_A"
                ELSE /\ pc' = "while3"
          /\ A' = A

set_A == /\ pc = "set_A"
         /\ A' = A + 1
         /\ pc' = "print_A2"

print_A2 == /\ pc = "print_A2"
            /\ PrintT(A)
            /\ pc' = "while2"
            /\ A' = A

while3 == /\ pc = "while3"
          /\ IF A <= 10
                THEN /\ A' = A + 1
                     /\ pc' = "while3"
                ELSE /\ pc' = "Done"
                     /\ A' = A

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == while1 \/ print_A \/ while2 \/ set_A \/ print_A2 \/ while3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
