---- MODULE Test_With ----

EXTENDS TLC, Naturals

(*--algorithm Test_With

    fair process withTest1 = 1
    variables
        z = 1;
    begin
    withLbl:
        with x = 10; y = 45 do
            print x + y + z;
        end with;

        with X = 15 do
            print x;
        end with;
    end process;

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1820e2d4" /\ chksum(tla) = "662d0236")
VARIABLES pc, z

vars == << pc, z >>

ProcSet == {1}

Init == (* Process withTest1 *)
        /\ z = 1
        /\ pc = [self \in ProcSet |-> "withLbl"]

withLbl == /\ pc[1] = "withLbl"
           /\ LET x == 10 IN
                LET y == 45 IN
                  PrintT(x + y + z)
           /\ LET X == 15 IN
                PrintT(x)
           /\ pc' = [pc EXCEPT ![1] = "Done"]
           /\ z' = z

withTest1 == withLbl

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == withTest1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(withTest1)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
