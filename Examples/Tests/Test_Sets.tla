---- MODULE Test_Sets ----
(*--algorithm Test_Sets

    fair process union = 1
    variables
        A = {1 .. 10};
        B = {2, 3, 4, {5..10}, 7};
        C = {9, 11, 13};
        E = {};
        D = {{1, 2, 3}, {2, 3, 4, 5}};
        F = { A, {3 .. 5}, 3+4 , {1,2,3}};
        begin
        lbl1:
            if (B \in A)
            then
               print 1
            else
                print 0
            end if;

            print (UNION {A, C});
            print (UNION D);
            print (SUBSET C);
        end process;

        fair process filter = 2
        variables
            Xs = {1,2,3,4,5,6,7,8,9};
        begin
        lbl1:
            print {x \in Xs : x > 4 \/ x = 1};
            print Cardinality({y \in {10, 11, 12, 13, 14, 16, 17} : y % 2 = 0});
        end process;
end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e3cecfbe" /\ chksum(tla) = "d661c1d7")
\* Label lbl1 of process union at line 14 col 13 changed to lbl1_
VARIABLES pc, A, B, C, E, D, F, Xs

vars == << pc, A, B, C, E, D, F, Xs >>

ProcSet == {1} \cup {2}

Init == (* Process union *)
        /\ A = {1 .. 10}
        /\ B = {2, 3, 4, {5..10}, 7}
        /\ C = {9, 11, 13}
        /\ E = {}
        /\ D = {{1, 2, 3}, {2, 3, 4, 5}}
        /\ F = { A, {3 .. 5}, 3+4 , {1,2,3}}
        (* Process filter *)
        /\ Xs = {1,2,3,4,5,6,7,8,9}
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "lbl1_"
                                        [] self = 2 -> "lbl1"]

lbl1_ == /\ pc[1] = "lbl1_"
         /\ IF (B \in A)
               THEN /\ PrintT(1)
               ELSE /\ PrintT(0)
         /\ PrintT((UNION {A, C}))
         /\ PrintT((UNION D))
         /\ PrintT((SUBSET C))
         /\ pc' = [pc EXCEPT ![1] = "Done"]
         /\ UNCHANGED << A, B, C, E, D, F, Xs >>

union == lbl1_

lbl1 == /\ pc[2] = "lbl1"
        /\ PrintT({x \in Xs : x > 4 \/ x = 1})
        /\ PrintT(Cardinality({y \in {10, 11, 12, 13, 14, 16, 17} : y % 2 = 0}))
        /\ pc' = [pc EXCEPT ![2] = "Done"]
        /\ UNCHANGED << A, B, C, E, D, F, Xs >>

filter == lbl1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == union \/ filter
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(union)
        /\ WF_vars(filter)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
