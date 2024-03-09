---- MODULE Test_FailAndMaybeFail ----
(*--algorithm Test_FailAndMaybeFail

    fair process fail1 = 1
    begin
        label1:
            fail();
    end process;

    fair process maybeFail1 = 2
    begin
        label1:
            maybeFail();
    end process;

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ff30f80f" /\ chksum(tla) = "ae59e487")
\* Label label1 of process fail1 at line 7 col 19 changed to label1_
VARIABLE pc

vars == << pc >>

ProcSet == {1} \cup {2}

Init == /\ pc = [self \in ProcSet |-> CASE self = 1 -> "label1_"
                                        [] self = 2 -> "label1"]

label1_ == /\ pc[1] = "label1_"
           /\ FALSE
           /\ pc' = [pc EXCEPT ![1] = "Done"]

fail1 == label1_

label1 == /\ pc[2] = "label1"
          /\ \/ /\ FALSE
             \/ /\ TRUE
          /\ pc' = [pc EXCEPT ![2] = "Done"]

maybeFail1 == label1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == fail1 \/ maybeFail1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(fail1)
        /\ WF_vars(maybeFail1)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
