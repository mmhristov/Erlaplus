---- MODULE Test_Macros ----
(*--algorithm Test_Macros
    macro CalcVar3(var1, var2)
    begin
        result := var1 + var2;
    end macro;

    macro DoNothing()
    begin
        skip;
    end macro;

    process Server1 = 1
    variable var1 = 0, var2 = 1, var3 = 2, var4 = 3, result = 0;
    begin
    label:
        CalcVar3(var1, var2);
        DoNothing();
        print var3;
    end process;

    process Server2 = 2
    variable v1 = 1, v2 = 2, v3 = 3, result = 0;
        begin
        label:
            CalcVar3(v2, v3);
            print result;
        end process;
end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "29b578bc" /\ chksum(tla) = "2681afd2")
\* Label label of process Server1 at line 5 col 9 changed to label_
\* Process variable result of process Server1 at line 14 col 54 changed to result_
VARIABLES pc, var1, var2, var3, var4, result_, v1, v2, v3, result

vars == << pc, var1, var2, var3, var4, result_, v1, v2, v3, result >>

ProcSet == {1} \cup {2}

Init == (* Process Server1 *)
        /\ var1 = 0
        /\ var2 = 1
        /\ var3 = 2
        /\ var4 = 3
        /\ result_ = 0
        (* Process Server2 *)
        /\ v1 = 1
        /\ v2 = 2
        /\ v3 = 3
        /\ result = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "label_"
                                        [] self = 2 -> "label"]

label_ == /\ pc[1] = "label_"
          /\ result_' = var1 + var2
          /\ TRUE
          /\ PrintT(var3)
          /\ pc' = [pc EXCEPT ![1] = "Done"]
          /\ UNCHANGED << var1, var2, var3, var4, v1, v2, v3, result >>

Server1 == label_

label == /\ pc[2] = "label"
         /\ result' = v2 + v3
         /\ PrintT(result')
         /\ pc' = [pc EXCEPT ![2] = "Done"]
         /\ UNCHANGED << var1, var2, var3, var4, result_, v1, v2, v3 >>

Server2 == label

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Server1 \/ Server2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
