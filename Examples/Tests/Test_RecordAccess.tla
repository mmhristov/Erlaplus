---- MODULE Test_RecordAccess ----
(*--algorithm Test_RecordAccess

    fair process test1 = 1
    variables
        map = [c |-> 1000, a |-> 0, b |-> [c |-> 100, d |-> 5]];
        var1 = 0;
        var2 = 0;
    begin
    lbl2:
        var1 := (map.b).c;
        var2 := map[b][c];
        print var1;
        print var2;
        print var1 = var2;
        print map[c] + map[b][d];
    end process;

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "aad63fd8" /\ chksum(tla) = "c6c6875a")
VARIABLES pc, map, var1, var2

vars == << pc, map, var1, var2 >>

ProcSet == {1}

Init == (* Process test1 *)
        /\ map = [c |-> 1000, a |-> 0, b |-> [c |-> 100, d |-> 5]]
        /\ var1 = 0
        /\ var2 = 0
        /\ pc = [self \in ProcSet |-> "lbl2"]

lbl2 == /\ pc[1] = "lbl2"
        /\ var1' = (map.b).c
        /\ var2' = map[b][c]
        /\ PrintT(var1')
        /\ PrintT(var2')
        /\ PrintT(var1' = var2')
        /\ PrintT(map[c] + map[b][d])
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ map' = map

test1 == lbl2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == test1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(test1)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
