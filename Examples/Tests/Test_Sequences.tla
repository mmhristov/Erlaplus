---- MODULE Test_Sequences ----
EXTENDS
    Sequences
(*--algorithm Test_Sequences
    fair process p1 = 1
    variables
        List1 = <<>>;
        List2 = <<"a", "bc", 10>>;
        List3 = <<>>;
    begin
    lbl1:
        print <<1 + 1, 2 + 1, 3 + 3>>;
        List1 := Append(Append(List1, "1"), <<3, <<"one", "two", "five">>>>); \* test append function
        print Head(List2);  \* test head function
        print Tail(List2); \* test tail function
        List3 := (List1 \o List2 \o <<"hey", "ho">>); \* test append operator
        print List3;
        print List3[5]; \* test element access
    lbl2:
        List3[2][2][3] := "six"; \* test nested element assignment
        print List3;
        print Len(List3); \* test length function
    end process;
end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b4e68e47" /\ chksum(tla) = "baf0045e")
VARIABLES pc, List1, List2, List3

vars == << pc, List1, List2, List3 >>

ProcSet == {1}

Init == (* Process p1 *)
        /\ List1 = <<>>
        /\ List2 = <<"a", "bc", 10>>
        /\ List3 = <<>>
        /\ pc = [self \in ProcSet |-> "lbl1"]

lbl1 == /\ pc[1] = "lbl1"
        /\ PrintT(<<1 + 1, 2 + 1, 3 + 3>>)
        /\ List1' = Append(Append(List1, "1"), <<3, <<"one", "two", "five">>>>)
        /\ PrintT(Head(List2))
        /\ PrintT(Tail(List2))
        /\ List3' = (List1' \o List2 \o <<"hey", "ho">>)
        /\ PrintT(List3')
        /\ PrintT(List3'[5])
        /\ pc' = [pc EXCEPT ![1] = "lbl2"]
        /\ List2' = List2

lbl2 == /\ pc[1] = "lbl2"
        /\ List3' = [List3 EXCEPT ![2][2][3] = "six"]
        /\ PrintT(List3')
        /\ PrintT(Len(List3'))
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << List1, List2 >>

p1 == lbl1 \/ lbl2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == p1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(p1)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
