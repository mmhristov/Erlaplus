---- MODULE Test_String ----
EXTENDS Sequences, TLC
(*--algorithm test_String
    variables
        first = "bob";
        last = "marley";
        name = "";

begin
    name := first \o last;
    print Len(first);
    print Append(Head(first), last);
    print SubSeq(name, 2, 7);
    print ("My name is" \o first)
\*    print Seq(first);
\*    todo: test SelectSeq(string/sequence, boolean function)
end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "dc664d19" /\ chksum(tla) = "ae87ba5b")
VARIABLES first, last, name, pc

vars == << first, last, name, pc >>

Init == (* Global variables *)
        /\ first = "bob"
        /\ last = "marley"
        /\ name = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ name' = first \o last
         /\ PrintT(Len(first))
         /\ PrintT(Append(Head(first), last))
         /\ PrintT(SubSeq(name', 2, 7))
         /\ PrintT(Seq(first))
         /\ pc' = "Done"
         /\ UNCHANGED << first, last >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
