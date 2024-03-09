    ---- MODULE Test_Records ----
EXTENDS
    Sequences, TLC
(*--algorithm Test_Records

    fair process test_1 = 1
    variables
        Picard = <<>>;
        Troi = <<>>;
        PicardClone = <<>>;
        Average_Age = 0;
    begin
    lbl1:
        Picard := [name |-> "Jean-Luc Picard", email |-> "picard@ufp.com", address |-> "USS Enterprise", age |-> 59];
        Troi := [name |-> "Deanna Troi", email |-> "troi@ufp.com", address |-> "USS Enterprise", age |-> 28];
        Average_Age := (Picard.age + Troi.age) \div 2;
        print Average_Age;

        PicardClone := [name |-> "Jean-Luc Picard", email |-> "picard2@ufp.com", address |-> "USS Enterprise", age |-> Picard.age];
        print Picard.age = PicardClone.age;
    end process;

    fair process squareBracketTest = 2
     variables
            map1 = [j \in {1,2,3} |-> 0];
            map2 = <<>>;
            a = 0;
        begin
        lbl2:
            map1[1] := 100;
            lbl3:
            map1[3] := 300;
            a := map1[1] + map1[2 + 1];
            print a;
            print map1;

            map2 := [key1 |-> 1, key2 |-> 2, key3 |-> [x |-> [y |-> 66]]];
            lblmap2:
            map2[key3][x][y] := 77;
            print map2;

    \*      Expected output:
    \*         400
    \*        #{1=>100,2=>0,3=>300}
    \*        #{key_key1=>1,key_key2=>2,key_key3=>#{key_x=>#{key_y=>77}}}
        end process;

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3ac88354" /\ chksum(tla) = "4b2cefb1")
VARIABLES pc, Picard, Troi, PicardClone, Average_Age, map1, map2, a

vars == << pc, Picard, Troi, PicardClone, Average_Age, map1, map2, a >>

ProcSet == {1} \cup {2}

Init == (* Process test_1 *)
        /\ Picard = <<>>
        /\ Troi = <<>>
        /\ PicardClone = <<>>
        /\ Average_Age = 0
        (* Process squareBracketTest *)
        /\ map1 = [j \in {1,2,3} |-> 0]
        /\ map2 = <<>>
        /\ a = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "lbl1"
                                        [] self = 2 -> "lbl2"]

lbl1 == /\ pc[1] = "lbl1"
        /\ Picard' = [name |-> "Jean-Luc Picard", email |-> "picard@ufp.com", address |-> "USS Enterprise", age |-> 59]
        /\ Troi' = [name |-> "Deanna Troi", email |-> "troi@ufp.com", address |-> "USS Enterprise", age |-> 28]
        /\ Average_Age' = ((Picard'.age + Troi'.age) \div 2)
        /\ PrintT(Average_Age')
        /\ PicardClone' = [name |-> "Jean-Luc Picard", email |-> "picard2@ufp.com", address |-> "USS Enterprise", age |-> Picard'.age]
        /\ PrintT(Picard'.age = PicardClone'.age)
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << map1, map2, a >>

test_1 == lbl1

lbl2 == /\ pc[2] = "lbl2"
        /\ map1' = [map1 EXCEPT ![1] = 100]
        /\ pc' = [pc EXCEPT ![2] = "lbl3"]
        /\ UNCHANGED << Picard, Troi, PicardClone, Average_Age, map2, a >>

lbl3 == /\ pc[2] = "lbl3"
        /\ map1' = [map1 EXCEPT ![3] = 300]
        /\ a' = map1'[1] + map1'[2 + 1]
        /\ PrintT(a')
        /\ PrintT(map1')
        /\ map2' = [key1 |-> 1, key2 |-> 2, key3 |-> [x |-> [y |-> 66]]]
        /\ pc' = [pc EXCEPT ![2] = "lblmap2"]
        /\ UNCHANGED << Picard, Troi, PicardClone, Average_Age >>

lblmap2 == /\ pc[2] = "lblmap2"
           /\ map2' = [map2 EXCEPT ![key3][x][y] = 77]
           /\ PrintT(map2')
           /\ pc' = [pc EXCEPT ![2] = "Done"]
           /\ UNCHANGED << Picard, Troi, PicardClone, Average_Age, map1, a >>

squareBracketTest == lbl2 \/ lbl3 \/ lblmap2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == test_1 \/ squareBracketTest
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(test_1)
        /\ WF_vars(squareBracketTest)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
