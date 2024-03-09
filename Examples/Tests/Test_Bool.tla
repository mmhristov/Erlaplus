-------------------- MODULE Test_Bool ------------------------
EXTENDS TLC

(* --algorithm test_bool 
    variables 
        A = TRUE;
        B = FALSE;
        C = TRUE;
        D = FALSE;
        
    begin 
        if A /\ B
        then
           print D
        else
           if ~B \/ C
           then
                print 42
           else
                print 43
           end if;  
        end if;
    end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "5736285b" /\ chksum(tla) = "aa77c628")
VARIABLES A, B, C, D, pc

vars == << A, B, C, D, pc >>

Init == (* Global variables *)
        /\ A = TRUE
        /\ B = FALSE
        /\ C = TRUE
        /\ D = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF A /\ B
               THEN /\ PrintT(D)
               ELSE /\ IF ~B \/ C
                          THEN /\ PrintT(42)
                          ELSE /\ PrintT(43)
         /\ pc' = "Done"
         /\ UNCHANGED << A, B, C, D >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
