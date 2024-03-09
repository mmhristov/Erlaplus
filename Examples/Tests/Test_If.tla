-------------------- MODULE Test_If ------------------------
EXTENDS Integers, TLC

(* --algorithm test_if

    fair process testIf1 = 1
    variables 
        A = 5, IsPositive = FALSE;
    begin
        if A > 0
        then
            A := 10;
            IsPositive := TRUE;
        else
            A := -10
        end if;
    end process;

    fair process testIf2 = 2
    variables
        i = 0;
        j = 0;

        a = 0;
        b = 0;
    begin
    while1:
        while (i <= 10) do
        while2:
            if (i = 5) then
                print "Halfway there";
                (* We expect of the erlang translation that at this point of the code
                    there should be a state assignment to catchup with the else branch's more advanced state number.
                    If successful, then the translation can successfully find the correct line to insert at,
                    even when more code has been generated before the index (e.g. for while functions),
                *)
            else
            lbl2:
                while (j <= 5) do
                    print <<i, j>>;
                    j := j + 1;
                end while;
                a := 10;
                b := 11;
            end if;
            asg:
                j := 0;
                i := i + 1;
            end while;
    end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e7465fce" /\ chksum(tla) = "38288854")
VARIABLES A, IsPositive, pc

vars == << A, IsPositive, pc >>

Init == (* Global variables *)
        /\ A = 5
        /\ IsPositive = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF A > 0
               THEN /\ A' = 10
                    /\ IsPositive' = TRUE
               ELSE /\ A' = -10
                    /\ UNCHANGED IsPositive
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
