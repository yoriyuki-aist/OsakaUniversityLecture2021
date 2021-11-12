-------------------------------- MODULE wire --------------------------------
EXTENDS Integers

(*--algorithm wire
variables
    people = {"alice", "bob"},
    acc = [p \in people |-> 5],
    
define 
    NoOverdrafts == \A p \in people: acc[p] >= 0
    EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)
end define;
    
process Wire \in 1..2
    variables
        sender = "alice",
        receiver = "bob",
        amount \in 1..5;
begin   
        CheckFundsAndWithdraw:
            if amount <= acc[sender] then
                acc[sender] := acc[sender] - amount;
            end if;
        Deposit:
                acc[receiver] := acc[receiver] + amount;
end process;            
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ae011abf" /\ chksum(tla) = "ca06606e")
VARIABLES people, acc, pc

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0
EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)

VARIABLES sender, receiver, amount

vars == << people, acc, pc, sender, receiver, amount >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        (* Process Wire *)
        /\ sender = [self \in 1..2 |-> "alice"]
        /\ receiver = [self \in 1..2 |-> "bob"]
        /\ amount \in [1..2 -> 1..5]
        /\ pc = [self \in ProcSet |-> "CheckFundsAndWithdraw"]

CheckFundsAndWithdraw(self) == /\ pc[self] = "CheckFundsAndWithdraw"
                               /\ IF amount[self] <= acc[sender[self]]
                                     THEN /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] - amount[self]]
                                     ELSE /\ TRUE
                                          /\ acc' = acc
                               /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                               /\ UNCHANGED << people, sender, receiver, 
                                               amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acc' = [acc EXCEPT ![receiver[self]] = acc[receiver[self]] + amount[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << people, sender, receiver, amount >>

Wire(self) == CheckFundsAndWithdraw(self) \/ Deposit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Nov 10 20:33:00 JST 2021 by yoriyuki
\* Created Mon Nov 08 16:55:58 JST 2021 by yoriyuki
