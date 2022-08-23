----------------------------- MODULE pBFTNormalCase ----------------------------

EXTENDS Integers

CONSTANT Replicas,
         Primary,
         Clients,
         Requests,
         f (* no. of faulty replicas *)

ASSUME
    /\ Primary \in Replicas,
    /\ f \in Nat

VARIABLES 
    rState,
    rLog,
    time,
    nSeq (* to keep track of the sequence number held by the primary *)

(* assume the primary is honest? *)


Messages ==
    [type : {"request"}, client : Clients, timestamp: Nat, req: Requests] (* to primary *)
    \cup
    [type: {"reply"}, replica : Replicas, client : Clients, timestamp: Nat, req: Requests] (* to client *)
    \cup
    [type : {"pre-prepare"}, seq : Nat, client : Clients, timestamp: Nat, req: Requests] (* we copy the field from the request msg instead of including the whole msg*)
    \cup 
    [type : {"prepare"}, replica : Replicas, seq : Nat, client : Clients, timestamp: Nat, req: Requests] (* from replica *)
    \cup
    [type : {"commit"}, replica : Replicas, seq : Nat, client : Clients, timestamp: Nat, req: Requests] (* from replica *)


TypeOK == /\ time \in Nat
          /\ nSeq \in Nat
          /\ rLog \in [Replicas -> Messages]
          /\ rState  \in [Replicas -> [Requests -> [val  : {"prepared", "commited-local", "none"}]]]



PCInit ==  \* The initial predicate.
  /\ rState  = [rep \in Replicas |-> 
                 [req \in Requests 
                    |-> [val  |-> "none"]]]
  /\ rLog = [rep \in Replicas |-> {}]
  /\ time = 0
  /\ nSeq = 0

  

