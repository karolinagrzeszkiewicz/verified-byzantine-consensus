----------------------------- MODULE pBFTNormalCase ----------------------------

EXTENDS Integers

CONSTANT Replicas,
         Primary,
         Byzantines,
         Clients,
         Requests,
         f (* no. of faulty replicas *)

ASSUME
    /\ Primary \in Replicas
    /\ Byzantines \subseteq Replicas
    /\ f \in Nat
    /\ Cardinality(Byzantines) \leq f
    /\ Cardinality(Replicas) = 3*f + 1
    /\ ~ (Primary \in Byzantines)

VARIABLES 
    rState,
    rLog,
    nSeq (* to keep track of the sequence number held by the primary *)

(* assume the primary is honest? *)


Messages ==
    [type : {"request"}, client : Clients, request : Requests] (* to primary *)
    \cup
    [type: {"reply"}, replica : Replicas, client : Clients, request : Requests] (* to client *)
    \cup
    [type : {"pre-prepare"}, seq : Nat, client : Clients, request : Requests] (* we copy the field from the request msg instead of including the whole msg*)
    \cup 
    [type : {"prepare"}, replica : Replicas, seq : Nat, client : Clients, request : Requests] (* from replica *)
    \cup
    [type : {"commit"}, replica : Replicas, seq : Nat, client : Clients, request : Requests] (* from replica *)


TypeOK == /\ nSeq \in Nat
          /\ rLog \in [Replicas -> Messages]
          /\ rState  \in [Replicas -> [Requests -> [val  : {"prepared", "commited-local", "none"}]]]



PCInit ==  \* The initial predicate.
  /\ rState  = [rep \in Replicas |-> 
                 [req \in Requests 
                    |-> [val  |-> "none"]]]
  /\ rLog = [rep \in Replicas |-> {}]
  /\ nSeq = 0

(* actions *)

(* 1. prepare and pre-prepare phase *)

Send(m, r) == rLog' = [rLog EXCEPT ![r] = rLog[r] \cup m]

sendRequest(cli, req) ==
    /\ cli \in Clients
    /\ req \in Requests
    /\ Send([type |-> {"request"}, client |-> cli, request |-> req], Primary)
    /\ UNCHANGED << nSeq, rState >>

PrePrepare(rep, req, cli) == (* done by the primary *)
    /\ rep = Primary
    /\ req \in Requests
    /\ cli \in Clients
    /\ [type |-> {"request"}, client |-> cli, request |-> req] \in rLog[rep]
    /\ \A r \in Replicas : Send([type |-> "pre-prepare", seq |-> nSeq, client |-> cli, request |-> req], r)
    /\ nSeq' = nSeq + 1
    /\ UNCHANGED << rState >>

    (* byzantine faults: define one byzantine behavior where any replica in Byzantines
    can send any message with any content to any replica *)
    (* we also need to model benign faults : losing msgs, as a separate func *)
    

PrepareHonest(rep, req, cli, n) == (* can be performed by a byzantine replica too *)
    /\ rep \in Replicas
    /\ req \in Requests
    /\ cli \in Clients
    /\ [type |-> "pre-prepare", seq |-> n, client |-> cli, request |-> req] \in rLog[rep]
    /\ \A r \in Replicas : Send([type |-> "prepare", replica |-> rep, seq |-> n, client |-> cli, request |-> req], r)
    /\ UNCHANGED << rState, nSeq >>

prepared(req, r, n) ==
    /\ \E cli \in Clients : [type |-> "pre-prepare", seq |-> n, client |-> cli, request |-> req] \in rLog[rep]
    /\ \E cli \in Clients, senders \subseteq (Replicas \ {Primary}) : 
        /\ \A sender \in senders : [type |-> "prepare", replica |-> sender, seq |-> n, client |-> cli, request |-> req] \in rLog[r]  
        /\ Cardinality(senders) \geq 2*f

setPrepared(req, r, n) ==
    /\ prepared(req, r, n)
    /\ rState' = [rState EXCEPT ![r][req].val = "prepared"]
    /\ UNCHANGED << rLog, nSeq >>

Invariant1 ==
    \E i \in Replicas, req1 \in Requests, n \in Nat : prepared(req1, i, n)
    => \A req2 \in Requests, j \in Replicas : 
        req2 \= req1 /\ i \= j => ~ prepared(req2, j, n)

    (* can we do this i.e. identify the request msg (and its digest) with the request label? *)


