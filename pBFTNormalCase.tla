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
    nSeq, (* to keep track of the sequence number held by the primary *)
    executed

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
          /\ rState  \in [Replicas -> [Requests -> [val  : {"prepared", "commited-local", "executed", "none"}]]]
          /\ executed \in [Replicas -> Seq(Requests)]



PCInit ==  \* The initial predicate.
  /\ rState  = [rep \in Replicas |-> 
                 [req \in Requests 
                    |-> [val  |-> "none"]]]
  /\ rLog = [rep \in Replicas |-> {}]
  /\ nSeq = 0
  /\ executed = [rep \in Replicas |-> << >> ]

(* actions *)

(* 1. prepare and pre-prepare phase *)

Send(m, r) == 
    rLog' = [rLog EXCEPT ![r] = rLog[r] \cup m] (* means the message gets delivered and inserted in the addressee's log *)

sendRequest(cli, req) ==
    /\ cli \in Clients
    /\ req \in Requests
    /\ Send([type |-> {"request"}, client |-> cli, request |-> req], Primary)
    /\ UNCHANGED << nSeq, rState, executed >>

PrePrepare(rep, req, cli) == (* done by the primary *)
    /\ rep = Primary
    /\ req \in Requests
    /\ cli \in Clients
    /\ [type |-> {"request"}, client |-> cli, request |-> req] \in rLog[rep]
    /\ \A r \in Replicas : Send([type |-> "pre-prepare", seq |-> nSeq, client |-> cli, request |-> req], r)
    /\ nSeq' = nSeq + 1
    /\ UNCHANGED << rState, executed >>

    (* byzantine faults: define one byzantine behavior where any replica in Byzantines
    can send any message with any content to any replica *)
    (* we also need to model benign faults : losing msgs, as a separate func *)
    

PrepareHonest(rep, req, cli, n) == (* can be performed by a byzantine replica too *)
    /\ \A r \in Replicas : Send([type |-> "prepare", replica |-> rep, seq |-> n, client |-> cli, request |-> req], r)
    /\ UNCHANGED << rState, nSeq, executed >>

PrepareByzantine(rep, req, cli, n) == (* byzantine only *)
    /\ \A r \in Replicas : 
            \/ \E m \in Nat \ {n}:
                Send([type |-> "prepare", replica |-> rep, seq |-> m, client |-> cli, request |-> req], r)
            \/ \E req2 \in Requests \ {req}:
                Send([type |-> "prepare", replica |-> rep, seq |-> n, client |-> cli, request |-> req2], r)
    /\ UNCHANGED << rState, nSeq, executed >>

Prepare(rep, req, cli, n) ==
    /\ rep \in Replicas
    /\ req \in Requests
    /\ cli \in Clients
    /\ [type |-> "pre-prepare", seq |-> n, client |-> cli, request |-> req] \in rLog[rep]
    /\ \/ PrepareHonest(rep, req, cli, n)
       \/ (/\ rep \in Byzantines 
           /\ PrepareByzantine(rep, req, cli, n))

prepared(req, cli, r, n) ==
    /\ cli \in Clients
    /\ req \in Requests
    /\ n \in Nat
    /\ r \in Replicas
    /\ [type |-> "pre-prepare", seq |-> n, client |-> cli, request |-> req] \in rLog[rep]
    /\ \E senders \subseteq (Replicas \ {Primary}) : 
        /\ \A sender \in senders : [type |-> "prepare", replica |-> sender, seq |-> n, client |-> cli, request |-> req] \in rLog[r]  
        /\ Cardinality(senders) \geq 2*f

setPrepared(req, cli, r, n) ==
    \/  /\ prepared(req, cli, r, n)
        /\ rState' = [rState EXCEPT ![r][req].val = "prepared"]
        /\ UNCHANGED << rLog, nSeq, executed >>
    \/  /\ r \in Byzantines
        /\ UNCHANGED << rState, rLog, nSeq, executed >>

Invariant1 ==
    \E i \in Replicas, req1 \in Requests, cli1 \in Clients, n \in Nat : prepared(req1, cli1, i, n)
    => \A req2 \in Requests, j \in Replicas, cli2 \in Clients : 
        req2 \= req1 \/ cli1 \= cli2 => ~ prepared(req2, j, n)

    (* can we do this i.e. identify the request msg (and its digest) with the request label? *)

CommitHonest(req, cli, rep, n) ==
    /\ \A r \in Replicas : Send([type |-> "commit", , replica |-> rep, seq |-> n, client |-> cli, request |-> req], r)
    /\ rState' = [rState EXCEPT ![rep][req].val = "committed-local"]
    /\ UNCHANGED << nSeq, executed >>

CommitByzantine(req, cli, rep, n) ==
    \/  /\ \A r \in Replicas : 
                \E req2 \in Requests \ {req}:
                    /\ Send([type |-> "commit", , replica |-> rep, seq |-> n, client |-> cli, request |-> req2], r)
                    /\ rState' = [rState EXCEPT ![rep][req2].val = "committed-local"]
        /\ UNCHANGED << nSeq, executed >>
    \/  /\ \A r \in Replicas : 
                \E m \in Nat \ {m}:
                    /\ Send([type |-> "commit", , replica |-> rep, seq |-> m, client |-> cli, request |-> req], r)
                    /\ rState' = [rState EXCEPT ![rep][req].val = "committed-local"]
        /\ UNCHANGED << nSeq, executed >>
    \/ UNCHANGED << rLog, nSeq, executed, rState >> (* do nothing *)

Commit(req, cli, rep, n) ==
    /\ prepared(req, cli, rep, n)
    /\ \/ CommitHonest(req, cli, rep, n)
       \/ /\ rep \in Byzantines
          /\ CommitByzantine(req, cli, rep, n)

(* committed predicate *)
committed(req, cli, n) ==
    /\ cli \in Clients
    /\ req \in Requests
    /\ n \in Nat
    /\ \E sset \subseteq Replicas \ Byzantines :
        /\ Cardinality(sset) = f + 1
        /\ \A r \in sset : prepared(req, cli, r, n)

(* commited-local predicate *)
committed_local(req, cli, i, n) ==
    /\ cli \in Clients
    /\ req \in Requests
    /\ n \in Nat
    /\ i \in Replicas
    /\ prepared(req, cli, i, n)
    /\ \E senders \subseteq Replicas : 
        /\ \A sender \in senders : [type |-> "commit", replica |-> sender, seq |-> n, client |-> cli, request |-> req] \in rLog[i]  
        /\ Cardinality(senders) = 2*f + 1

Invariant2 ==
    \A req \in Requests, cli \in Clients, n \in Nat:
        (\E i \in (Replicas \ Byzantines) : committed_local(req, cli, i, n)) => committed(req, cli, n)

(* ready to execute predicate *)

(* each replica executes the op after
1. committed-local becomes true
2. it's state reflects the sequential execution of all requests with lower sequence numbers - how to model this?*)

readyToExecute(req, cli, i, n) ==
    /\ cli \in Clients
    /\ req \in Requests
    /\ n \in Nat
    /\ i \in Replicas
    /\ committed_local(req, cli, i, n)
    /\ ~ (\E req2 \in Requests, cli2 \in Clients, m \in Nat :
            /\ m < n 
            /\ [type |-> "pre-prepare", seq |-> m, client |-> cli2, request |-> req2] \in rLog[i]
            /\ rState[i][req2].val # "executed") (* or: all reqs with seq no m < n should have been executed before?*)

executeAndNotifyHonest(req, cli, i, n) ==
    /\ executed' = [executed EXCEPT ![i]. = Append(executed, req)]
    /\ /\ rState' = [rState EXCEPT ![r][req].val = "executed"]
    /\ Send([type |-> {"reply"}, replica |-> i, client |-> cli, request |-> req])
    /\ UNCHANGED << nSeq >>

executeAndNotifyByzantine(req, cli, i, n) ==
    \/ \E req2 \in Requests \ {req} :
        /\ executed' = [executed EXCEPT ![i]. = Append(executed, req2)]
        /\ /\ rState' = [rState EXCEPT ![r][req2].val = "executed"]
        /\ Send([type |-> {"reply"}, replica |-> i, client |-> cli, request |-> req2])
        /\ UNCHANGED << nSeq >>
    \/ UNCHANGED << rLog, nSeq, executed, rState >> (* do nothing *)

executeAndNotify(req, cli, i, n) ==
    /\ readyToExecute(req, cli, i, n)
    /\ \/ executeAndNotifyHonest(req, cli, i, n)
       \/ /\ i \in Byzantines
          /\ executeAndNotifyByzantine(req, cli, i, n)

-----------------------------------------------------------------------------
(*                          faulty behaviour                                *)
-----------------------------------------------------------------------------

(* 1. benign faults *)

LoseMsg == /\ \E r \in Replicas:
                \E m \in rLog[r]: 
                    rLog' = [rLog EXCEPT ![r] = rLog[r] \ {m}]
           /\ UNCHANGED << rState, nSeq, executed  >>

(* 2. byzantine faults *)

SendRandomMsg == /\ \E b \in Byzantines:
                        \E cli \in Clients, req \in Requests, n \in Nat, addr \in Replicas:
                            \/ Send([type |-> "pre-prepare", replica |-> b, seq |-> n, client |-> cli, request |-> req], addr)
                            \/ Send([type |-> "commit", replica |-> b, seq |-> n, client |-> cli, request |-> req], addr)
                 /\ UNCHANGED << rState, nSeq, executed, rLog  >>
    
(* also byzantine behavior is optional for a bynzatine node in the protocol elements above *)

-----------------------------------------------------------------------------
(*                          transitions                               *)
-----------------------------------------------------------------------------

Next == \/ \E cli \in Clients, req \in Requests : 
            \/ sendRequest(cli, req)
            \/ PrePrepare(Primary, req, cli)
            \/ \E rep \in Replicas, n \in Nat : 
                \/ Prepare(rep, req, cli, n)
                \/ setPrepared(req, cli, r, n)
                \/ Commit(req, cli, rep, n)
                \/ executeAndNotify(req, cli, rep, n)
        \/ LoseMsg
        \/ SendRandomMsg  

vars == << rState, rLog, nSeq, executed  >>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

THEOREM Spec => TypeOK

(* invariants *)
(* safety *)