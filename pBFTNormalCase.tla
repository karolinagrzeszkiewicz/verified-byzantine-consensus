----------------------------- MODULE pBFTNormalCase ----------------------------

EXTENDS Integers, Sequences, FiniteSets, Naturals

CONSTANT Replicas,
         Primary,
         Byzantines,
         Client,
         Requests,
         f, (* no. of faulty replicas *)
         SeqNums

ASSUME
    /\ Primary \in Replicas
    /\ Byzantines \subseteq Replicas
    /\ f \in Nat
    /\ Cardinality(Byzantines) \leq f
    /\ Cardinality(Replicas) = 3*f + 1
    /\ ~ (Primary \in Byzantines)

VARIABLES 
    rState,
    cState,
    rLog,
    nSeq, (* to keep track of the sequence number held by the primary *)
    executed

(* assume the primary is honest? *)


Messages ==
    [type : {"request"}, request : Requests] (* to primary *)
    \cup
    [type: {"reply"}, replica : Replicas, request : Requests] (* to client *)
    \cup
    [type : {"pre-prepare"}, seq : Nat, request : Requests] (* we copy the field from the request msg instead of including the whole msg*)
    \cup 
    [type : {"prepare"}, replica : Replicas, seq : Nat, request : Requests] (* from replica *)
    \cup
    [type : {"commit"}, replica : Replicas, seq : Nat, request : Requests] (* from replica *)


TypeOK == /\ nSeq \in Nat
          /\ rLog \in [Replicas \cup {Client} -> Messages]
          /\ rState  \in [Replicas -> [Requests -> [val  : {"prepared", "commited-local", "executed", "none"}]]]
          /\ cState \in {"waiting", "done"}
          /\ executed \in [Replicas -> Seq(Requests)]



Init ==  \* The initial predicate.
  /\ rState  = [rep \in Replicas |-> 
                 [req \in Requests 
                    |-> [val  |-> "none"]]]
  /\ cState = "done"
  /\ rLog = [rep \in Replicas \cup {Client} |-> {}]
  /\ nSeq = 0
  /\ executed = [rep \in Replicas |-> << >> ]

(* actions *)

(* 1. prepare and pre-prepare phase *)

Send(m, r) == 
    rLog' = [rLog EXCEPT ![r] = rLog[r] \cup {m}] (* means the message gets delivered and inserted in the addressee's log *)

(* assumption from the paper: client waits for one request to be executed before sending next request *)

sendRequest(req) ==
    /\ cState = "done" 
    /\ req \in Requests
    /\ Send([type |-> {"request"}, request |-> req], Primary)
    /\ cState' = "waiting"
    /\ UNCHANGED << nSeq, rState, executed >>

PrePrepare(rep, req) == (* done by the primary *)
    /\ rep = Primary
    /\ req \in Requests
    /\ [type |-> {"request"}, request |-> req] \in rLog[rep]
    /\ \A r \in Replicas : Send([type |-> "pre-prepare", seq |-> nSeq, request |-> req], r)
    /\ nSeq' = nSeq + 1
    /\ UNCHANGED << rState, executed >>

    (* byzantine faults: define one byzantine behavior where any replica in Byzantines
    can send any message with any content to any replica *)
    (* we also need to model benign faults : losing msgs, as a separate func *)
    

PrepareHonest(rep, req, n) == (* can be performed by a byzantine replica too *)
    /\ \A r \in Replicas : Send([type |-> "prepare", replica |-> rep, seq |-> n, request |-> req], r)
    /\ UNCHANGED << rState, cState, nSeq, executed >>

PrepareByzantine(rep, req, n) == (* byzantine only *)
    /\ \A r \in Replicas : 
            \/ \E m \in Nat \ {n}:
                Send([type |-> "prepare", replica |-> rep, seq |-> m, request |-> req], r)
            \/ \E req2 \in Requests \ {req}:
                Send([type |-> "prepare", replica |-> rep, seq |-> n, request |-> req2], r)
    /\ UNCHANGED << rState, cState, nSeq, executed >>

Prepare(rep, req, n) ==
    /\ rep \in Replicas
    /\ req \in Requests
    /\ [type |-> "pre-prepare", seq |-> n, request |-> req] \in rLog[rep]
    /\ \/ PrepareHonest(rep, req, n)
       \/ (/\ rep \in Byzantines 
           /\ PrepareByzantine(rep, req, n))

prepared(req, r, n) ==
    /\ req \in Requests
    /\ n \in Nat
    /\ r \in Replicas
    /\ [type |-> "pre-prepare", seq |-> n, request |-> req] \in rLog[r]
    /\ \E senders \in SUBSET(Replicas \ {Primary}) : 
        /\ \A sender \in senders : [type |-> "prepare", replica |-> sender, seq |-> n, request |-> req] \in rLog[r]  
        /\ Cardinality(senders) \geq 2*f

setPrepared(req, r, n) ==
    \/  /\ prepared(req, r, n)
        /\ rState' = [rState EXCEPT ![r][req].val = "prepared"]
        /\ UNCHANGED << rLog, cState, nSeq, executed >>
    \/  /\ r \in Byzantines
        /\ UNCHANGED << rState, cState, rLog, nSeq, executed >>

Invariant1 ==
    \E i \in Replicas, req1 \in Requests, n \in SeqNums : prepared(req1, i, n)
    => \A req2 \in Requests, j \in Replicas : 
        req2 # req1 => ~ prepared(req2, j, n)

    (* can we do this i.e. identify the request msg (and its digest) with the request label? *)

CommitHonest(req, rep, n) ==
    /\ \A r \in Replicas : Send([type |-> "commit", replica |-> rep, seq |-> n, request |-> req], r)
    /\ rState' = [rState EXCEPT ![rep][req].val = "committed-local"]
    /\ UNCHANGED << nSeq, executed, cState >>

CommitByzantine(req, rep, n) ==
    \/  /\ \A r \in Replicas : 
                \E req2 \in Requests \ {req}:
                    /\ Send([type |-> "commit", replica |-> rep, seq |-> n, request |-> req2], r)
                    /\ rState' = [rState EXCEPT ![rep][req2].val = "committed-local"]
        /\ UNCHANGED << nSeq, executed, cState >>
    \/  /\ \A r \in Replicas : 
                \E m \in SeqNums :
                    /\ Send([type |-> "commit", replica |-> rep, seq |-> m, request |-> req], r)
                    /\ rState' = [rState EXCEPT ![rep][req].val = "committed-local"]
        /\ UNCHANGED << nSeq, executed, cState >>
    \/ UNCHANGED << rLog, nSeq, executed, rState, cState >> (* do nothing *)

Commit(req, rep, n) ==
    /\ prepared(req, rep, n)
    /\ \/ CommitHonest(req, rep, n)
       \/ /\ rep \in Byzantines
          /\ CommitByzantine(req, rep, n)

(* committed predicate *)
committed(req, n) ==
    /\ req \in Requests
    /\ n \in Nat
    /\ \E sset \in SUBSET(Replicas \ Byzantines) :
        /\ Cardinality(sset) = f + 1
        /\ \A r \in sset : prepared(req, r, n)

(* commited-local predicate *)
committed_local(req, i, n) ==
    /\ req \in Requests
    /\ n \in Nat
    /\ i \in Replicas
    /\ prepared(req, i, n)
    /\ \E senders \in SUBSET(Replicas) : 
        /\ \A sender \in senders : [type |-> "commit", replica |-> sender, seq |-> n, request |-> req] \in rLog[i]  
        /\ Cardinality(senders) = 2*f + 1

Invariant2 ==
    \A req \in Requests, n \in SeqNums:
        (\E i \in (Replicas \ Byzantines) : committed_local(req, i, n)) => committed(req, n)

(* ready to execute predicate *)

(* each replica executes the op after
1. committed-local becomes true
2. it's state reflects the sequential execution of all requests with lower sequence numbers - how to model this?*)

readyToExecute(req, i, n) ==
    /\ req \in Requests
    /\ n \in Nat
    /\ i \in Replicas
    /\ committed_local(req, i, n)
    /\ ~ (\E req2 \in Requests, m \in SeqNums :
            /\ m < n 
            /\ [type |-> "pre-prepare", seq |-> m, request |-> req2] \in rLog[i]
            /\ rState[i][req2].val # "executed") (* or: all reqs with seq no m < n should have been executed before?*)

executeAndNotifyHonest(req, i, n) ==
    /\ executed' = [executed EXCEPT ![i] = Append(executed, req)]
    /\ /\ rState' = [rState EXCEPT ![i][req].val = "executed"]
    /\ Send([type |-> {"reply"}, replica |-> i, request |-> req], Client)
    /\ UNCHANGED << nSeq, cState >>

executeAndNotifyByzantine(req, i, n) ==
    \/ \E req2 \in Requests \ {req} :
        /\ executed' = [executed EXCEPT ![i] = Append(executed, req2)]
        /\ rState' = [rState EXCEPT ![i][req2].val = "executed"]
        /\ Send([type |-> {"reply"}, replica |-> i, request |-> req2], Client)
        /\ UNCHANGED << nSeq, cState >>
    \/ UNCHANGED << rLog, nSeq, executed, rState, cState >> (* do nothing *)

executeAndNotify(req, i, n) ==
    /\ readyToExecute(req, i, n)
    /\ \/ executeAndNotifyHonest(req, i, n)
       \/ /\ i \in Byzantines
          /\ executeAndNotifyByzantine(req, i, n)

requestAccepted(req) ==
    /\ cState = "waiting"
    /\ req \in Requests
    /\ \E sset \in SUBSET(Replicas) :
        /\ Cardinality(sset) = f + 1
        /\ \A i \in sset : [type |-> {"reply"}, replica |-> i, request |-> req] \in rLog[Client]
    /\ cState' = "done"
    /\ UNCHANGED << rLog, nSeq, executed, rState >>

-----------------------------------------------------------------------------
(*                          faulty behaviour                                *)
-----------------------------------------------------------------------------

(* 1. benign faults *)

LoseMsg == /\ \E r \in Replicas:
                \E m \in rLog[r]: 
                    rLog' = [rLog EXCEPT ![r] = rLog[r] \ {m}]
           /\ UNCHANGED << rState, nSeq, executed, cState  >>

(* 2. byzantine faults *)

SendRandomMsg == /\ \E b \in Byzantines:
                        \E req \in Requests, n \in SeqNums, addr \in Replicas:
                            \/ Send([type |-> "pre-prepare", replica |-> b, seq |-> n, request |-> req], addr)
                            \/ Send([type |-> "commit", replica |-> b, seq |-> n, request |-> req], addr)
                 /\ UNCHANGED << rState, nSeq, executed, cState  >>
    
(* also byzantine behavior is optional for a bynzatine node in the protocol elements above *)

-----------------------------------------------------------------------------
(*                          transitions                               *)
-----------------------------------------------------------------------------

Next == \/ \E req \in Requests : 
            \/ sendRequest(req)
            \/ PrePrepare(Primary, req)
            \/ \E rep \in Replicas, n \in SeqNums : 
                \/ Prepare(rep, req, n)
                \/ setPrepared(req, rep, n)
                \/ Commit(req, rep, n)
                \/ executeAndNotify(req, rep, n)
            \/ requestAccepted(req)
        \/ LoseMsg
        \/ SendRandomMsg  

vars == << rState, cState, rLog, nSeq, executed  >>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

THEOREM Spec => TypeOK

(* invariants *)

(* safety *)

Consensus ==
    cState = "done" => \A i, j \in (Replicas \ Byzantines) : executed[i] = executed[j]

=============================================================================