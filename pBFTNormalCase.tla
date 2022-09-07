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
    reqPool,
    executed

(* Assumption : the primary is honest *)


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
          /\ reqPool \in SUBSET(Requests)
          /\ executed \in [Replicas -> Seq(Requests)]



Init ==  \* The initial predicate.
  /\ rState  = [rep \in Replicas |-> 
                 [req \in Requests 
                    |-> [val  |-> "none"]]]
  /\ cState = "done"
  /\ rLog = [rep \in Replicas \cup {Client} |-> {}]
  /\ nSeq = 0
  /\ reqPool = Requests
  /\ executed = [rep \in Replicas |-> << >> ]

-----------------------------------------------------------------------------
(*                               protocol actions                           *)
-----------------------------------------------------------------------------

(* 1. prepare and pre-prepare phase *)

Send(m, r) == 
    rLog' = [rLog EXCEPT ![r] = rLog[r] \cup {m}] (* means the message gets delivered and inserted in the addressee's log *)

Broadcast(m) ==
    /\ rLog' = [r \in Replicas \cup {Client} |-> rLog[r] \cup {m}]

(* assumption from the paper: client waits for one request to be executed before sending next request *)

sendRequest(req) ==
    /\ cState = "done" 
    /\ req \in reqPool
    /\ Send([type |-> "request", request |-> req], Primary)
    /\ cState' = "waiting"
    /\ reqPool' = reqPool \ {req}
    /\ UNCHANGED << nSeq, rState, executed >>

prePrepare(req) ==
    /\ req \in Requests
    /\ cState = "waiting"
    /\ [type |-> "request", request |-> req] \in rLog[Primary]
    /\ nSeq' = nSeq + 1
    /\ Broadcast([type |-> "pre-prepare", seq |-> nSeq, request |-> req])
    /\ UNCHANGED << rState, executed, cState, reqPool >>
    
PrepareHonest(rep, req, n) == (* can be performed by a byzantine replica too *)
    /\ Broadcast([type |-> "prepare", replica |-> rep, seq |-> n, request |-> req])
    /\ UNCHANGED << rState, cState, nSeq, executed, reqPool >>

PrepareByzantine(rep, req, n) == (* byzantine only *)
    /\ \A r \in Replicas : 
            \/ \E m \in SeqNums \ {n}:
                Send([type |-> "prepare", replica |-> rep, seq |-> m, request |-> req], r)
            \/ \E req2 \in Requests \ {req}:
                Send([type |-> "prepare", replica |-> rep, seq |-> n, request |-> req2], r)
    /\ UNCHANGED << rState, cState, nSeq, executed, reqPool >>

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
        /\ UNCHANGED << rLog, cState, nSeq, executed, reqPool >>
    \/  /\ r \in Byzantines
        /\ UNCHANGED << rState, cState, rLog, nSeq, executed, reqPool >>

(* 2. commit phase *)

CommitHonest(req, rep, n) ==
    /\ Broadcast([type |-> "commit", replica |-> rep, seq |-> n, request |-> req])
    /\ rState' = [rState EXCEPT ![rep][req].val = "committed-local"]
    /\ UNCHANGED << nSeq, executed, cState, reqPool >>

CommitByzantine(req, rep, n) ==
    \/  /\ \A r \in Replicas : 
                \E req2 \in Requests \ {req}:
                    /\ Send([type |-> "commit", replica |-> rep, seq |-> n, request |-> req2], r)
                    /\ rState' = [rState EXCEPT ![rep][req2].val = "committed-local"]
        /\ UNCHANGED << nSeq, executed, cState, reqPool >>
    \/  /\ \A r \in Replicas : 
                \E m \in SeqNums :
                    /\ Send([type |-> "commit", replica |-> rep, seq |-> m, request |-> req], r)
                    /\ rState' = [rState EXCEPT ![rep][req].val = "committed-local"]
        /\ UNCHANGED << nSeq, executed, cState, reqPool >>
    \/ UNCHANGED << rLog, nSeq, executed, rState, cState, reqPool >> (* do nothing *)

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
    (* /\ rState[i] = "committed-local" *)
    /\ \E senders \in SUBSET(Replicas) : 
        /\ \A sender \in senders : [type |-> "commit", replica |-> sender, seq |-> n, request |-> req] \in rLog[i]  
        /\ Cardinality(senders) = 2*f + 1

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
    /\ executed' = [executed EXCEPT ![i] = Append(executed[i], req)]
    /\ rState' = [rState EXCEPT ![i][req].val = "executed"]
    /\ Send([type |-> "reply", replica |-> i, request |-> req], Client)
    /\ UNCHANGED << nSeq, cState, reqPool >>

executeAndNotifyByzantine(req, i, n) ==
    \/ \E req2 \in Requests \ {req} :
        /\ executed' = [executed EXCEPT ![i] = Append(executed[i], req2)]
        /\ rState' = [rState EXCEPT ![i][req2].val = "executed"]
        /\ Send([type |-> "reply", replica |-> i, request |-> req2], Client)
        /\ UNCHANGED << nSeq, cState, reqPool >>
    \/ UNCHANGED << rLog, nSeq, executed, rState, cState, reqPool >> (* do nothing *)

executeAndNotify(req, i, n) ==
    /\ ~ (rState[i][req].val = "executed")
    /\ readyToExecute(req, i, n)
    /\ \/ executeAndNotifyHonest(req, i, n)
       \/ /\ i \in Byzantines
          /\ executeAndNotifyByzantine(req, i, n)

requestAccepted(req) ==
    /\ cState = "waiting"
    /\ req \in Requests
    /\ \E sset \in SUBSET(Replicas) :
        /\ Cardinality(sset) = f + 1
        /\ \A i \in sset : [type |-> "reply", replica |-> i, request |-> req] \in rLog[Client]
    /\ cState' = "done"
    /\ UNCHANGED << rLog, nSeq, executed, rState, reqPool >>

-----------------------------------------------------------------------------
(*                          faulty behaviour                                *)
-----------------------------------------------------------------------------

(* byzantine faults: define one byzantine behavior where any replica in Byzantines
    can send any message with any content to any replica *)
(* we also need to model benign faults : losing msgs, as a separate func *)

(* 1. benign faults *)

(*
LoseMsg == /\ \E r \in Replicas:
                \E m \in rLog[r]: 
                    rLog' = [rLog EXCEPT ![r] = rLog[r] \ {m}]
           /\ UNCHANGED << rState, nSeq, executed, cState, reqPool  >>
*)

(* 2. byzantine faults *)

(* SendRandomMsg == /\ \E b \in Byzantines:
                        \E req \in Requests, n \in SeqNums, addr \in Replicas:
                            \/ Send([type |-> "pre-prepare", replica |-> b, seq |-> n, request |-> req], addr)
                            \/ Send([type |-> "commit", replica |-> b, seq |-> n, request |-> req], addr)
                 /\ UNCHANGED << rState, nSeq, executed, cState, reqPool  >>
*)
    
(* also byzantine behavior is optional for a bynzatine node in the protocol elements above *)

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

Next == \/ \E req \in Requests : 
            \/ sendRequest(req)
            \/ prePrepare(req)
            \/ \E rep \in Replicas, n \in SeqNums : 
                \/ Prepare(rep, req, n)
                \/ setPrepared(req, rep, n)
                \/ Commit(req, rep, n)
                \/ executeAndNotify(req, rep, n)
            \/ requestAccepted(req)
     (* \/ LoseMsg
        \/ SendRandomMsg  
    *)

vars == << rState, cState, rLog, nSeq, executed, reqPool  >>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

THEOREM Spec => TypeOK

(* helper predicates *)

isPrefixOf(seq1, seq2) ==
    \/ /\ seq1 = << >> /\ seq2 = << >>
    \/ \E r3 \in Requests : Append(seq1, r3) = seq2
    \/ seq1 = seq2

logsAgree(r1, r2) ==
    /\ Len(executed[r1]) - Len(executed[r2]) \in {-1, 0, 1}
    /\ \/ isPrefixOf(executed[r1], executed[r2])
       \/ isPrefixOf(executed[r2], executed[r1])

(* invariants *)

Invariant1 ==
    \E i \in Replicas, req1 \in Requests, n \in SeqNums : prepared(req1, i, n)
    => \A req2 \in Requests, j \in Replicas : 
        req2 # req1 => ~ prepared(req2, j, n)

Invariant2 ==
    \A req \in Requests, n \in SeqNums:
        (\E i \in (Replicas \ Byzantines) : committed_local(req, i, n)) => committed(req, n)

(* safety *)

Consensus ==
    \A r1, r2 \in (Replicas \ Byzantines) : logsAgree(r1, r2)

postCondSendReq(req) ==
    /\ [type |-> "request", request |-> req] \in rLog[Primary]
    /\ cState' = "waiting"
    /\ reqPool' = reqPool \ {req}

preCondPrePrepare(req) ==
    /\ req \in Requests
    /\ cState = "waiting"
    /\ [type |-> "request", request |-> req] \in rLog[Primary]

Debugger ==
    \A req \in Requests: ~ (req \in reqPool) => preCondPrePrepare(req)

=============================================================================