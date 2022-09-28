----------------------------- MODULE AccountableConfirmer ----------------------------

(* this is for a single iteration i.e. single consensus *)

EXTENDS Integers, Sequences, FiniteSets, Naturals

(* assumption: no. of byzantines <= t0 *)

CONSTANTS
    replicas,
    values_all

VARIABLES
    is_byzantine,
    predecisions, 
    confirmed,
    from,
    lightCertificate,
    fullCertificate,
    obtainedLightCertificates,
    obtainedFullCertificates,
    rLog, (* temporary storage for submit messages *)
    proof, (* of culpability *)
    rState

values_all_opt == {"none"} \cup values_all

t0 == Cardinality(replicas) \div 3 (* floor division *)

Messages ==
    [type : {"SUBMIT"}, value : values_all, signed : replicas]
    \cup
    [type: {"LIGHT-CERTIFICATE"}, value : values_all, signed : replicas, certificate : values_all \X SUBSET(replicas)] (* values_all not needed here ? *)
    \cup 
    [type: {"FULL-CERTIFICATE"}, value : values_all, signed : replicas, certificate : [type : {"SUBMIT"}, value : values_all, signed : replicas]] 

TypeOK == 
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ predecisions \in [replicas -> values_all \cup {"none"}] (* to store each replica's value *)
    /\ confirmed \in [replicas -> {"true", "false"}]
    /\ from \in [replicas -> replicas] (* to keep track of replicas that submitted the same value: i.e. submit messages for the same value *)
    /\ lightCertificate \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] (* light signature = (v, signatures) *)
    /\ fullCertificate \in [replicas -> SUBSET(Messages)] (* set of SUBMIT messages *)
    /\ obtainedLightCertificates \in [replicas -> SUBSET(Messages)] (* set of LIGHT-CERTIFICATE messages, each contained lightCertificates *)
    /\ obtainedFullCertificates \in [replicas -> SUBSET(Messages)] (* set of FULL-CERTIFICATE messages, each contained fullCertificates *)
    /\ rLog \in [replicas -> SUBSET(Messages)]
    /\ proof \in [replicas -> SUBSET(replicas)]
    /\ rState \in [replicas -> {"none", "submitted", "confirmed", "done"}]
    
Init == 
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ predecisions \in [replicas -> values_all] (* can be any value *)
    /\ confirmed = [r \in replicas |-> "false"]
    /\ from = [r \in replicas |-> {}]
    /\ lightCertificate = [r \in replicas |-> "none"]
    /\ fullCertificate = [r \in replicas |-> {}]
    /\ obtainedLightCertificates = [r \in replicas |-> {}]
    /\ obtainedFullCertificates = [r \in replicas |-> {}]
    /\ rLog = [r \in replicas |-> {}]
    /\ proof = [r \in replicas |-> {}]
    /\ rState = [r \in replicas |-> "none"]
    

Send(m, r) == 
    rLog' = [rLog EXCEPT ![r] = rLog[r] \cup {m}]

Broadcast(m) ==
    rLog' = [r \in replicas |-> rLog[r] \cup {m}] 

BroadcastLC(m) ==
    obtainedLightCertificates' = [r \in replicas |-> obtainedLightCertificates[r] \cup {m}] 

BroadcastFC(m) ==
    obtainedFullCertificates' = [r \in replicas |-> obtainedFullCertificates[r] \cup {m}]

ByzantineBroadcast(sender) ==
    LET setOfMsgFunctions == [replicas -> {[type |-> "SUBMIT", value |-> w, signed |-> sender] : w \in values_all}]
    IN \E f \in setOfMsgFunctions : 
      /\ \E a, b \in replicas \ {sender}:
        /\ a # b 
        /\ f[a] # f[b]
      /\ rLog' = [r \in replicas |-> rLog[r] \cup {f[r]}]
    (* rLog' = [r \in replicas |-> rLog[r] \cup {[type |-> "SUBMIT", value |-> w, signed |-> sender] : w \in values_all}] *)

(* the protocol transitions *)

submit(r, v) ==
    \/ /\ r \in replicas
       /\ is_byzantine[r] = "false"
       /\ rState[r] = "none"
       /\ Broadcast([type |-> "SUBMIT", value |-> v, signed |-> r])
       /\ rState' = [rState EXCEPT ![r] = "submitted"]
       /\ UNCHANGED << confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, proof, predecisions, is_byzantine >>
    \/ /\ is_byzantine[r] = "true"
       /\ rState[r] = "none"
       /\ ByzantineBroadcast(r)
          (* \/ \E w \in values_all : Broadcast([type |-> "SUBMIT", value |-> w, signed |-> r]) *)
          (* \/ /\ values[r] = v
             /\ Broadcast([type |-> "SUBMIT", value |-> v, signed |-> r]) *)
       /\ rState' = [rState EXCEPT ![r] = "submitted"]
       /\ UNCHANGED << confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, proof, predecisions, is_byzantine >>

updateCertificates(r) ==
    /\ rState[r] \in {"none", "submitted"}
    /\ r \in replicas
    /\ rLog[r] # {}
    /\ LET submit_msgs == {m \in rLog[r] : 
                            /\ m.type = "SUBMIT"
                            /\ m.value = predecisions[r]
                            /\ m.signed # r
                            }
        IN LET submit_replicas == {rep \in replicas: (\E m \in submit_msgs : m.signed = rep)}
        IN  /\ from' = [from EXCEPT ![r] = from[r] \cup submit_replicas]
            /\ lightCertificate' = IF lightCertificate[r] = "none" THEN [lightCertificate EXCEPT ![r] = <<predecisions[r], submit_replicas>>]
                                   ELSE [lightCertificate EXCEPT ![r] = <<lightCertificate[r][1], lightCertificate[r][2] \cup submit_replicas>>]
            /\ fullCertificate' = [fullCertificate EXCEPT ![r] = fullCertificate[r] \cup submit_msgs]
            /\ rLog' = [rLog EXCEPT ![r] = {}]
    /\ UNCHANGED << predecisions, confirmed, obtainedLightCertificates, obtainedFullCertificates, proof, rState, is_byzantine >>

confirm(r, v) == 
    /\ r \in replicas
    /\ confirmed[r] = "false"
    /\ rState[r] = "submitted"
    /\ Cardinality(from[r]) \geq (Cardinality(replicas) - t0)
    /\ lightCertificate[r][1] = v
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ rState' = [rState EXCEPT ![r] = "confirmed"]
    /\ BroadcastLC([type |-> "LIGHT-CERTIFICATE", value |-> predecisions[r], signed |-> r, certificate |-> lightCertificate[r]])
    /\ UNCHANGED << predecisions, from, lightCertificate, fullCertificate, obtainedFullCertificates, proof, rLog, is_byzantine>>


light_certificates_conflict(r) ==
    /\ confirmed[r] = "true"
    /\ \E val1 \in values_all, val2 \in values_all, r1 \in replicas, r2 \in replicas, lc1 \in (values_all \X SUBSET(replicas)), lc2 \in (values_all \X SUBSET(replicas)): 
        /\ [type |-> "LIGHT-CERTIFICATE", value |-> val1, signed |-> r1, certificate |-> lc1] \in obtainedLightCertificates[r]
        /\ [type |-> "LIGHT-CERTIFICATE", value |-> val2, signed |-> r2, certificate |-> lc2] \in obtainedLightCertificates[r]
        /\ val1 # val2

full_certificates_conflict(r, c1, c2) ==
    /\ confirmed[r] = "true"
    /\ c1 \in obtainedFullCertificates[r]
    /\ c2 \in obtainedFullCertificates[r]
    /\ \E v1 \in values_all, r1 \in replicas, lc1 \in SUBSET([type : {"SUBMIT"}, value : values_all, signed : replicas]) : 
        /\ c1 = [type |-> "FULL-CERTIFICATE", value |-> v1, signed |-> r1, certificate |-> lc1]
        /\ \E v2 \in values_all, r2 \in replicas, lc2 \in SUBSET([type : {"SUBMIT"}, value : values_all, signed : replicas]) : 
            /\ c2 = [type |-> "FULL-CERTIFICATE", value |-> v2, signed |-> r2, certificate |-> lc2]
            /\ v1 # v2

bcast_full_cerificate(r) ==
    /\ r \in replicas
    /\ light_certificates_conflict(r)
    /\ BroadcastFC([type |-> "FULL-CERTIFICATE", value |-> predecisions[r], signed |-> r, certificate |-> fullCertificate[r]])
    /\ UNCHANGED << predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, proof, rLog, rState, is_byzantine >>

extract_proof(r, c1, c2) == (* symmetric difference *)
    /\ proof' = [proof EXCEPT ![r] = (c1.certificate \ c2.certificate) \cup (c2.certificate \ c1.certificate)]
    /\ UNCHANGED << predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, rLog, rState, is_byzantine >>
    
    
prove_culpability(r) ==
    /\ r \in replicas
    /\ rState[r] = "confirmed"
    /\ \E c1, c2 \in obtainedFullCertificates[r] :
       /\ full_certificates_conflict(r, c1, c2)
       /\ extract_proof(r, c1, c2)
    /\ rState' = [rState EXCEPT ![r] = "done"]
    

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

Next == \E r \in replicas : 
            \/ submit(r, predecisions[r])
            \/ updateCertificates(r)
            \/ confirm(r, predecisions[r])
            \/ bcast_full_cerificate(r)
            \/ prove_culpability(r)

vars == << predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, rLog, proof, rState, is_byzantine >>

Spec == Init /\ [][Next]_vars
    

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

THEOREM Spec => TypeOK

(* helper predicates *)

(* invariants *)

Debug ==
    \A sender \in replicas : 
        confirmed[sender] = "true"
        => \E val1 \in values_all, rcv \in replicas, lc1 \in (values_all \X SUBSET(replicas)) : 
            /\ [type |-> "LIGHT-CERTIFICATE", value |-> val1, signed |-> sender, certificate |-> lc1] \in obtainedLightCertificates[rcv]
            /\ rcv # sender

Debug2 ==
    \A r1, r2 \in replicas:
        /\ confirmed[r1] = "true"
        /\ confirmed[r2] = "true"
        /\ r1 # r2
    => \E r \in replicas:
        \E val1 \in values_all, lc1 \in (values_all \X SUBSET(replicas)) : 
            /\ [type |-> "LIGHT-CERTIFICATE", value |-> val1, signed |-> r1, certificate |-> lc1] \in obtainedLightCertificates[r]
            /\ \E val2 \in values_all, lc2 \in (values_all \X SUBSET(replicas)) : 
                [type |-> "LIGHT-CERTIFICATE", value |-> val2, signed |-> r2, certificate |-> lc2] \in obtainedLightCertificates[r]

(* accountability - safety : if there's a proof of culpability then there was faulty behvaior *)
(* if an honest replica proves another replica to be guilty then the guilty replica must be byzantine *)

Accountability == 
    \A r1 \in replicas, r2 \in replicas : is_byzantine[r1] = "false" => (r2 \in proof[r1] => is_byzantine[r2] = "true")

=============================================================================