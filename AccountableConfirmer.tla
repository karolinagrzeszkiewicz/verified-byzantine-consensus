----------------------------- MODULE AccountableConfirmer ----------------------------

(* this is for a single iteration i.e. single consensus *)

EXTENDS Integers, Sequences, FiniteSets, Naturals

CONSTANTS
    replicas,
    byzantines,
    values_all, (* set of possible values *)
    values_BC, (* values decided in the BFT *)
    t0

ASSUME
    /\ values_BC \in [Replicas -> values_all] (* TODO: this cant be a function bc not allowed in config*)
    /\ byzantines \subseteq Replicas
    /\ t0 \in Nat
    (* /\ t0 == Cardinality(replicas) / 3 - 1 *) (* ceiling of n / 3*)


VARIABLES
    values,
    confirmed,
    from,
    lightCertificate,
    fullCertificate,
    obtainedLightCertificates,
    obtainedFullCertificates,
    rLog, (* temporary storage for submit messages *)
    proof (* of culpability *)

Messages ==
    [type : {"SUBMIT"}, value : values_all, signed : replicas]
    \cup
    [type: {"LIGHT-CERTIFICATE"}, value : values_all, signed : replicas, certificate : values_all \X SUBSET(replicas)] (* values_all not needed here ? *)
    \cup 
    [type: {"FULL-CERTIFICATE"}, value : values_all, signed : replicas, certificate : [type : {"SUBMIT"}, value : values_all, signed : replicas]] 

TypeOK == 
    /\ values \in [replicas -> all_values \cup {"none"}] (* to store each replica's value *)
    /\ confirmed \in [replicas -> {"true", "false"}]
    /\ from \in [replicas -> replicas] (* to keep track of replicas that submitted the same value: i.e. submit messages for the same value *)
    /\ lightCertificate \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] (* light signature = (v, signatures) *)
    /\ fullCertificate \in [replicas -> {"none"} \cup Messages] (* set of SUBMIT messages *)
    /\ obtainedLightCertificates \in [replicas -> Messages] (* set of LIGHT-CERTIFICATE messages, each contained lightCertificates *)
    /\ obtainedFullCertificates \in [replicas -> Messages] (* set of FULL-CERTIFICATE messages, each contained fullCertificates *)
    /\ rLog \in [replicas -> Messages]
    /\ proof \in [replicas -> replicas]
    
Init == 
    /\ values = [r \in replicas -> "none"]
    /\ confirmed = [r \in replicas -> "false"]
    /\ from = [r \in replicas -> {}]
    /\ lightCertificate = [r \in replicas -> "none"]
    /\ fullCertificate = [r \in replicas -> "none"]
    /\ obtainedLightCertificates = [r \in replicas -> {}]
    /\ obtainedFullCertificates = [r \in replicas -> {}]
    /\ rLog = [r \in replicas -> {}]
    /\ proof = {}
    

Send(m, r) == 
    rLog' = [rLog EXCEPT ![r] = rLog[r] \cup {m}] (* means the message gets delivered and inserted in the addressee's log *)

Broadcast(m) ==
    rLog' = [r \in replicas |-> rLog[r] \cup {m}] 

BroadcastLC(m) ==
    obtainedLightCertificates' = [r \in replicas |-> obtainedLightCertificates[r] \cup {m}] 

BroadcastFC(m) ==
    obtainedFullCertificates' = [r \in replicas |-> obtainedFullCertificates[r] \cup {m}]

ByzantineBroadcast(r) ==
    [addr \in replicas |-> \E w \in values_all : rLog[addr] \cup {[type |-> "SUBMIT", value |-> w, signed |-> r]}] 

(* the protocol transitions *)

submit(r, v) ==
    \/ /\ r \in replicas \ byzantines
       /\ values_BC[r] = v
       /\ Broadcast([[type |-> "SUBMIT", value |-> v, signed |-> r]])
       /\ values' = [values EXCEPT ![r] = v]
       /\ UNCHANGED << confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, proof >>
    \/ /\ r \in byzantines (* TODO: send differnet values to different replicas *)
       /\ \/ /\ \E w \in values_all : 
             /\ Broadcast([[type |-> "SUBMIT", value |-> w, signed |-> r]])
             /\ values' = [values EXCEPT ![r] = w]
          \/ /\ ByzantineBroadcast(r)
             /\ \E w \in values_all : values' = [values EXCEPT ![r] = w]
          \/ /\ values_BC[r] = v
             /\ Broadcast([[type |-> "SUBMIT", value |-> v, signed |-> r]])
             /\ values' = [values EXCEPT ![r] = v]
       /\ UNCHANGED << confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, proof >>

updateCertificates(r) ==
    /\ r \in replicas
    /\ \A msg \in rLog[r]: 
        /\ LET submit_msgs == {m \in rLog[r] : 
                                /\ m.type = "SUBMIT"
                                /\ m.value = values[r]
                              }
          IN LET submit_replicas == {r \in replicas: (\E m \in submit_msgs : m.signed = r)}
          IN /\ from' = [from EXCEPT ![r] = from[r] \cup submit_replicas]
             /\ lightCertificate' = [lightCertificate EXCEPT ![r] = <lightCertificate[r][1], lightCertificate[r][2] \cup submit_replicas>]
             /\ fullCertificate' = [fullCertificate EXCEPT ![r] = fullCertificate[r] \cup submit_msgs]
             /\ rLog' = [rLog EXCEPT ![r] = {}] (* can we just clear the log? Yes, it only stores submit msgs *)
    /\ UNCHANGED << values, confirmed, obtainedLightCertificates, obtainedFullCertificates, proof >>

confirm(r) == 
    /\ Cardinality(from[r]) \geq (Cardinality(replicas) - t0)
    /\ r \in replicas
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ (* trigger <ac, confirm | value[r]> *)
    /\ BroadcastLC([type |-> "LIGHT-CERTIFICATE", value |-> values[r], signed |-> r, certificate |-> lightCertificate[r]])
    /\ UNCHANGED << values, from, lightCertificate, fullCertificate, obtainedFullCertificates, proof, rLog >>

light_certificates_conflict(r, c1, c2) ==
    /\ confimed[r] = "true"
    /\ c1 \in obtainedLightCertificates
    /\ c2 \in obtainedLightCertificates
    /\ \E v1 \in values_all, r1 \in replicas, lc1 \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] : 
        c1 = [type |-> "LIGHT-CERTIFICATE", value |-> v1, signed |-> r1, certificate |-> lc1]
    /\ \E v2 \in values_all, r2 \in replicas, lc2 \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] : 
        c2 = [type |-> "LIGHT-CERTIFICATE", value |-> v2, signed |-> r2, certificate |-> lc2]
    /\ v1 # v2

full_certificates_conflict(r, c1, c2) ==
    /\ confimed[r] = "true"
    /\ c1 \in obtainedFullCertificates
    /\ c2 \in obtainedFullCertificates
    /\ \E v1 \in values_all, r1 \in replicas, lc1 \in [replicas -> [type : {"SUBMIT"}, value : values_all, signed : replicas]] : 
        c1 = [type |-> "FULL-CERTIFICATE", value |-> v1, signed |-> r1, certificate |-> lc1]
    /\ \E v2 \in values_all, r2 \in replicas, lc2 \in [type : {"SUBMIT"}, value : values_all, signed : replicas] : 
        c2 = [type |-> "FULL-CERTIFICATE", value |-> v2, signed |-> r2, certificate |-> lc2]
    /\ v1 # v2

bcast_full_cerificate(r) ==
    /\ r \in replicas
    /\ \E c1, c2 \in obtainedLightCertificates[r] : light_certificates_conflict(r, c1, c2)
    /\ BroadcastFC([type |-> "FULL-CERTIFICATE", value |-> values[r], signed |-> r, certificate |-> fullCertificate[r]])
    /\ UNCHANGED << values, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, proof, rLog >>

extract_proof(r, c1, c2) == (* symmetric difference *)
    /\ proof' = [proof EXCEPT ![r] = (c1.certificate \ c2.certificate) \U (c2.certificate \ c1.certificate)]
    /\ UNCHANGED << values, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, rLog >>
    
    
prove_culpability(r) ==
    /\ r \in replicas
    /\ \E c1, c2 \in obtainedFullCertificates[r] :
       /\ full_certificates_conflict(r, c1, c2)
       /\ extract_proof(r, c1, c2)

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

Next == \E r \in replicas : 
            \/ submit(r, values_BC[r])
            \/ updateCertificates(r)
            \/ confirm(r)
            \/ bcast_full_cerificate(r)
            \/ prove_culpability(r)

vars == << values, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, rLog, proof >>

Spec == Init /\ [][Next]_vars
    

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

THEOREM Spec => TypeOK

(* helper predicates *)

(* invariants *)

(* accountability - safety : if there's a proof of culpability then there was faulty behvaior *)
(* if an honest replica proves another replica to be guilty then the guilty replica must be byzantine *)

Accountability == 
    \E r1 \in replicas \ byzantines, r2 \in replicas : r2 \in proof[r1] => r2 \in byzantines