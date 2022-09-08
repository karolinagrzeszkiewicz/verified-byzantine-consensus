----------------------------- MODULE AccountableConfirmer ----------------------------

EXTENDS Integers, Sequences, FiniteSets, Naturals

CONSTANTS
    replicas,
    byzantines,
    values_all,
    values_BC,
    f

ASSUME
    /\ values_BC \in [Replicas -> values_all]
    /\ Byzantines \subseteq Replicas
    /\ f \in Nat


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
    /\ values \in [replicas -> all_values \cup {"none"}]
    /\ confirmed \in [replicas -> {"true", "false"}]
    /\ from \in [replicas -> SUBSET(replicas)]
    /\ lightCertificate \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] (* light signature = (v, signatures) *)
    /\ fullCertificate \in [replicas -> {"none"} \cup Messages]
    /\ obtainedLightCertificates \in [replicas -> Messages]
    /\ obtainedFullCertificates \in [replicas -> Messages] (* ? *)
    /\ proof \in SUBSET(replicas)
    
Init == 
    /\ values = [r \in replicas -> "none"]
    /\ confirmed = [r \in replicas -> "false"]
    /\ from = [r \in replicas -> {}]
    /\ lightCertificate = [r \in replicas -> "none"]
    /\ fullCertificate = [r \in replicas -> "none"]
    /\ obtainedLightCertificates = [r \in replicas -> {}]
    /\ obtainedFullCertificates = [r \in replicas -> {}]
    /\ proof = {}
    

Send(m, r) == 
    rLog' = [rLog EXCEPT ![r] = rLog[r] \cup {m}] (* means the message gets delivered and inserted in the addressee's log *)

Broadcast(m) ==
    rLog' = [r \in replicas |-> rLog[r] \cup {m}] 

BroadcastLC(m) ==
    obtainedLightCertificates' = [r \in replicas |-> obtainedLightCertificates[r] \cup {m}] 

BroadcastFC(m) ==
    obtainedFullCertificates' = [r \in replicas |-> obtainedFullCertificates[r] \cup {m}]


(* the protocol transitions *)

submit(r, v) ==
    \/ /\ r \in replicas \ byzantines
       /\ values_BC[r] = v
       /\ Broadcast([[type |-> "SUBMIT", value |-> v, signed |-> r]])
       /\ values' = [values EXCEPT ![r] = v]
    \/ /\ r \in byzantines (* TODO: send differnet values to different replicas *)
       /\ \E w \in values_all : 
            /\ Broadcast([[type |-> "SUBMIT", value |-> w, signed |-> r]])
            /\ values' = [values EXCEPT ![r] = w]

updateCertificates(r) ==
    /\ r \in replicas
    /\ \A msg \in rLog[r]: 
        IF \E p \in replicas : msg = [type |-> "SUBMIT", value |-> values[r], signed |-> p]
        THEN /\ from' = [from EXCEPT ![r] = from[r] \cup {p}]
             /\ lightCertificate' = [lightCertificate EXCEPT ![r] = <lightCertificate[r][1], lightCertificate[r][2] \cup {p}>]
             /\ fullCertificate' = [fullCertificate EXCEPT ![r] = fullCertificate[r] \cup {msg}]
             /\ rLog' = [rLog EXCEPT ![r] = {}] (* can we just clear the log? Yes, it only stores submit msgs *)

confirm(r) == 
    /\ Cardinality(from[r]) \geq (Cardinality(replicas) - f)
    /\ r \in replicas
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ (* trigger <ac, confirm | value[r]> *)
    /\ BroadcastLC([type |-> "LIGHT-CERTIFICATE", value |-> values[r], signed |-> r, certificate |-> lightCertificate[r]])

light_certificates_conflict(r, c1, c2) ==
    /\ confimed[r] = "true"
    /\ c1 \in obtainedLightCertificates
    /\ c2 \in obtainedLightCertificates
    /\ \E v1 \in values_all, r1 \in replicas, lc1 \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] : 
        c1 = [type |-> "FULL-CERTIFICATE", value |-> v1, signed |-> r1, certificate |-> lc1]
    /\ \E v2 \in values_all, r2 \in replicas, lc2 \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] : 
        c2 = [type |-> "FULL-CERTIFICATE", value |-> v2, signed |-> r2, certificate |-> lc2]
    /\ v1 # v2

full_certificates_conflict(r, c1, c2) ==
    /\ confimed[r] = "true"
    /\ c1 \in obtainedFullCertificates
    /\ c2 \in obtainedFullCertificates
    /\ \E v1 \in values_all, r1 \in replicas, lc1 \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] : 
        c1 = [type |-> "LIGHT-CERTIFICATE", value |-> v1, signed |-> r1, certificate |-> lc1]
    /\ \E v2 \in values_all, r2 \in replicas, lc2 \in [replicas -> {"none"} \cup (values_all \X SUBSET(replicas))] : 
        c2 = [type |-> "LIGHT-CERTIFICATE", value |-> v2, signed |-> r2, certificate |-> lc2]
    /\ v1 # v2

bcast_full_cerificate(r) ==
    /\ r \in replicas
    /\ \E c1, c2 \in obtainedLightCertificates[r] : light_certificates_conflict(r, c1, c2)
    /\ BroadcastFC([type |-> "FULL-CERTIFICATE", value |-> values[r], signed |-> r, certificate |-> fullCertificate[r]])

extract_proof(r, c1, c2) == (* symmetric difference would be ideal here*)
    proof' = (c1.certificate \ c2.certificate) \U (c2.certificate \ c1.certificate)
    
    
prove_culpability(r) ==
    /\ r \in replicas
    /\ \E c1, c2 \in obtainedFullCertificates[r] :
       /\ full_certificates_conflict(r, c1, c2)
       /\ extract_proof(r, c1, c2)
    