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
    rState,
    confirmedVal,
    submitted

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
    /\ confirmedVal \in [replicas -> values_all_opt]
    /\ submitted \in [replicas -> SUBSET(values_all)]
    
Init == 
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ predecisions \in [replicas -> values_all] (* can be any value *)
    /\ confirmed = [r \in replicas |-> "false"]
    /\ from = [r \in replicas |-> {}]
    /\ lightCertificate = [r \in replicas |-> << "none", {} >>]
    /\ fullCertificate = [r \in replicas |-> {}]
    /\ obtainedLightCertificates = [r \in replicas |-> {}]
    /\ obtainedFullCertificates = [r \in replicas |-> {}]
    /\ rLog = [r \in replicas |-> {}]
    /\ proof = [r \in replicas |-> {}]
    /\ rState = [r \in replicas |-> "none"]
    /\ confirmedVal = [r \in replicas |-> "none"]
    /\ submitted = [r \in replicas |-> {}]
    

Send(m, r) == 
    rLog' = [rLog EXCEPT ![r] = rLog[r] \cup {m}]

Broadcast(m) ==
    rLog' = [r \in replicas |-> rLog[r] \cup {m}]

BroadcastLC(m) ==
    obtainedLightCertificates' = [r \in replicas |-> obtainedLightCertificates[r] \cup {m}] 

BroadcastFC(m) ==
    obtainedFullCertificates' = [r \in replicas |-> obtainedFullCertificates[r] \cup {m}]

(* the protocol transitions *)

ByzantineBroadcastSubmit(sender) ==
    LET setOfValFunctions == [replicas -> values_all]
    IN \E f \in setOfValFunctions : 
      /\ \E a, b \in replicas \ {sender}:
        /\ a # b 
        /\ f[a] # f[b]
      /\ submitted' = [submitted EXCEPT ![sender] = {f[rcv] : rcv \in replicas \ {sender}}]
      /\ LET reps == [p \in replicas |-> IF predecisions[p] = f[p] THEN {sender} ELSE {}]
         IN LET msgs == [p \in replicas |-> IF predecisions[p] = f[p] THEN {[type |-> "SUBMIT", value |-> predecisions[p], signed |-> sender]} ELSE {}]
         IN /\ from' = [p \in replicas |-> from[p] \cup reps[p]]
            /\ lightCertificate' = [p \in replicas |-> << predecisions[p], lightCertificate[p][2] \cup reps[p]>>]
            /\ fullCertificate' = [p \in replicas |-> fullCertificate[p] \cup msgs[p]]

BroadcastSubmit(r) ==
    LET reps == [p \in replicas |-> IF predecisions[p] = predecisions[r] THEN {r} ELSE {}]
    IN LET msgs == [p \in replicas |-> IF predecisions[p] = predecisions[r] THEN {[type |-> "SUBMIT", value |-> predecisions[r], signed |-> r]} ELSE {}]
    IN /\ from' = [p \in replicas |-> from[p] \cup reps[p]]
       /\ lightCertificate' = [p \in replicas |-> << predecisions[p], lightCertificate[p][2] \cup reps[p]>>]
       /\ fullCertificate' = [p \in replicas |-> fullCertificate[p] \cup msgs[p]]

submit(r) ==
    \/ /\ r \in replicas
       /\ is_byzantine[r] = "false"
       /\ rState[r] = "none"
       /\ BroadcastSubmit(r)
       /\ submitted' = [submitted EXCEPT ![r] = {predecisions[r]}]
       /\ rState' = [rState EXCEPT ![r] = "submitted"]
       /\ UNCHANGED << confirmed, rLog, obtainedLightCertificates, obtainedFullCertificates, proof, predecisions, is_byzantine, confirmedVal >>
    \/ /\ r \in replicas
       /\ is_byzantine[r] = "true"
       /\ rState[r] = "none"
       /\ ByzantineBroadcastSubmit(r)
       /\ rState' = [rState EXCEPT ![r] = "submitted"]
       /\ UNCHANGED << confirmed, rLog, obtainedLightCertificates, obtainedFullCertificates, proof, predecisions, is_byzantine, confirmedVal >>


(* \/ \E w \in values_all : Broadcast([type |-> "SUBMIT", value |-> w, signed |-> r]) *)
          (* \/ /\ values[r] = v
             /\ Broadcast([type |-> "SUBMIT", value |-> v, signed |-> r]) *)
    

confirm(r) == 
    /\ r \in replicas
    /\ confirmed[r] = "false"
    /\ rState[r] = "submitted"
    /\ Cardinality(from[r]) \geq (Cardinality(replicas) - t0)
    /\ lightCertificate[r][1] = predecisions[r]
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ confirmedVal' = [confirmedVal EXCEPT ![r] = predecisions[r]]
    /\ rState' = [rState EXCEPT ![r] = "confirmed"]
    /\ BroadcastLC([type |-> "LIGHT-CERTIFICATE", value |-> predecisions[r], signed |-> r, certificate |-> lightCertificate[r]])
    /\ UNCHANGED << predecisions, from, lightCertificate, fullCertificate, obtainedFullCertificates, proof, rLog, is_byzantine, submitted >>


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
    /\ UNCHANGED << predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, proof, rLog, rState, is_byzantine, submitted, confirmedVal >>

extract_proof(r, c1, c2) == (* symmetric difference *)
    /\ proof' = [proof EXCEPT ![r] = (c1.certificate \ c2.certificate) \cup (c2.certificate \ c1.certificate)]
    /\ UNCHANGED << predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, rLog, rState, is_byzantine, submitted, confirmedVal >>
    
    
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
            \/ submit(r)
            \/ confirm(r)
            \/ bcast_full_cerificate(r)
            \/ prove_culpability(r)

vars == << predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, rLog, proof, rState, is_byzantine, submitted, confirmedVal >>

Spec == Init /\ [][Next]_vars
    

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

THEOREM Spec => TypeOK

(* helper predicates *)

(* this predicate means that two honest replicas have confirmed different values 
=> which implies that they must have broadcasted light certificates for
and any honest replicas (including p and q) must have detected a conflict and broadcasted full certificates
=> then any honest replica having received two conflicting full certificates has enough info to prove culpability 
of a replica included in both certificates (since it has sent two incompatible SUBMIT msgs) *)

confirmDifferentVal(p, q) ==
    \E vp \in values_all, vq \in values_all:
        /\ is_byzantine[p] = "false"
        /\ is_byzantine[q] = "false"
        /\ p # q
        /\ vp # vq
        /\ confirmed[p] = "true"
        /\ confirmed[q] = "true"
        /\ confirmedVal[p] = vp
        /\ confirmedVal[q] = vq

SomeConfirmDifferentVal ==
    \E p \in replicas, q \in replicas : confirmDifferentVal(p, q)

behavedByzantine(r) ==
    \E v1 \in submitted[r], v2 \in submitted[r] : v1 # v2

(* invariants *)

invFromComplete ==
    \A b \in replicas, r \in replicas :
        (\E v \in submitted[b] : 
            /\ is_byzantine[r] = "false" 
            /\ predecisions[r] = v
            /\ Cardinality(from[r]) \geq (Cardinality(replicas) - t0))
            => b \in from[r]

invFromConsistent1 ==
    \A b \in replicas, r \in replicas :
        b \in from[r] /\ is_byzantine[r] = "false" => predecisions[r] \in submitted[b]

invFromConsistent2 ==
    \A b \in replicas, r \in replicas :
        b \in from[r] /\ is_byzantine[r] = "false" => predecisions[r] = predecisions[b] \/ is_byzantine[b] = "true"

invConfirmDifferentValComplete ==
    \A r1 \in replicas, r2 \in replicas :
        (/\ is_byzantine[r1] = "false"
        /\ is_byzantine[r2] = "false"
        /\ predecisions[r1] # predecisions[r2]
        /\ Cardinality(from[r1]) \geq (Cardinality(replicas) - t0)
        /\ Cardinality(from[r2]) \geq (Cardinality(replicas) - t0))
        => confirmDifferentVal(r1, r2)

invConfirmDifferentValConsistent1 ==
    \A r1 \in replicas, r2 \in replicas :
        confirmDifferentVal(r1, r2)
        => /\ Cardinality(from[r1]) \geq (Cardinality(replicas) - t0)
           /\ Cardinality(from[r2]) \geq (Cardinality(replicas) - t0)
           /\ predecisions[r1] # predecisions[r2]

invConfirmDifferentValConsistent2 ==
    \A r1 \in replicas, r2 \in replicas :
        confirmDifferentVal(r1, r2)
        => \E r \in replicas : r \in from[r1] /\ r \in from[r2] (* nonempty intersection *)

invConfirmDifferentValConsistent3 ==
    \A r1 \in replicas, r2 \in replicas :
        confirmDifferentVal(r1, r2)
        => \E r \in replicas : behavedByzantine(r) (* byzantine behaviour *)

invConfirm ==
    \A b \in replicas, r1 \in replicas, r2 \in replicas :
        (\E v1 \in submitted[b], v2 \in submitted[b] : 
            /\ is_byzantine[r1] = "false" /\ predecisions[r1] = v1
            /\ is_byzantine[r2] = "false" /\ predecisions[r2] = v2
            /\ v1 # v2
            /\ rState[r1] = "confirmed"
            /\ rState[r2] = "confirmed")
            => confirmDifferentVal(r1, r2)

invLCConflict ==
    \A r \in replicas : confirmed[r] = "true" =>
    (SomeConfirmDifferentVal => light_certificates_conflict(r))

(* Debugging *)

(* Debug ==
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
                [type |-> "LIGHT-CERTIFICATE", value |-> val2, signed |-> r2, certificate |-> lc2] \in obtainedLightCertificates[r] *)

(* Accountability *)

AccountabilitySoundness ==
    \A r1 \in replicas : is_byzantine[r1] = "false"
    => \A r2 \in proof[r1] : behavedByzantine(r2)

AccountabilityCompleteness ==
    \A r1 \in replicas : is_byzantine[r1] = "false"
    => (\A r2 \in replicas :
            (/\ behavedByzantine(r2)
            /\ SomeConfirmDifferentVal
            /\ rState[r1] = "proved") 
            => r2 \in proof[r1])
    
(* Accountability == 
    /\ AccountabilitySoundness
    /\ AccountabilityCompleteness *)

=============================================================================