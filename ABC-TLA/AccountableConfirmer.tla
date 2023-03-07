----------------------------- MODULE AccountableConfirmer ----------------------------

EXTENDS Integers, Sequences, FiniteSets, Naturals, TLC

CONSTANTS
    replicas,
    values_all

symm == Permutations(replicas) \union Permutations(values_all)

VARIABLES
    is_byzantine,
    predecisions, 
    confirmed,
    from,
    lightCertificate,
    fullCertificate,
    obtainedLightCertificates,
    obtainedFullCertificates,
    proof, (* of culpability *)
    rState,
    confirmedVal,
    submitted,
    msgs,
    countSubmit

values_all_opt == {"none"} \cup values_all

divide_by_three_ceil(m) == CHOOSE k \in 0..m: 3*(k-1) < m /\ m \leq 3*k

n == Cardinality(replicas)
t0 == divide_by_three_ceil(n) - 1
f == Cardinality({p \in replicas : is_byzantine[p] = "true"})
k == n - t0

(* predictates for the initial setup *)

ConsensusPreCond ==
    LET byzantines == {r \in replicas : is_byzantine[r] = "true"}
    IN ~ (Cardinality(byzantines) \geq t0 + 1)

(* in case we want to initialise predecisions with values from the BFT *)
Consensus ==
    ConsensusPreCond => 
        \A r1 \in replicas, r2 \in replicas : 
        (/\ is_byzantine[r1] = "false"
         /\ is_byzantine[r2] = "false")
        => predecisions[r1] = predecisions[r2]
    

Messages ==
    [type : {"SUBMIT"}, value : values_all, signed : replicas, to : replicas]
    \cup
    [type: {"LIGHT-CERTIFICATE"}, value : values_all, signed : replicas, certificate : values_all \X SUBSET(replicas), to : replicas]
    \cup 
    [type: {"FULL-CERTIFICATE"}, value : values_all, signed : replicas, certificate : [type : {"SUBMIT"}, value : values_all, signed : replicas, to : replicas], to : replicas] 

TypeOK == 
    /\ is_byzantine \in [replicas -> {"true", "false"}] 
    /\ predecisions \in [replicas -> values_all] (* to store each replica's value *)
    /\ confirmed \in [replicas -> {"true", "false"}]
    /\ from \in [replicas -> replicas] (* to keep track of replicas that submitted the same value: i.e. submit messages for the same value *)
    /\ lightCertificate \in [replicas -> values_all \X SUBSET(replicas)] (* light signature = (v, signatures) *)
    /\ fullCertificate \in [replicas -> SUBSET(Messages)] (* set of SUBMIT messages *)
    /\ obtainedLightCertificates \in [replicas -> SUBSET(Messages)] (* set of LIGHT-CERTIFICATE messages, each contained lightCertificates *)
    /\ obtainedFullCertificates \in [replicas -> SUBSET(Messages)] (* set of FULL-CERTIFICATE messages, each contained fullCertificates *)
    /\ proof \in [replicas -> SUBSET(replicas)]
    /\ rState \in [replicas -> {"none", "submitted", "confirmed", "lc-complete", "full-bcast", "done"}]
    /\ confirmedVal \in [replicas -> values_all_opt]
    /\ submitted \in [replicas -> SUBSET(values_all)]
    /\ msgs \in SUBSET(Messages)
    /\ countSubmit \in [replicas -> Nat]
    
Init == 
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ predecisions \in [replicas -> values_all] (* can be any value *)
    /\ confirmed = [r \in replicas |-> "false"]
    /\ from = [r \in replicas |-> {}]
    /\ lightCertificate = [r \in replicas |-> << predecisions[r], {} >>]
    /\ fullCertificate = [r \in replicas |-> {}]
    /\ obtainedLightCertificates = [r \in replicas |-> {}]
    /\ obtainedFullCertificates = [r \in replicas |-> {}]
    /\ proof = [r \in replicas |-> {}]
    /\ rState = [r \in replicas |-> "none"]
    /\ confirmedVal = [r \in replicas |-> "none"]
    /\ submitted = [r \in replicas |-> {}]
    /\ msgs = {}
    /\ countSubmit = [r \in replicas |-> 0]
    

Send(m) ==
    msgs' = msgs \cup {m}

(* assumption: the n - t0 threshold for a replica's confirm includes the replica so a replica also sends SUBMIT to itself *)

BroadcastSubmit(r) ==
    LET submit_msgs == {[type |-> "SUBMIT", value |-> predecisions[r], signed |-> r, to |-> rcv] : rcv \in replicas }
    IN msgs' = msgs \cup submit_msgs

ByzantineBroadcastSubmit(sender) ==
    LET setOfValFunctions == [replicas -> values_all]
    IN \E g \in setOfValFunctions : 
      /\ \E a, b \in replicas \ {sender}:
        /\ a # b 
        /\ g[a] # g[b]
      /\ submitted' = [submitted EXCEPT ![sender] = {g[rcv] : rcv \in replicas}]
      /\ msgs' = msgs \cup {[type |-> "SUBMIT", value |-> g[r], signed |-> sender, to |-> r] : r \in replicas}
    

BroadcastLC(r) ==
    msgs' = msgs \cup {[type |-> "LIGHT-CERTIFICATE", value |-> predecisions[r], signed |-> r, certificate |-> lightCertificate[r], to |-> rcv] : rcv \in replicas}

    
BroadcastFC(r) ==
    msgs' = msgs \cup {[type |-> "FULL-CERTIFICATE", value |-> predecisions[r], signed |-> r, certificate |-> fullCertificate[r], to |-> rcv] : rcv \in replicas}
    

(* the protocol transitions *)


submit(r) ==
    /\ r \in replicas
    /\ rState[r] = "none"
    /\ is_byzantine[r] = "false"
    /\ BroadcastSubmit(r)
    /\ submitted' = [submitted EXCEPT ![r] = {predecisions[r]}]
    /\ rState' = [rState EXCEPT ![r] = "submitted"]
    /\ UNCHANGED << countSubmit, confirmed, obtainedLightCertificates, obtainedFullCertificates, proof, predecisions, is_byzantine, confirmedVal, from, fullCertificate, lightCertificate>>

submitByzantine(r) ==
    /\ r \in replicas
    /\ rState[r] = "none"
    /\ is_byzantine[r] = "true"
    /\ ByzantineBroadcastSubmit(r)
    /\ rState' = [rState EXCEPT ![r] = "submitted"]
    /\ UNCHANGED << countSubmit, confirmed, obtainedLightCertificates, obtainedFullCertificates, proof, predecisions, is_byzantine, confirmedVal, from, fullCertificate, lightCertificate >>
    

receiveSubmit(r) ==
    /\ rState[r] \in {"none", "submitted"}
    /\ r \in replicas
    /\ msgs # {}
    /\ \E m \in msgs :
        /\ m.type = "SUBMIT"
        /\ m.to = r
        /\ \/ (/\ m.value # predecisions[r]
               /\ msgs' = msgs \ {m}
               /\ countSubmit' = [countSubmit EXCEPT ![r] = countSubmit[r] + 1]
               /\ UNCHANGED << from, fullCertificate, lightCertificate, predecisions, confirmed, obtainedLightCertificates, obtainedFullCertificates, proof, rState, is_byzantine, submitted, confirmedVal >>)
           \/ (/\ m.value = predecisions[r]
               /\ \E s \in replicas : 
                    /\ m.signed = s
                    /\ from' = [from EXCEPT ![r] = from[r] \cup {s}]
                    /\ lightCertificate' = [lightCertificate EXCEPT ![r] = <<lightCertificate[r][1], lightCertificate[r][2] \cup {s} >>]
                    /\ fullCertificate' = [fullCertificate EXCEPT ![r] = fullCertificate[r] \cup {m}]
                    /\ msgs' = msgs \ {m}
                    /\ countSubmit' = [countSubmit EXCEPT ![r] = countSubmit[r] + 1]
                    /\ UNCHANGED << predecisions, confirmed, obtainedLightCertificates, obtainedFullCertificates, proof, rState, is_byzantine, submitted, confirmedVal >>)

forgePartialSignaturesByzantine(r) ==
    /\ r \in replicas
    /\ is_byzantine[r] = "true"
    /\ rState[r] = "submitted"
    /\ f > n - k
    /\ \E v \in values_all, signatures \in SUBSET(replicas):
        lightCertificate' = [lightCertificate EXCEPT ![r] = << v, signatures >>]
    /\ rState' = [rState EXCEPT ![r] = "lc-complete"]
    /\ UNCHANGED << proof, countSubmit, predecisions, confirmed, from, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, msgs, is_byzantine, submitted, confirmedVal >>


confirm(r) == 
    /\ r \in replicas
    /\ confirmed[r] = "false"
    /\ rState[r] = "submitted"
    /\ Cardinality(from[r]) \geq (Cardinality(replicas) - t0)
    /\ lightCertificate[r][1] = predecisions[r]
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ confirmedVal' = [confirmedVal EXCEPT ![r] = predecisions[r]]
    /\ rState' = [rState EXCEPT ![r] = "confirmed"]
    /\ BroadcastLC(r)
    /\ UNCHANGED << countSubmit, predecisions, from, lightCertificate, fullCertificate, obtainedFullCertificates, obtainedLightCertificates, proof, is_byzantine, submitted >>

confirmByzantine(r) ==
    /\ r \in replicas
    /\ is_byzantine[r] = "true"
    /\ confirmed[r] = "false"
    /\ f > n - k
    /\ rState[r] \in {"submitted", "lc-complete"}
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ confirmedVal' = [confirmedVal EXCEPT ![r] = predecisions[r]]
    /\ rState' = [rState EXCEPT ![r] = "confirmed"]
    /\ BroadcastLC(r)
    /\ UNCHANGED << countSubmit, predecisions, from, lightCertificate, fullCertificate, obtainedFullCertificates, obtainedLightCertificates, proof, is_byzantine, submitted >>

receiveLC(r) ==
    /\ \E m \in msgs:
        /\ m.type = "LIGHT-CERTIFICATE"
        /\ m.to = r
        /\ obtainedLightCertificates' = [obtainedLightCertificates EXCEPT ![r] = obtainedLightCertificates[r] \cup {m}]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED << countSubmit, confirmed, obtainedFullCertificates, proof, predecisions, is_byzantine, confirmedVal, rState, submitted, from, fullCertificate, lightCertificate >>

light_certificates_conflict(r) ==
    \E m1 \in obtainedLightCertificates[r], m2 \in obtainedLightCertificates[r]:
        m1.value # m2.value

full_certificates_conflict(r, c1, c2) ==
    /\ c1 \in obtainedFullCertificates[r]
    /\ c2 \in obtainedFullCertificates[r]
    /\ c1.value # c2.value

bcast_full_cerificate(r) ==
    /\ r \in replicas
    /\ rState[r] = "confirmed"
    /\ confirmed[r] = "true"
    /\ light_certificates_conflict(r)
    /\ BroadcastFC(r)
    /\ rState' = [rState EXCEPT ![r] = "full-bcast"]
    /\ UNCHANGED << countSubmit, predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, proof, is_byzantine, submitted, confirmedVal >>

receiveFC(r) ==
    /\ \E m \in msgs:
        /\ m.type = "FULL-CERTIFICATE"
        /\ m.to = r
        /\ obtainedFullCertificates' = [obtainedFullCertificates EXCEPT ![r] = obtainedFullCertificates[r] \cup {m}]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED << countSubmit, confirmed, obtainedLightCertificates, proof, predecisions, is_byzantine, confirmedVal, submitted, from, fullCertificate, lightCertificate, rState >>

(* keep extending the proof until there are conflicting certificates being added to obtainedFullCertificates *)
extract_proof(r, c1, c2) == 
    LET c1rep == {p \in replicas : (\E submit_msg \in c1.certificate : submit_msg.signed = p)}
        c2rep == {p \in replicas : (\E submit_msg \in c2.certificate : submit_msg.signed = p)}
        c1intersectionc2 == c1rep \intersect c2rep
    IN /\ \E rep \in c1intersectionc2 : ~ (rep \in proof[r])
       /\ proof' = [proof EXCEPT ![r] = proof[r] \union c1intersectionc2]
    
(* TODO: should be allowed to repeat ie for state "done" *)
prove_culpability(r) ==
    /\ r \in replicas
    /\ rState[r] \in {"confirmed", "full-bcast"}
    /\ confirmed[r] = "true"
    /\ \E c1, c2 \in obtainedFullCertificates[r] :
       /\ full_certificates_conflict(r, c1, c2)
       /\ extract_proof(r, c1, c2)
    /\ rState' = [rState EXCEPT ![r] = "done"]
    /\ UNCHANGED << countSubmit, predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, msgs, is_byzantine, submitted, confirmedVal >>
    
    

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

Next == \E r \in replicas : 
            \/ submit(r)
            \/ receiveSubmit(r)
            \/ confirm(r)
            \/ receiveLC(r)
            \/ bcast_full_cerificate(r)
            \/ receiveFC(r)
            \/ prove_culpability(r)
            \/ submitByzantine(r)
            \/ forgePartialSignaturesByzantine(r)
            \/ confirmByzantine(r)

vars == << countSubmit, predecisions, confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, obtainedFullCertificates, msgs, proof, rState, is_byzantine, submitted, confirmedVal >>

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

ConfirmedSameVal == ~ SomeConfirmDifferentVal

behavedByzantine(r) ==
    \E v1 \in submitted[r], v2 \in submitted[r] : v1 # v2

(* invariants *)

invFromComplete ==
    \A b \in replicas, r \in replicas :
        (\E v \in submitted[b] : 
            /\ is_byzantine[r] = "false" 
            /\ predecisions[r] = v
            /\ Cardinality(from[r]) \geq (Cardinality(replicas)))
            => b \in from[r]

invFromSound1 ==
    \A b \in replicas, r \in replicas :
        b \in from[r] /\ is_byzantine[r] = "false" => predecisions[r] \in submitted[b]

invFromSound2 ==
    \A b \in replicas, r \in replicas :
        b \in from[r] /\ is_byzantine[r] = "false" => predecisions[r] = predecisions[b] \/ is_byzantine[b] = "true"

invConfirmDifferentValComplete ==
    \A r1 \in replicas, r2 \in replicas :
        (/\ is_byzantine[r1] = "false"
        /\ is_byzantine[r2] = "false"
        /\ predecisions[r1] # predecisions[r2]
        /\ Cardinality(from[r1]) \geq (Cardinality(replicas) - t0)
        /\ Cardinality(from[r2]) \geq (Cardinality(replicas) - t0)
        /\ confirmed[r1] = "true"
        /\ confirmed[r2] = "true")
        => confirmDifferentVal(r1, r2)

invConfirmDifferentValSound1 ==
    \A r1 \in replicas, r2 \in replicas :
        confirmDifferentVal(r1, r2)
        => /\ Cardinality(from[r1]) \geq (Cardinality(replicas) - t0)
           /\ Cardinality(from[r2]) \geq (Cardinality(replicas) - t0)
           /\ predecisions[r1] # predecisions[r2]

invConfirmDifferentValSound2 ==
    \A r1 \in replicas, r2 \in replicas :
        confirmDifferentVal(r1, r2)
        => \E r \in replicas : r \in from[r1] /\ r \in from[r2] (* nonempty intersection *)

invConfirmDifferentValSound3 ==
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

invLCsConflictComplete ==
    \A r \in replicas : 
        (/\ confirmed[r] = "true"
        /\ is_byzantine[r] = "false"
        /\ Cardinality(obtainedLightCertificates[r]) \geq Cardinality(replicas)) => (SomeConfirmDifferentVal => light_certificates_conflict(r))

invLCsConflictSound ==
    \A r \in replicas :
        light_certificates_conflict(r)
        => SomeConfirmDifferentVal 


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
    
(* Other properties *)

(* 1. if f < t0 then there is no proof of culpability *)

(* 2. if f >= t0 then ... *)

(* 3. if all act honest then there is no proof of culpability 
- or if more than x act honest then no proof of culpability *)

(* TODO! *)
    

=============================================================================