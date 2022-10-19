----------------------------- MODULE SimpleAC ----------------------------

EXTENDS Integers, Sequences, FiniteSets, Naturals, TLC

CONSTANTS
    replicas,
    values_all

symm == Permutations(replicas) \union Permutations(values_all)

VARIABLES
    is_byzantine,
    predecisions, 
    confirmed,
    certificate,
    obtainedCertificates,
    proof, (* of culpability *)
    msgs,
    rState

values_all_opt == {"none"} \cup values_all

divide_by_three_ceil(m) == CHOOSE k \in 0..m: 3*(k-1) < m /\ m \leq 3*k

n == Cardinality(replicas)
t0 == divide_by_three_ceil(n) - 1
f == Cardinality({p \in replicas : is_byzantine[p] = "true"})

Messages ==
    [type : {"SUBMIT"}, value : values_all, signed : replicas, to : replicas]
    \cup
    [type: {"CERTIFICATE"}, value : values_all, signed : replicas, certificate : SUBSET(replicas), to : replicas] 


TypeOK == 
    /\ is_byzantine \in [replicas -> {"true", "false"}] 
    /\ predecisions \in [replicas -> values_all_opt] 
    /\ confirmed \in [replicas -> {"true", "false"}]
    /\ certificate \in [replicas -> SUBSET(replicas)]
    /\ obtainedCertificates \in [replicas -> SUBSET(Messages)]
    /\ proof \in [replicas -> SUBSET(replicas)]
    /\ rState \in [replicas -> {"none", "submitted", "confirmed", "lc-complete", "full-bcast", "done"}]
    /\ msgs \in SUBSET(Messages)

Init == 
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ predecisions \in [replicas -> values_all]
    /\ confirmed = [r \in replicas |-> "false"]
    /\ certificate = [r \in replicas |-> {}]
    /\ obtainedCertificates = [r \in replicas |-> {}]
    /\ proof = [r \in replicas |-> {}]
    /\ rState = [r \in replicas |-> "none"]
    /\ msgs = {}

BroadcastSubmit(r) ==
    LET submit_msgs == {[type |-> "SUBMIT", value |-> predecisions[r], signed |-> r, to |-> rcv] : rcv \in replicas }
    IN msgs' = msgs \cup submit_msgs

ByzantineBroadcastSubmit(sender) ==
    LET others == replicas \ {sender}
        valuesForOthers == [others -> values_all]
    IN \E g \in valuesForOthers : 
      /\ \E a, b \in others:
        /\ a # b 
        /\ g[a] # g[b]
      /\ msgs' = msgs \cup {[type |-> "SUBMIT", value |-> g[r], signed |-> sender, to |-> r] : r \in others}

BroadcastCertificate(r) ==
    msgs' = msgs \cup {[type |-> "CERTIFICATE", value |-> predecisions[r], signed |-> r, certificate |-> certificate[r], to |-> rcv] : rcv \in replicas}

submit(r) ==
    /\ r \in replicas
    /\ rState[r] = "none"
    /\ is_byzantine[r] = "false"
    /\ BroadcastSubmit(r)
    /\ rState' = [rState EXCEPT ![r] = "submitted"]
    /\ UNCHANGED <<  proof, predecisions, is_byzantine, certificate, obtainedCertificates >>

submitByzantine(r) ==
    /\ r \in replicas
    /\ rState[r] = "none"
    /\ is_byzantine[r] = "true"
    /\ ByzantineBroadcastSubmit(r)
    /\ rState' = [rState EXCEPT ![r] = "submitted"]
    /\ UNCHANGED <<  proof, predecisions, is_byzantine, certificate, obtainedCertificates >>

receiveSubmit(r) ==
    /\ rState[r] \in {"none", "submitted"}
    /\ r \in replicas
    /\ \E m \in msgs :
        /\ m.type = "SUBMIT"
        /\ m.to = r
        /\ m.value = predecisions[r]
        /\ LET s == m.signed
        IN  /\ certificate' = [certificate EXCEPT ![r] = certificate[r] \cup {s}]
            /\ msgs' = msgs \ {m}
            /\ UNCHANGED <<  proof, predecisions, is_byzantine, rState, obtainedCertificates >>

confirm(r) == 
    /\ r \in replicas
    /\ confirmed[r] = "false"
    /\ rState[r] = "submitted"
    /\ Cardinality(certificate[r]) \geq (n - t0)
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ rState' = [rState EXCEPT ![r] = "confirmed"]
    /\ BroadcastCertificate(r)
    /\ UNCHANGED <<  proof, predecisions, is_byzantine, obtainedCertificates >>

receiveCertificate(r) ==
    \E m \in msgs:
        /\ m.type = "CERTIFICATE"
        /\ m.to = r
        /\ obtainedCertificates' = [obtainedCertificates EXCEPT ![r] = obtainedCertificates[r] \cup {m}]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED <<  proof, predecisions, is_byzantine, rState, certificate >> 


certificatesConflict(r, c1, c2) ==
    /\ c1 \in obtainedCertificates[r]
    /\ c2 \in obtainedCertificates[r]
    /\ c1.value # c2.value

extractProof(r, c1, c2) == 
    LET c1intersectionc2 == c1.certificate \intersect c2.certificate
    IN /\ \E rep \in c1intersectionc2 : ~ (rep \in proof[r])
       /\ proof' = [proof EXCEPT ![r] = proof[r] \union c1intersectionc2]
    
proveCulpability(r) ==
    /\ r \in replicas
    /\ rState[r] \in {"confirmed", "proved"}
    /\ \E c1, c2 \in obtainedCertificates[r] :
       /\ certificatesConflict(r, c1, c2)
       /\ extractProof(r, c1, c2)
    /\ rState' = [rState EXCEPT ![r] = "proved"]
    /\ UNCHANGED <<  predecisions, is_byzantine, rState, obtainedCertificates, certificate, msgs >>
   

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

Next == \E r \in replicas : 
            \/ submit(r)
            \/ receiveSubmit(r)
            \/ confirm(r)
            \/ receiveCertificate(r)
            \/ proveCulpability(r)
            \/ submitByzantine(r)


=============================================================================