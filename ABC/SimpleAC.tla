----------------------------- MODULE simpleAC ----------------------------

EXTENDS Integers, Sequences, FiniteSets, Naturals, TLC

-----------------------------------------------------------------------------
(*                          predeclared constants                           *)
-----------------------------------------------------------------------------

CONSTANTS
    replicas,
    values_all

symm == Permutations(replicas) \union Permutations(values_all)

-----------------------------------------------------------------------------
(*                          variables                                       *)
-----------------------------------------------------------------------------

VARIABLES
    is_byzantine,
    predecisions, 
    confirmed,
    certificate,
    obtainedCertificates,
    proof, (* of culpability *)
    msgs,
    rState,
    submitted,
    conflictingCertificates

values_all_opt == {"none"} \cup values_all

divide_by_three_ceil(m) == CHOOSE k \in 0..m: 3*(k-1) < m /\ m \leq 3*k

n == Cardinality(replicas)
t0 == divide_by_three_ceil(n) - 1
f == Cardinality({p \in replicas : is_byzantine[p] = "true"})
h == Cardinality({p \in replicas : is_byzantine[p] = "false"})

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
    /\ rState \in [replicas -> {"none", "submitted", "confirmed", "proved"}]
    /\ msgs \in SUBSET(Messages)
    /\ submitted \in [replicas -> [replicas -> values_all]]
    /\ conflictingCertificates \in [replicas -> SUBSET(replicas)]

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

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
      /\ submitted' = [submitted EXCEPT ![sender] = [r \in others |-> g[r]]]

BroadcastCertificate(r) ==
    msgs' = msgs \cup {[type |-> "CERTIFICATE", value |-> predecisions[r], signed |-> r, certificate |-> certificate[r], to |-> rcv] : rcv \in replicas}

submit(r) ==
    /\ r \in replicas
    /\ rState[r] = "none"
    /\ is_byzantine[r] = "false"
    /\ BroadcastSubmit(r)
    /\ rState' = [rState EXCEPT ![r] = "submitted"]
    /\ submitted' = [submitted EXCEPT ![r] = [rcv \in replicas \ {r} |-> predecisions[r]]]
    /\ UNCHANGED <<  proof, predecisions, is_byzantine, confirmed, certificate, obtainedCertificates, conflictingCertificates >>

submitByzantine(r) ==
    /\ r \in replicas
    /\ rState[r] = "none"
    /\ is_byzantine[r] = "true"
    /\ ByzantineBroadcastSubmit(r)
    /\ rState' = [rState EXCEPT ![r] = "submitted"]
    /\ UNCHANGED <<  proof, predecisions, is_byzantine, confirmed, certificate, obtainedCertificates, conflictingCertificates >>

receiveSubmit(r) ==
    /\ rState[r] \in {"none", "submitted"}
    /\ r \in replicas
    /\ \E m \in msgs :
        /\ m.type = "SUBMIT"
        /\ m.to = r
        /\ m.value = predecisions[r]
        /\ LET s == m.signed
           IN /\ certificate' = [certificate EXCEPT ![r] = certificate[r] \cup {s}]
              /\ msgs' = msgs \ {m}
              /\ UNCHANGED <<  proof, predecisions, is_byzantine, rState, confirmed, obtainedCertificates, submitted, conflictingCertificates >>

confirm(r) == 
    /\ r \in replicas
    /\ confirmed[r] = "false"
    /\ rState[r] = "submitted"
    /\ Cardinality(certificate[r]) \geq (n - t0)
    /\ confirmed' = [confirmed EXCEPT ![r] = "true"]
    /\ rState' = [rState EXCEPT ![r] = "confirmed"]
    /\ BroadcastCertificate(r)
    /\ UNCHANGED <<  proof, predecisions, is_byzantine, obtainedCertificates, certificate, submitted, conflictingCertificates >>

receiveCertificate(r) ==
    \E m \in msgs:
        /\ m.type = "CERTIFICATE"
        /\ m.to = r
        /\ obtainedCertificates' = [obtainedCertificates EXCEPT ![r] = obtainedCertificates[r] \cup {m}]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED <<  proof, predecisions, is_byzantine, rState, confirmed, certificate, submitted, conflictingCertificates >> 


certificatesConflict(r, c1, c2) ==
    /\ c1 \in obtainedCertificates[r]
    /\ c2 \in obtainedCertificates[r]
    /\ c1.value # c2.value

extractProof(r, c1, c2) == 
    LET c1intersectionc2 == c1.certificate \intersect c2.certificate
    IN proof' = [proof EXCEPT ![r] = c1intersectionc2]
    
proveCulpability(r) ==
    /\ r \in replicas
    /\ rState[r] = "confirmed"
    /\ \E c1, c2 \in obtainedCertificates[r] :
       /\ certificatesConflict(r, c1, c2)
       /\ extractProof(r, c1, c2)
       /\ conflictingCertificates' = [conflictingCertificates EXCEPT ![r] = {c1.signed, c2.signed}]
    /\ rState' = [rState EXCEPT ![r] = "proved"]
    /\ UNCHANGED <<  predecisions, is_byzantine, obtainedCertificates, confirmed, certificate, msgs, submitted >>
   

-----------------------------------------------------------------------------
(*                          inductive specification                         *)
-----------------------------------------------------------------------------

(* predictates for the initial setup *)

(* no. of byzantines =< t0 *)
ConsensusPreCond ==
    LET byzantines == {r \in replicas : is_byzantine[r] = "true"}
    IN (Cardinality(byzantines) \leq t0)

HonestPredecideSameValue ==
    \A r1 \in replicas, r2 \in replicas : 
        (/\ is_byzantine[r1] = "false"
         /\ is_byzantine[r2] = "false")
        => predecisions[r1] = predecisions[r2]

(* in case we initialise predecisions with values from the BFT: 
    if less than one third are faulty then the honest predecide the same value *)
Consensus ==
    ConsensusPreCond => HonestPredecideSameValue

Init == 
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ predecisions \in [replicas -> values_all]
    /\ confirmed = [r \in replicas |-> "false"]
    /\ certificate = [r \in replicas |-> {}]
    /\ obtainedCertificates = [r \in replicas |-> {}]
    /\ proof = [r \in replicas |-> {}]
    /\ rState = [r \in replicas |-> "none"]
    /\ msgs = {}
    /\ conflictingCertificates = [r \in replicas |-> {}]
    /\ submitted = [r \in replicas |-> [p \in replicas |-> {}]]
    /\ Consensus

Next == \E r \in replicas : 
            \/ submit(r)
            \/ receiveSubmit(r)
            \/ confirm(r)
            \/ receiveCertificate(r)
            \/ proveCulpability(r)
            \/ submitByzantine(r)

vars == << is_byzantine, predecisions, confirmed, certificate, obtainedCertificates, proof, msgs, rState, submitted, conflictingCertificates >>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*                   classification of byzantine behaviour                  *)
-----------------------------------------------------------------------------

behavedByzantine(r) ==
    \E v1 \in {submitted[r][to] : to \in replicas \ {r}}, v2 \in {submitted[r][to] : to \in replicas \ {r}} : v1 # v2

SentUnknownValues(r) ==
    \A v \in {submitted[r][to] : to \in replicas \ {r}} : 
        ~ (\E p \in replicas :
            /\ is_byzantine[p] = "false"
            /\ predecisions[p] = v)

SentUnknownValuesExceptMaxOne(r) ==
    ~ (\E v1, v2 \in {submitted[r][to] : to \in replicas} : 
        /\ (\E p1 \in replicas :
                /\ is_byzantine[p1] = "false"
                /\ predecisions[p1] = v1)
        /\ (\E p2 \in replicas :
                /\ is_byzantine[p2] = "false"
                /\ predecisions[p2] = v2)
        /\ v1 # v2)

(* this kind of byzantine behaviour is a subset of behavedByzantine(r),
    and it is the kind of behaviour that 
    1. causes the protocol to never terminate if ConsensusPreCond does not hold i.e no consensus ib BFT
    2. is never detected because honest replicas ignore submit messages with values different
       from their respective predecided values*)
behavedByzantineSentUnknownValues(r) ==
    /\ behavedByzantine(r)
    /\ SentUnknownValues(r)
    
(* Question : is this behavior dangerous? Yes, if byzantines can intentionally behave in the way described above,
yet this requires the knowledge of the values predecided by others or otherwise knowledge of which values are more
likely to be predecided and a sufficiently big pool of other values 'unlikely to be predecided' to choose from *)

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

THEOREM Spec => TypeOK

(* Accountability *)

(* completeness: if behaved byzantine then eventually detected 
    where "eventually" means that once an honest replica r1 has a proof of culpability
    then the replica that has behaved byzantine must be in it *)

(* note: it holds only if we have a maximum of 2 possible values and a maximum of 2 honest replicas *)

confirmDifferentVal(p, q) ==
    \E vp \in values_all, vq \in values_all:
        /\ is_byzantine[p] = "false"
        /\ is_byzantine[q] = "false"
        /\ p # q
        /\ vp # vq
        /\ confirmed[p] = "true"
        /\ confirmed[q] = "true"
        /\ predecisions[p] = vp
        /\ predecisions[q] = vq

CompletenessPrecond ==
    (Cardinality(values_all) \leq 2 /\ h \leq 2)

AccountabilityCompleteness ==
    (\A r1, r2 \in replicas : 
               (/\ is_byzantine[r1] = "false"
                /\ behavedByzantine(r2)
                /\ \E p \in replicas, q \in replicas : confirmDifferentVal(p, q)
                /\ rState[r1] = "proved") 
                => r2 \in proof[r1])

AccountabilityPossiblyIncomplete ==
    (\A r1, r2 \in replicas : 
               (/\ is_byzantine[r1] = "false"
                /\ behavedByzantine(r2)
                /\ \E v \in values_all : (\A r \in conflictingCertificates[r1] : submitted[r2][r] = v) (* r2 sent the same value to them *)
                /\ rState[r1] = "proved") 
                => ~ (r2 \in proof[r1]))

(* actual accountability completeness and soundness properties *)

AccountabilityRestrictedCompleteness ==
    CompletenessPrecond => AccountabilityCompleteness

AccountabilityIncompleteness ==
    ~ CompletenessPrecond => AccountabilityPossiblyIncomplete

(* soundness: if detected by an honest process then must have behaved byzantine *)
AccountabilitySoundness ==
    \A r1 \in replicas : is_byzantine[r1] = "false"
    => \A r2 \in proof[r1] : behavedByzantine(r2)

Accountability ==
    (\E p \in replicas, q \in replicas : confirmDifferentVal(p, q))
    => \A r \in replicas : 
       (/\ is_byzantine[r] = "false"
        /\ rState[r] = "proved")
        => Cardinality(proof[r]) \geq t0 + 1

(* Undetected byzantine behaviour *)
    
UndetectedByzantineBehaviour ==
    \A r \in replicas : behavedByzantineSentUnknownValues(r)
    => \A p \in replicas \ {r} : is_byzantine[p] = "false" => ~ (r \in proof[p])
    
(* termination and confirmation *)

(* if we have f > t0 byzantines, then we have n-f < n-t0 honest
    so to get |from| >= n-t0 submit messages for its predecided value each honest 
    must also receive some submit messages for this value from some byzantines 
    but in this scenario the byzantines send messages no honest replica has predecided
    so no honest confirms *)

NonConfirmationCausedByByzantineBehaviour ==
   (/\ (\A r \in replicas : is_byzantine[r] = "true" => behavedByzantineSentUnknownValues(r))
    /\ ~ ConsensusPreCond)
    => (\A p \in replicas : is_byzantine[p] = "false" => rState[p] # "confirmed")

(* if f <= t0 and honest agree on the same value then all honest confirm and they never prove culpability 
   since there is no disagreement between certificates (and certificates are uniquely determined to be for the predecided value
   since the majority n-t0 must be for the predecided value) *)

\* ConfirmationWithConsensus ==
\*     (ConsensusPreCond /\ Consensus)
\*     => (\A r \in replicas : is_byzantine[r] = "false"
\*         => <>(rState[r] = "confirm"))

NonTerminationWithConsensus ==
    (ConsensusPreCond /\ Consensus)
    => (\A r \in replicas : is_byzantine[r] = "false"
        => /\ rState[r] # "proved"
           /\ proof[r] = {})

NonTerminationByzantinesActHonest ==
    (/\ \A b \in replicas : is_byzantine[b] = "true" => ~ behavedByzantine(b)
     /\ Consensus)
     => \A r \in replicas : is_byzantine[r] = "false" => rState[r] # "proved" /\ proof[r] = {}

(* if f > t0 and the byzantines decide to behave honest
    then it never happens that all replicas confirm 
    unless all honest decided the same value *)

(* this is another "dangerous behaviour" if the byzantines can prevent the others from deciding,
    but in the f > t0 case we can't expect consensus anyways - but we don't get detection/accountability either! *)
PossibleNonConfirmationByzantinesActHonest ==
    (/\ \A b \in replicas : is_byzantine[b] = "true" => ~ behavedByzantine(b)
     /\ ~ ConsensusPreCond
     /\ ~ HonestPredecideSameValue)
     => ~ (\A r \in replicas : is_byzantine[r] = "false" => confirmed[r] = "true")

=============================================================================