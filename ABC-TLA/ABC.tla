----------------------------- MODULE ABC ----------------------------

EXTENDS Naturals, AccountableConfirmer

(* ABC refines BC *)

VARIABLES 
    proposals,
    proposals_set,
    decisions,
    states

ABCTypeOK == 
    /\ states \in [replicas -> {"working", "proposed", "predecided", "submitted", "decided", "detected"}]
    /\ proposals \in [replicas -> values_all]
    /\ proposals_set \subseteq values_all
    /\ TypeOK

-----------------------------------------------------------------------------
(*                          actions                                        *)
-----------------------------------------------------------------------------

propose(r) ==
    /\ states[r] = "working"
    /\ states' = [states EXCEPT ![r] = "proposed"]
    /\ proposals_set' = proposals_set \cup {proposals[r]}
    /\ 
    /\ UNCHANGED (<< proposals, decisions, is_byzantine >> \o vars)

predecide_random(r) ==
    \E f \in [replicas -> proposals_set] : predecisions' = [predecisions EXCEPT ![r] = f[r]]

ConsensusPreCond ==
    LET byzantines == {r \in replicas : is_byzantine[r] = "true"}
    IN ~ (Cardinality(byzantines) \geq t0 + 1)

predecide(r) ==
    /\ states[r] = "proposed"
    /\ predecisions[r] = "none"
    /\ \A p \in replicas : states[p] /= "working"
    /\ states' = [states EXCEPT ![r] = "predecided"]
    /\ \/ /\ ConsensusPreCond
          /\ predecisions' = [predecisions EXCEPT ![r] = CHOOSE val \in proposals_set : TRUE] (* TODO: byzantines can still decide anything*)
       \/ /\ ~ ConsensusPreCond
          /\ predecide_random(r)
    /\ UNCHANGED << proposals, proposals_set, decisions, is_byzantine >>    

submitABC(r) ==
    /\ states[r] = "predecided"
    /\ \E v \in values_all : 
        /\ v = predecisions[r]
        /\ submit(r, v)
    /\ states' = [states EXCEPT ![r] = "submitted"]
    /\ UNCHANGED << proposals, proposals_set, predecisions, decisions, is_byzantine >> 

decide(r) ==
    /\ states[r] = "submitted"
    /\ \E v \in values_all :
        /\ v = predecisions[r]
        /\ confirm(r, v)
        /\ decisions' = [decisions EXCEPT ![r] = v]
    /\ states' = [states EXCEPT ![r] = "decided"]
    /\ UNCHANGED << proposals, proposals_set, predecisions, is_byzantine >> 

detect(r) ==
    /\ states[r] = "decided"
    /\ prove_culpability(r)
    

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

BC == INSTANCE ByzantineConsensus

ABCInit ==
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ predecisions = [r \in replicas |-> "none"] (* must be none initially! *)
    /\ confirmed = [r \in replicas |-> "false"]
    /\ from = [r \in replicas |-> {}]
    /\ lightCertificate = [r \in replicas |-> "none"]
    /\ fullCertificate = [r \in replicas |-> {}]
    /\ obtainedLightCertificates = [r \in replicas |-> {}]
    /\ obtainedFullCertificates = [r \in replicas |-> {}]
    /\ rLog = [r \in replicas |-> {}]
    /\ proof = [r \in replicas |-> {}]
    /\ rState = [r \in replicas |-> "none"]
    /\ proposals \in [replicas -> values_all]
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ proposals_set = {}
    /\ decisions = [r \in replicas |-> "none"]
    /\ states = [r \in replicas |-> "working"]
    (* Init /\ BC!Init *)
    (* but predecisions should be "none" for every replica *)

ABCNext ==
    \E r \in replicas:
        \/ propose(r)
        \/ predecide(r)
        \/ submitABC(r)
        \/ updateCertificates(r)
        \/ decide(r) (* we can replace propose and decide with BC!Next*)
        \/ bcast_full_cerificate(r)
        \/ detect(r)

ABCvars == << proposals, proposals_set, predecisions, decisions, states, is_byzantine,
confirmed, from, lightCertificate, fullCertificate, obtainedLightCertificates, 
obtainedFullCertificates, rLog, proof, rState >>

ABCSpec == ABCInit /\ [][ABCNext]_ABCvars

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------


=============================================================================
