----------------------------- MODULE ByzantineConsensus ----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    replicas,
    values_all

values_all_opt == {"none"} \cup values_all

t0 == Cardinality(replicas) \div 3 (* floor division *)

VARIABLES 
    proposals,
    proposals_set,
    decisions,
    states,
    is_byzantine

TypeOK == 
    /\ proposals \in [replicas -> values_all]
    /\ proposals_set \subseteq values_all
    /\ decisions \in [replicas -> values_all_opt]
    /\ states \in [replicas -> {"working", "proposed", "decided"}]
    /\ is_byzantine \in [replicas -> {"true", "false"}]

-----------------------------------------------------------------------------
(*                          actions                                        *)
-----------------------------------------------------------------------------

ConsensusPreCond ==
    LET byzantines == {r \in replicas : is_byzantine[r] = "true"}
    IN ~ (Cardinality(byzantines) \geq t0 + 1)

decide_random(r) ==
    \E f \in [replicas -> proposals_set] : decisions' = [decisions EXCEPT ![r] = f[r]]

propose(r) ==
    /\ states[r] = "working"
    /\ states' = [states EXCEPT ![r] = "proposed"]
    /\ proposals_set' = proposals_set \cup {proposals[r]}
    /\ UNCHANGED << proposals, decisions, is_byzantine >>

decide(r) ==
    /\ states[r] = "proposed"
    /\ decisions[r] = "none"
    /\ \A p \in replicas : states[p] /= "working"
    /\ states' = [states EXCEPT ![r] = "decided"]
    /\ \/ /\ ConsensusPreCond
          /\ decisions' = [decisions EXCEPT ![r] = CHOOSE val \in proposals_set : TRUE] (* TODO: byzantines can still decide anything*)
       \/ /\ ~ ConsensusPreCond
          /\ decide_random(r)
    /\ UNCHANGED << proposals, proposals_set, is_byzantine >>
    

-----------------------------------------------------------------------------
(*                          transitions                                     *)
-----------------------------------------------------------------------------

Init ==
    /\ proposals \in [replicas -> values_all]
    /\ is_byzantine \in [replicas -> {"true", "false"}]
    /\ proposals_set = {}
    /\ decisions = [r \in replicas |-> "none"]
    /\ states = [r \in replicas |-> "working"]

Next == \E r \in replicas : propose(r) \/ decide(r)

vars == << proposals, proposals_set, is_byzantine, decisions, states >>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*                          invariants and properties                       *)
-----------------------------------------------------------------------------

Validity ==
    LET correct == {r \in replicas : is_byzantine[r] = "false"}
    IN ConsensusPreCond => 
        (\E v \in values_all : (\A c \in correct : proposals[c] = v)
        => \A r \in replicas : (states[r] = "decided" => decisions[r] = v))

Agreement ==
    LET correct == {r \in replicas : is_byzantine[r] = "false"}
    IN ConsensusPreCond => \A c1, c2 \in correct : 
        (/\ decisions[c1] /= "none" /\ decisions[c2] /= "none") => (decisions[c1] = decisions[c2])

=============================================================================
