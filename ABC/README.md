# Accountable Byzantine Consensus

This repository contains my work in progress in formalizing [Accountable Byzantine Consensus (ABC)](https://eprint.iacr.org/2021/1169) in TLA+.

The ABC transformation consists of taking any protocol which implements Byzantine consensus (BFT) and plugging in the respective processes' values decided in the protocol into the Accountable Confirmer Algorithm which enables the honest processes the detect some byzantine behaviour under some circumstances (more about this below). The **ByzantineConsensus** module contains a specification of a generalised protocol which satsifies Byzantine consensus (i.e. ensures the agreement of honest processes when the number of byzantines is smaller than the threshold and does not guarantee agreement otherwise), and **SimpleAC** specifies the Accountable Confirmer protocol. Composing the two together is a work in progress. There is also **AccountableConfirmer** which refines **SimpleAC** by modeling the cryptography used in the actual protocol and introducing an extra layer of lightweight certificate broadcast intended to reduce the communication complexity by a factor of n in case consensus is achieved in the BFT.

## SimpleAC (Accountable Confirmer)

There are two constants which need to be declared in the configuration file to run the TLC model checker:
```tla
CONSTANTS
    replicas,
    values_all
```
Where `replicas` is the set of all processes participating in the protocol, and `values_all` is the pool of all possible values that can be submitted, confirmed etc.

```tla
VARIABLES
    is_byzantine,
    predecisions, 
    confirmed,
    certificate,
    obtainedCertificates,
    proof,
    msgs,
    rState,
    submitted,
    conflictingCertificates
```

Where:
* `is_byzantine` is a function from replicas to 'booleans' indicating whether a given replica is byzantine
* `predecisions` is a function from replicas to possible values assigning to each replica the value it has predecided (e.g. in the BFT) and it is about to submit assuming it follows the rules of the protocol
* `confirmed` is a function from replicas to 'booleans' indicating whether a given replica has confirmed a value or not (refer to the *confirm* transition of the protocol)
* `certificate` is a function from replicas to their certificates, where a replica's certificate is the set of replicas that have sent it a *submit* message with the same value the replica has predecided
* `obtainedCertificates` is a function from replicas to the certificate messages they have collected i.e. each replica collects the certificate messages from other replicas for their respective predecided values and containing their certificates for those values
* `proof` is a function from replicas to the powerset of replicas mapping each replica to the set of replicas it has detected as violating the protocol
* `msgs` is the set of all messages currently in the pool (when a message is received it gets removed from the pool, this is to model asynchrony)
* `rState` is a function from replicas to their possible states reflecting which phase of the protocol they are in
* `submitted` is a function from sender replicas to a function from receiver replicas to values i.e. `submitted[sender][receiver]` is the value that the sender has submitted to the receiver in the *submit* phase of the protocol, used merely for bookkeeping
* `conflictingCertificates` is a function from replicas to the powerset of replicas mapping each replica to either an empty set (if it hasn't detected any conflicting certificates and thus hasn't detected any guilty nodes) or the two replicas whose certificates it found to conflict with each other (and thus used to construct its proof of culpability)

### Assumptions behind the model

### Asynchrony

### Byzantine behaviour

### Accountability

### Invariants