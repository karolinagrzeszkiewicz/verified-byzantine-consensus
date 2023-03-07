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

### Model assumptions

1. **Asynchrony** – we assume that the processes can experience arbitrary delays in performing actions and in particular in receiving messages. We have two separate transitions for sending a message (whereby a message gets added to the pool of all unreceived messages) and for receiving a message (whereby a message is removed from the pool of messages and the receiving replica performs some bookkeeping)
2. **Byzantine Consensus** – if the number of faulty processes is smaller than $t_0$ then the predecided values of all of the honest processes are the same (Agreement property of Byzantine Consensus), otherwise the predecided values are randomly assigned values from the set of possible values
3. **Cryptography** – in this model we abstract away the cryptographic methods and challenges, namely the `signed` field of a message always corresponds to the process that actually sent the message, and signatures cannot be forged. 

### Model transitions (following the protocol)

The following transitions can hold for both a byzantine and a non-byzantine process:
* *submit* – broadcast a submit message to all other processes containg the predecided value (where the broadcast transition inserts the corresponding message in the pool of messages for all of the intended recipients), can be taken if the process is in the intial state and after the broadcast it switches to the 'submitted' state
* *receiveSubmit* – a process removes a submit message for which it is the intended recipient from the pool of messages and performs bookkeeping i.e. if the value in the submit message is the same as its predecided value then it adds the sender of that message to its `certificate` set, otherwise it ignores the contents of the message. This transition can be taken in the initial or 'submitted' state
* *confirm* – this transition can hold for a process that has not confirmed any value yet, but has submitted a value i.e. is in the 'submitted' state, and its certificate has reached the size of $n - t_{0}$ i.e. it has received at least $n - t_{0}$ submit messages for its predecided value. If this holds, then the process can broadcast its certificate i.e. its value with the set of processes that 'endorsed' that value (again by inserting it into the pool of messages) and move to the 'confirmed' state.
* *receiveCertificate* – if there is a certificate message in the pool of which the process is the intended recipient it appends the message to its set of `obtainedCertificates`, and removes it from the pool of messages.
* *proveCulpability* – if a process has two conflicting certificates in its `obtainedCertificates` i.e. two certificates for different values, then it extracts a proof of culpability of given processes by finding the intersection of the two sets of processes that 'endorsed' the two values. It saves the intersection as its proof and enters the 'proved' state.

### Model transitions (byzantine)

`submitByzantine` is a transition that is only allowed for a byzantine process as it involves violating the rules of the protocol by submitting values different from what a process has predecided, and possibly different values to different recipients. 

Other deviations from the protocol are not considered – the only other deviations are failures to take some transition action which is equivalent to an arbitrarily long delay and hence will be covered by TLC. Forging certificates is not possible since in a proper implementation of this protocol a certificate corresponds to what is called the 'full-certificate' that contains submit messages signed with the respective processes' private keys.


### Byzantine behaviour

Broadly we could understand Byzantine behavior as any deviation from the protocol, yet we are only concern with the kinds of deviations that are malicious by nature, intended to prevent others from reaching agreement, push other processes to decide 'the wrong value' i.e. value proposed by one of the Byzantines, or in case of accountable consensus we can also consider a subset of the above-mentioned actions where the malicious action is ingeniously covered up to avoid being detetected by the Accountable Confirmer. 

### Accountability

1. Soundness – if a process get caught then the process must have behaved byzantine
2. Completeness – if a process behaved byzantine then it gets caught eventually

However, completeness does not hold. This is because being in the proof of culpability collected by some process the byzantine process must be in the two conflicting certificates. However, if the number of byzantine processes is greater than $t_{0} + 1$ sometimes a process might behave byzantine but not with respect to exactly the two processes whose certificates were found to conflict with each other (other byzantines have behaved byzantine too). Furthermore, the process might send values that no honest process has predecided in which case its submit messages get ignored and hence its byzantine behaviour is not detected.

Which leads to undetected byzantine behaviour:

```tla
UndetectedByzantineBehaviour ==
    \A r \in replicas : behavedByzantineSentUnknownValues(r)
    => \A p \in replicas \ {r} : is_byzantine[p] = "false" => ~ (r \in proof[p])
```
    
and no confirmation:

```tla
NonConfirmationCausedByByzantineBehaviour ==
   (/\ (\A r \in replicas : is_byzantine[r] = "true" => behavedByzantineSentUnknownValues(r))
    /\ ~ ConsensusPreCond)
    => (\A p \in replicas : is_byzantine[p] = "false" => rState[p] # "confirmed")
```

Since if we have f > t0 byzantines, then we have n-f < n-t0 honest
so to get |from| >= n-t0 submit messages for its predecided value each honest 
must also receive some submit messages for this value from some byzantines 
but in this scenario the byzantines send messages no honest replica has predecided
so no honest confirms

### Non-termination

### Invariants