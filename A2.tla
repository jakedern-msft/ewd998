---- MODULE A2 ----
EXTENDS Integers, TLC

CONSTANT NumberOfNodes

\* Map from node -> is working
VARIABLE NodeWorking, Network, TerminationDetected

Nodes == 1..NumberOfNodes

\* Termination definition
Terminated == 
    /\ \A node \in Nodes : Network[node] = 0
    /\ \A node \in Nodes : NodeWorking[node] = FALSE

\* Action Allowable state change
DetectTermination == 
    /\ TerminationDetected' = Terminated
    /\ UNCHANGED << Network, NodeWorking >>

\* Initial state
Init == 
    /\ NodeWorking = [node \in Nodes |-> TRUE]
    /\ Network = [node \in Nodes |-> 0]
    /\ TerminationDetected = FALSE

\* Possible actions in the system
NodeFinishesWork(node) ==
    /\ NodeWorking' = node :> FALSE @@ NodeWorking
    /\ UNCHANGED << Network, TerminationDetected >>

NodeReceives(destinationNode) == 
    /\ Network[destinationNode] > 0
    /\ Network' = [Network EXCEPT ![destinationNode] = Network[destinationNode] - 1]
    /\ NodeWorking' = [NodeWorking EXCEPT ![destinationNode] = TRUE]
    /\ UNCHANGED << TerminationDetected >>

SendMessage(sourceNode) ==
    /\ NodeWorking[sourceNode] = TRUE
    /\ \E destinationNode \in Nodes : Network' = [Network EXCEPT ![destinationNode] = Network[destinationNode] + 1]
    /\ UNCHANGED  << NodeWorking, TerminationDetected >>

Next == 
    \/ DetectTermination
    \/ \E node \in Nodes :
        \/ NodeFinishesWork(node)    
        \/ SendMessage(node)
        \/ NodeReceives(node)

NetworkIsFinite == 
    \A node \in Nodes : Network[node] <= 3

NetworkIsValid == 
    \A node \in Nodes : Network[node] >= 0

TypesOk == 
    /\ NodeWorking \in [Nodes -> {TRUE, FALSE}]
    /\ Network \in [Nodes -> Nat]
    /\ TerminationDetected \in {TRUE, FALSE}

vars == << Network, NodeWorking, TerminationDetected >>
NodesStarWorkingAfterReceivingMessage == 
    /\ [][\A node \in Nodes : Network'[node] = Network[node] - 1 => NodeWorking'[node] = TRUE]_vars

TerminationDetectionIsCorrect ==
    TerminationDetected => Terminated

TerminationIsEventuallyDetected == 
    <>Terminated ~> TerminationDetected

TerminationDetectionIsStable ==
    [][TerminationDetected => TerminationDetected']_TerminationDetected

\* Fixes temporal issue, fairness
Spec == 
    /\ Init
    /\ [][Next]_vars

====