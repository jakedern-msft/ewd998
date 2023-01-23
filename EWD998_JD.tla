---- MODULE EWD998_JD ----
EXTENDS Integers, TLC

CONSTANT NumberOfNodes

\* Map from node -> is working
VARIABLE 
    NodeWorking,
    NodeColor,
    NodeCounter,
    Network,
    TerminationDetected,
    TokenPosition,
    TokenColor,
    TokenValue

vars == << NodeWorking, NodeColor, NodeCounter, Network, TerminationDetected, TokenPosition, TokenColor, TokenValue >>
Nodes == 1..NumberOfNodes

ATD == INSTANCE A2

\* Termination definition
Terminated == 
    /\ TokenPosition = 1
    /\ TokenColor = "White"
    /\ NodeCounter[1] + TokenValue = 0
    /\ NodeColor[1] = "White"
    /\ NodeWorking[1] = FALSE

\* Action Allowable state change
DetectTermination == 
    /\ TerminationDetected' = Terminated
    /\ UNCHANGED << NodeWorking, NodeColor, NodeCounter, Network, TokenPosition, TokenColor, TokenValue >>

\* Initial state
Init == 
    /\ NodeWorking = [node \in Nodes |-> TRUE]
    /\ NodeCounter = [node \in Nodes |-> 0]
    /\ NodeColor = [node \in Nodes |-> "Black"]
    /\ Network = [node \in Nodes |-> 0]
    /\ TerminationDetected = FALSE
    /\ TokenPosition = 1
    /\ TokenValue = 0
    /\ TokenColor = "White"

InitiateProbe == 
    /\ TokenPosition = 1
    /\ ~Terminated
    /\ TokenValue' = 0
    /\ TokenPosition' = TokenPosition + 1
    /\ TokenColor' = "White"
    /\ NodeColor' = [NodeColor EXCEPT ![1] = "White"]
    /\ UNCHANGED << NodeWorking, NodeCounter, Network, TerminationDetected >>

\* Possible actions in the system
NodeFinishesWork(node) ==
    /\ NodeWorking' = node :> FALSE @@ NodeWorking
    /\ UNCHANGED << NodeColor, NodeCounter, TokenColor, TokenValue, Network, TerminationDetected, TokenPosition >>    

NodePassesToken(node) ==
    /\ node # 1
    /\ TokenPosition = node
    /\ NodeWorking[node] = FALSE
    /\ IF TokenPosition = NumberOfNodes THEN TokenPosition' = 1 ELSE TokenPosition' = node + 1
    /\ TokenValue' = TokenValue + NodeCounter[node]
    /\ NodeColor' = [NodeColor EXCEPT ![node] = "White"]
    /\ UNCHANGED << Network, TerminationDetected, NodeWorking, NodeCounter, TokenColor >>

NodeReceivesToken(node) ==
    /\ TokenPosition = node
    /\ IF NodeColor[node] = "Black" THEN TokenColor' = "Black" ELSE UNCHANGED TokenColor
    /\ UNCHANGED << Network, TerminationDetected, NodeWorking, NodeCounter, TokenValue, TokenPosition, NodeColor >>

NodeReceives(destinationNode) == 
    /\ Network[destinationNode] > 0
    /\ Network' = [Network EXCEPT ![destinationNode] = Network[destinationNode] - 1]
    /\ NodeCounter' = [NodeCounter EXCEPT ![destinationNode] = @ - 1]
    /\ NodeColor' = [NodeColor EXCEPT ![destinationNode] = "Black"]
    /\ NodeWorking' = [NodeWorking EXCEPT ![destinationNode] = TRUE]
    /\ UNCHANGED << TerminationDetected, TokenPosition, TokenColor, TokenValue >>

SendMessage(sourceNode) ==
    /\ NodeWorking[sourceNode] = TRUE
    /\ NodeCounter' = [NodeCounter EXCEPT ![sourceNode] = @ + 1]
    /\ \E destinationNode \in Nodes : Network' = [Network EXCEPT ![destinationNode] = Network[destinationNode] + 1]
    /\ UNCHANGED  << NodeWorking, TerminationDetected, TokenPosition, NodeColor, TokenColor, TokenValue >>

Next == 
    \/ DetectTermination
    \/ InitiateProbe
    \/  \E node \in Nodes :
            \/ NodeFinishesWork(node)
            \/ SendMessage(node)
            \/ NodeReceives(node)
            \/ NodePassesToken(node)

NetworkIsFinite == 
    \A node \in Nodes : Network[node] <= 5

WorkIsFinite == 
    \A node \in Nodes : NodeCounter[node] <= 5

NetworkIsValid == 
    \A node \in Nodes : Network[node] >= 0

TypesOk == 
    /\ NodeWorking \in [Nodes -> {TRUE, FALSE}]
    /\ NodeCounter \in [Nodes -> Int]
    /\ NodeColor \in [Nodes -> {"White", "Black"}]
    /\ TokenColor \in {"White", "Black"}
    /\ TokenValue \in Int
    /\ TokenPosition \in Nodes
    /\ Network \in [Nodes -> Nat]
    /\ TerminationDetected \in {TRUE, FALSE}

NodesStarWorkingAfterReceivingMessage == 
    /\ [][\A node \in Nodes : Network'[node] = Network[node] - 1 => NodeWorking'[node] = TRUE]_vars

TerminationDetectionIsCorrect ==
    /\ TerminationDetected => Terminated
    /\ TerminationDetected => \A node \in Nodes : NodeWorking[node] = FALSE
    /\ TerminationDetected => \A node \in Nodes : Network[node] = 0

TerminationIsEventuallyDetected == 
    <>Terminated ~> TerminationDetected

TerminationDetectionIsStable ==
    [][TerminationDetected => TerminationDetected']_TerminationDetected

\* Fixes temporal issue, fairness
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

THEOREM Spec => ATD!Spec

Correct ==
    /\ [](ATD!TypesOk)
    /\ [](TypesOk)
    /\ [](TerminationDetectionIsCorrect)
    /\ ATD!TerminationIsEventuallyDetected
    /\ ATD!TerminationDetectionIsStable
====