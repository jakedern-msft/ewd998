---- MODULE CRSM ----
EXTENDS TLC, Integers, Sequences

\* A simplified view of a kubernetes resource
K8sResourceType == [
    Exists: BOOLEAN,
    Ready: BOOLEAN
]

\* Custom resource provider state machine
CustomResourceProviderStateMachineStates == { "Inactive", "CreateUpdateResource", "WaitForResourceToBeReady", "CreateUpdatePaused", "Ready" }
CustomResourceProviderStateMachineEvents == { "Update", "Pause" }
CustomResourceProviderStateMachineType == [
    State: CustomResourceProviderStateMachineStates,
    K8sResource: K8sResourceType
]

\* Possible states for a feature operation
FeatureOperationStates == { "Initial", "Pending", "Completed" }
FeatureOperationType == [
    State: FeatureOperationStates,
    Machine: CustomResourceProviderStateMachineType
]

\* Custom resource state machine states and events
CustomResourceStateMachineStates == { "Inactive", "PrepareForCreation", "CreateResources", "WaitForResourceCreation", "PrepareForCreation", "Ready" }
CustomResourceStateMachineEvents == { "Update", "Create"}
CustomResourceStateMachineType == [
    State: CustomResourceStateMachineStates,
    Operations: Seq(FeatureOperationType),
    K8sResource: K8sResourceType
]

\** Initial state for the custom resource state machine
InitialCRSM == [
    State |-> "Inactive",
    Operations |-> << 
        [ State |-> "Initial", Machine |-> [ State |-> "Inactive", K8sResource |-> [ Exists |-> FALSE, Ready |-> FALSE]]],
        [ State |-> "Initial", Machine |-> [ State |-> "Inactive", K8sResource |-> [ Exists |-> FALSE, Ready |-> FALSE]]],
        [ State |-> "Initial", Machine |-> [ State |-> "Inactive", K8sResource |-> [ Exists |-> FALSE, Ready |-> FALSE]]]
    >>,
    K8sResource |-> [ Exists |-> FALSE, Ready |-> FALSE ]
]

\** Variables and types

VARIABLE CRSM

vars == << CRSM >>

TypeOk == 
    /\ CRSM \in CustomResourceStateMachineType
    /\ CRSM.Operations \in Seq(FeatureOperationType)
    /\ CRSM.K8sResource \in K8sResourceType
    /\ Len(CRSM.Operations) = 3

\** Custom resource provider machine actions

CRFP_PauseEvent(machine) ==
    \/ /\ machine.State  = "CreateUpdateResource"
       /\ machine' = [ machine EXCEPT !.State = "CreateUpdatePaused" ]
    \/ /\ machine.State  = "WaitForResourceToBeReady"
       /\ machine' = [ machine EXCEPT !.State = "CreateUpdatePaused" ]

\** Custom Resource State Machine Actions

CRSM_CreateEvent == 
    /\ CRSM.K8sResource.Exists = FALSE
    /\ CRSM' = [ CRSM EXCEPT !.K8sResource.Exists = TRUE ]

CRSM_BecomesActive ==
    /\ CRSM.State = "Inactive"
    /\ CRSM.K8sResource.Exists = TRUE
    /\ CRSM' = [ CRSM EXCEPT !.State = "PrepareForCreation" ]

CRSM_PrepareForCreationTransition ==
    /\ CRSM.State = "PrepareForCreation"
    /\ \A i \in 1..Len(CRSM.Operations): IF CRSM.Operations[i].State = "Pending" THEN CRFP_PauseEvent(CRSM.Operations[i].Machine) ELSE TRUE
    /\ CRSM' = [ CRSM EXCEPT !.State = "CreateResources" ]

CRSM_CreateResourcesTransition == 
    /\ CRSM.State = "CreateResources"
    /\ CRSM' = [ CRSM EXCEPT !.State = "WaitForResourceCreation" ]

CRSM_WaitForResourcesCompleteTransition == 
    /\ CRSM.State = "WaitForResourceCreation"
    /\ CRSM' = [ CRSM EXCEPT !.State = "Ready" ]

CRSM_Actions ==
    \/ CRSM_CreateEvent
    \/ CRSM_BecomesActive
    \/ CRSM_PrepareForCreationTransition
    \/ CRSM_CreateResourcesTransition
    \/ CRSM_WaitForResourcesCompleteTransition


\** Spec

Init == 
    /\ CRSM = InitialCRSM

Next == 
    \/ CRSM_Actions

Spec == 
    /\ Init
    /\ [][Next]_vars


\** Invariants

Safe ==
    /\ TypeOk

Live ==
    /\ TRUE

Correct ==
    /\ Safe
    /\ Live


    
====