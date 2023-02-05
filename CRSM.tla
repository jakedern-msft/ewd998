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
    State: CustomResourceProviderStateMachineStates
]

\* Possible states for a feature operation
FeatureOperationStates == { "Initial", "Pending", "Completed" }
FeatureOperationType == [
    State: FeatureOperationStates
]

\* Custom resource state machine states and events
CustomResourceStateMachineStates == { "Inactive", "PrepareForCreation", "CreateResources", "WaitForResourceCreation", "PrepareForCreation", "Ready" }
CustomResourceStateMachineEvents == { "Update", "Create"}
CustomResourceStateMachineType == [
    State: CustomResourceStateMachineStates
]

\** Variables and types

VARIABLE CustomResourceFSM, CustomResourceProviderFSM_One, FeatureOperation_One, K8sChildCustomObject, K8sParentCustomObjectGeneration

vars == << CustomResourceFSM, CustomResourceProviderFSM_One, FeatureOperation_One, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

TypeOk == 
    /\ CustomResourceFSM \in CustomResourceStateMachineType
    /\ CustomResourceProviderFSM_One \in CustomResourceProviderStateMachineType
    /\ FeatureOperation_One \in FeatureOperationType
    /\ K8sChildCustomObject \in K8sResourceType
    /\ CustomResourceFSM.State \in CustomResourceStateMachineStates
    /\ CustomResourceProviderFSM_One.State \in CustomResourceProviderStateMachineStates
    /\ FeatureOperation_One.State \in FeatureOperationStates
    /\ K8sChildCustomObject.Exists \in BOOLEAN
    /\ K8sChildCustomObject.Ready \in BOOLEAN
    /\ K8sParentCustomObjectGeneration \in Nat

\** Child custom object actions

K8sChildCustomObject_BecomesReady ==
    /\ K8sChildCustomObject.Exists = TRUE
    /\ K8sChildCustomObject.Ready = FALSE
    /\ K8sChildCustomObject' = [ K8sChildCustomObject EXCEPT !.Ready = TRUE ]
    /\ UNCHANGED << CustomResourceFSM, CustomResourceProviderFSM_One, FeatureOperation_One, K8sParentCustomObjectGeneration >>

K8sChildCustomObject_Actions ==
    \/ K8sChildCustomObject_BecomesReady

\** Custom resource provider machine actions

CustomResourceProvider_FSM_Start ==
    /\ CustomResourceProviderFSM_One.State = "Inactive"
    /\ FeatureOperation_One.State = "Pending"
    /\ CustomResourceProviderFSM_One' = [ CustomResourceProviderFSM_One EXCEPT !.State = "CreateUpdateResource" ]
    /\ UNCHANGED << CustomResourceFSM, K8sChildCustomObject, K8sParentCustomObjectGeneration, FeatureOperation_One >>

CustomResourceProvider_FSM_CreateUpdateResource ==
    /\ CustomResourceProviderFSM_One.State = "CreateUpdateResource"
    /\ CustomResourceProviderFSM_One' = [ CustomResourceProviderFSM_One EXCEPT !.State = "WaitForResourceToBeReady" ]
    /\ K8sChildCustomObject' = [ K8sChildCustomObject EXCEPT !.Exists = TRUE ]
    /\ UNCHANGED << CustomResourceFSM, FeatureOperation_One, K8sParentCustomObjectGeneration, K8sParentCustomObjectGeneration >>

CustomResourceProvider_FSM_TransitionToReady ==
    /\ CustomResourceProviderFSM_One.State = "WaitForResourceToBeReady"
    /\ K8sChildCustomObject.Ready = TRUE
    /\ CustomResourceProviderFSM_One' = [ CustomResourceProviderFSM_One EXCEPT !.State = "Ready" ]
    /\ UNCHANGED << CustomResourceFSM, FeatureOperation_One, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResourceProvider_FSM_Actions ==
    \/ CustomResourceProvider_FSM_CreateUpdateResource
    \/ CustomResourceProvider_FSM_TransitionToReady
    \/ CustomResourceProvider_FSM_Start

\** Custom Resource State Machine Actions

CustomResource_FSM_Start ==
    /\ CustomResourceFSM.State = "Inactive"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "PrepareForCreation" ]
    /\ UNCHANGED << CustomResourceProviderFSM_One, FeatureOperation_One, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_PrepareForCreationTransition ==
    /\ CustomResourceFSM.State = "PrepareForCreation"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "CreateResources" ]
    /\  IF FeatureOperation_One.State = "Pending"
        THEN 
            /\ \/ CustomResourceProviderFSM_One.State = "CreateUpdateResource"
               \/ CustomResourceProviderFSM_One.State = "WaitForResourceToBeReady"
            /\ CustomResourceProviderFSM_One' = [ CustomResourceProviderFSM_One EXCEPT !.State  = "CreateUpdatePaused" ]
        ELSE 
            /\ UNCHANGED CustomResourceProviderFSM_One
    /\ UNCHANGED << FeatureOperation_One, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_CreateResourcesTransition ==
    /\ CustomResourceFSM.State = "CreateResources"
    /\  IF FeatureOperation_One.State = "Initial" 
        THEN /\ FeatureOperation_One' = [ FeatureOperation_One EXCEPT !.State = "Pending" ]
             /\ UNCHANGED CustomResourceProviderFSM_One 
        ELSE IF FeatureOperation_One.State = "Pending" /\ CustomResourceProviderFSM_One.State = "CreateUpdatePaused"
             THEN /\ CustomResourceProviderFSM_One' = [ CustomResourceProviderFSM_One EXCEPT !.State = "CreateUpdateResource"]
                  /\ UNCHANGED FeatureOperation_One
             ELSE /\ UNCHANGED << CustomResourceProviderFSM_One, FeatureOperation_One >>
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "WaitForResourceCreation" ]
    \* Scheduler will not select feature operations that are in the "Completed" state
    /\ UNCHANGED << K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_WaitForResourcesUpdateEventTransition ==
    /\ CustomResourceFSM.State = "WaitForResourceCreation"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "PrepareForCreation" ]
    /\ K8sParentCustomObjectGeneration' = K8sParentCustomObjectGeneration + 1
    /\ UNCHANGED << CustomResourceProviderFSM_One, FeatureOperation_One, K8sChildCustomObject >>

CustomResource_FSM_ResourcesCreationCompleteTransition ==
    \* Custom reosurce fsm must be in WaitForResourceCreation state for this auto action
    /\ CustomResourceFSM.State = "WaitForResourceCreation"
    /\ CustomResourceProviderFSM_One.State = "Ready"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "Ready" ]
    /\ FeatureOperation_One' = [ FeatureOperation_One EXCEPT !.State = "Completed" ]
    /\ UNCHANGED << CustomResourceProviderFSM_One, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_Actions ==
    \/ CustomResource_FSM_Start
    \/ CustomResource_FSM_PrepareForCreationTransition
    \/ CustomResource_FSM_CreateResourcesTransition
    \/ CustomResource_FSM_WaitForResourcesUpdateEventTransition
    \/ CustomResource_FSM_ResourcesCreationCompleteTransition

\** Spec

Init == 
    /\ CustomResourceFSM = [ State |-> "Inactive" ]
    /\ CustomResourceProviderFSM_One = [ State |-> "Inactive" ]
    /\ FeatureOperation_One = [ State |-> "Initial" ]
    /\ K8sChildCustomObject = [ Exists |-> FALSE, Ready |-> FALSE ]
    /\ K8sParentCustomObjectGeneration = 0

Next == 
    \/ K8sChildCustomObject_Actions
    \/ CustomResourceProvider_FSM_Actions
    \/ CustomResource_FSM_Actions

UpdatesAreFinite == 
    K8sParentCustomObjectGeneration < 2

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CustomResource_FSM_Actions)
    /\ WF_vars(CustomResourceProvider_FSM_Actions)
    /\ WF_vars(K8sChildCustomObject_Actions)
    

\** Invariants

Safe ==
    /\ TypeOk
    \* /\ [][CustomResourceProviderFSM_One.State # "Ready"]_vars
    \* /\ [][K8sChildCustomObject.Ready # TRUE]_vars
    \* /\ [][CustomResourceFSM.State # "Ready"]_vars
    \* /\ [][CustomResourceFSM.State = "Ready" => CustomResourceProviderFSM_One.State = "Ready"]_vars

Live ==
    \* /\ <>(K8sChildCustomObject.Ready = TRUE) ~> (CustomResourceFSM.State = "Ready" /\ CustomResourceProviderFSM_One.State = "Ready")
    /\ TRUE

Correct ==
    /\ Safe
    /\ Live

====