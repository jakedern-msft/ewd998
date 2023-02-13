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
CustomResourceStateMachineStates == { "Inactive", "PrepareForCreation", "CreateResources", "WaitForResourceCreation", "Ready" }
CustomResourceStateMachineEvents == { "Update", "Create"}
CustomResourceStateMachineType == [
    State: CustomResourceStateMachineStates
]

\* State
VARIABLE CustomResourceFSM, CustomResourceproviderFSM, FeatureOperation, K8sChildCustomObject, K8sParentCustomObjectGeneration

Init == 
    /\ CustomResourceFSM = [ State |-> "Inactive" ]
    /\ CustomResourceproviderFSM = [ State |-> "Inactive" ]
    /\ FeatureOperation = [ State |-> "Initial" ]
    /\ K8sChildCustomObject = [ Exists |-> FALSE, Ready |-> FALSE ]
    /\ K8sParentCustomObjectGeneration = 0

vars == << CustomResourceFSM, CustomResourceproviderFSM, FeatureOperation, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

TypeOk == 
    /\ CustomResourceFSM \in CustomResourceStateMachineType
    /\ CustomResourceproviderFSM \in CustomResourceProviderStateMachineType
    /\ FeatureOperation \in FeatureOperationType
    /\ K8sChildCustomObject \in K8sResourceType
    /\ CustomResourceFSM.State \in CustomResourceStateMachineStates
    /\ CustomResourceproviderFSM.State \in CustomResourceProviderStateMachineStates
    /\ FeatureOperation.State \in FeatureOperationStates
    /\ K8sChildCustomObject.Exists \in BOOLEAN
    /\ K8sChildCustomObject.Ready \in BOOLEAN
    /\ K8sParentCustomObjectGeneration \in Nat

\** Child custom object actions

K8sChildCustomObject_BecomesReady ==
    /\ K8sChildCustomObject.Exists = TRUE
    /\ K8sChildCustomObject.Ready = FALSE
    /\ K8sChildCustomObject' = [ K8sChildCustomObject EXCEPT !.Ready = TRUE ]
    /\ UNCHANGED << CustomResourceFSM, CustomResourceproviderFSM, FeatureOperation, K8sParentCustomObjectGeneration >>

K8sChildCustomObject_Actions ==
    \/ K8sChildCustomObject_BecomesReady

\** Custom resource provider machine actions

CustomResourceProvider_FSM_Start ==
    /\ CustomResourceproviderFSM.State = "Inactive"
    /\ FeatureOperation.State = "Pending"
    /\ CustomResourceproviderFSM' = [ CustomResourceproviderFSM EXCEPT !.State = "CreateUpdateResource" ]
    /\ UNCHANGED << CustomResourceFSM, K8sChildCustomObject, K8sParentCustomObjectGeneration, FeatureOperation >>

CustomResourceProvider_FSM_CreateUpdateResource ==
    /\ CustomResourceproviderFSM.State = "CreateUpdateResource"
    /\ CustomResourceproviderFSM' = [ CustomResourceproviderFSM EXCEPT !.State = "WaitForResourceToBeReady" ]
    /\ K8sChildCustomObject' = [ K8sChildCustomObject EXCEPT !.Exists = TRUE ]
    /\ UNCHANGED << CustomResourceFSM, FeatureOperation, K8sParentCustomObjectGeneration, K8sParentCustomObjectGeneration >>

CustomResourceProvider_FSM_TransitionToReady ==
    /\ CustomResourceproviderFSM.State = "WaitForResourceToBeReady"
    /\ K8sChildCustomObject.Ready = TRUE
    /\ CustomResourceproviderFSM' = [ CustomResourceproviderFSM EXCEPT !.State = "Ready" ]
    /\ UNCHANGED << CustomResourceFSM, FeatureOperation, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResourceProvider_FSM_Actions ==
    \/ CustomResourceProvider_FSM_CreateUpdateResource
    \/ CustomResourceProvider_FSM_TransitionToReady
    \/ CustomResourceProvider_FSM_Start

\** Custom Resource State Machine Actions

CustomResource_FSM_Start ==
    /\ CustomResourceFSM.State = "Inactive"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "PrepareForCreation" ]
    /\ UNCHANGED << CustomResourceproviderFSM, FeatureOperation, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_PrepareForCreationTransition ==
    /\ CustomResourceFSM.State = "PrepareForCreation"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "CreateResources" ]
    \* If feature operations are pending, we fire pause events on them
    /\  IF FeatureOperation.State = "Pending"
        THEN 
            \* Pause events are only valid in either the "CreateUpdateResource" or "WaitForResourceToBeReady"
            /\ \/ CustomResourceproviderFSM.State = "CreateUpdateResource"
               \/ CustomResourceproviderFSM.State = "WaitForResourceToBeReady"
            /\ CustomResourceproviderFSM' = [ CustomResourceproviderFSM EXCEPT !.State  = "CreateUpdatePaused" ]
        ELSE 
            /\ UNCHANGED CustomResourceproviderFSM
    /\ UNCHANGED << FeatureOperation, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_CreateResourcesTransition ==
    /\ CustomResourceFSM.State = "CreateResources"
    /\  IF FeatureOperation.State = "Initial" 
        THEN /\ FeatureOperation' = [ FeatureOperation EXCEPT !.State = "Pending" ]
             /\ UNCHANGED CustomResourceproviderFSM 
        ELSE IF FeatureOperation.State = "Pending" /\ CustomResourceproviderFSM.State = "CreateUpdatePaused"
             THEN /\ CustomResourceproviderFSM' = [ CustomResourceproviderFSM EXCEPT !.State = "CreateUpdateResource"]
                  /\ UNCHANGED FeatureOperation
             ELSE /\ UNCHANGED << CustomResourceproviderFSM, FeatureOperation >>
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "WaitForResourceCreation" ]
    \* Scheduler will not select feature operations that are in the "Completed" state
    /\ UNCHANGED << K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_WaitForResourcesUpdateEventTransition ==
    /\ CustomResourceFSM.State = "WaitForResourceCreation"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "PrepareForCreation" ]
    /\ K8sParentCustomObjectGeneration' = K8sParentCustomObjectGeneration + 1
    /\ UNCHANGED << CustomResourceproviderFSM, FeatureOperation, K8sChildCustomObject >>

CustomResource_FSM_ResourcesCreationCompleteTransition ==
    \* Custom reosurce fsm must be in WaitForResourceCreation state for this auto action
    /\ CustomResourceFSM.State = "WaitForResourceCreation"
    /\ CustomResourceproviderFSM.State = "Ready"
    /\ CustomResourceFSM' = [ CustomResourceFSM EXCEPT !.State = "Ready" ]
    /\ FeatureOperation' = [ FeatureOperation EXCEPT !.State = "Completed" ]
    /\ UNCHANGED << CustomResourceproviderFSM, K8sChildCustomObject, K8sParentCustomObjectGeneration >>

CustomResource_FSM_Actions ==
    \/ CustomResource_FSM_Start
    \/ CustomResource_FSM_PrepareForCreationTransition
    \/ CustomResource_FSM_CreateResourcesTransition
    \/ CustomResource_FSM_WaitForResourcesUpdateEventTransition
    \/ CustomResource_FSM_ResourcesCreationCompleteTransition

\** Spec

Next == 
    \/ K8sChildCustomObject_Actions
    \/ CustomResourceProvider_FSM_Actions
    \/ CustomResource_FSM_Actions

UpdatesAreFinite == 
    K8sParentCustomObjectGeneration < 3

Spec == 
    /\ Init
    /\ [][Next]_vars
    \* /\ WF_vars(CustomResource_FSM_Actions)
    \* /\ WF_vars(CustomResourceProvider_FSM_Actions)
    \* /\ WF_vars(K8sChildCustomObject_Actions)
    

\** Invariants

Safe ==
    /\ TypeOk
    \* /\ [][CustomResourceproviderFSM.State # "Ready"]_vars
    \* /\ [][K8sChildCustomObject.Ready # TRUE]_vars
    \* /\ [][CustomResourceFSM.State # "Ready"]_vars
    \* /\ [][CustomResourceFSM.State = "Ready" => CustomResourceproviderFSM.State = "Ready"]_vars

Live ==
    /\ <>(K8sChildCustomObject.Ready = TRUE) ~> (CustomResourceFSM.State = "Ready" /\ CustomResourceproviderFSM.State = "Ready")
    /\ TRUE

Correct ==
    /\ Safe
    /\ Live

====