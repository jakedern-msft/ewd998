---- MODULE CRFP ----
EXTENDS TLC

VARIABLE State, ResourceExists, ResourceIsReady \** K8sSpecMatchesStateMachineSpec

States == { "CreateUpdateResource", "WaitForResourceToBeReady", "CreateUpdatePaused", "Ready", "Deleted"}

TypeOk ==
    /\ State \in States
    /\ ResourceExists \in BOOLEAN
    /\ ResourceIsReady \in BOOLEAN

Init == 
    /\ State = "CreateUpdateResource"
    /\ ResourceExists \in BOOLEAN
    /\ IF ResourceExists THEN ResourceIsReady \in BOOLEAN ELSE ResourceIsReady = FALSE 

\******* Safety properties ********

ResourceIsReadyImpliesResourceExists ==
    [][ResourceIsReady => ResourceExists]_<< ResourceIsReady, ResourceExists >>

DeletionIsStable ==
    [][State = "Deleted" => State' = "Deleted"]_<< State >>

ResourcesAreDeleted ==
    [][State = "Deleted" => ResourceExists = FALSE]_<< State, ResourceExists >>

Safe ==
    /\ [](TypeOk)
    /\ ResourceIsReadyImpliesResourceExists
    /\ DeletionIsStable
    /\ ResourcesAreDeleted

\******* Liveness properties ********

StableStateIsReached ==
    \/ <>(State = "Ready")
    \/ <>(State = "Deleted")

Live ==
    /\ TRUE
    /\ StableStateIsReached

\******* Update Events ********

UpdateEventFired_From_CreateUpdateResource ==
    /\ State = "CreateUpdateResource"
    /\ State' = "CreateUpdateResource"
    /\ UNCHANGED << ResourceIsReady, ResourceExists >>

UpdateEventFired_From_WaitForResourceToBeReady ==
    /\ State = "WaitForResourceToBeReady"
    /\ State' = "CreateUpdateResource"
    /\ ResourceExists = TRUE
    /\ ResourceExists' = TRUE
    /\ UNCHANGED << ResourceIsReady >>

UpdateEventFired_From_CreateUpdatePaused ==
    /\ State = "CreateUpdatePaused"
    /\ State' = "CreateUpdateResource"
    /\ UNCHANGED << ResourceIsReady, ResourceExists >>

UpdateEventFired_From_Ready ==
    /\ State = "Ready"
    /\ State' = "CreateUpdateResource"
    /\ ResourceExists = TRUE
    /\ ResourceExists' = TRUE
    /\ ResourceIsReady = TRUE
    /\ ResourceIsReady' \in BOOLEAN


UpdateEventFired ==
    \/ UpdateEventFired_From_CreateUpdateResource
    \/ UpdateEventFired_From_WaitForResourceToBeReady
    \/ UpdateEventFired_From_CreateUpdatePaused
    \/ UpdateEventFired_From_Ready

\******* CreateUpdateResource Method ********

\* Creation was successful and next state is WaitForResourceToBeReady
CreateUpdateResource_Success ==
    /\ State = "CreateUpdateResource"
    /\ State' = "WaitForResourceToBeReady"
    /\ ResourceExists' = TRUE
    /\ UNCHANGED << ResourceIsReady >>

\* Creation failed and the next state is CreateUpdateResource
CreateUpdateResource_Fail ==
    /\ State = "CreateUpdateResource"
    /\ State' = "CreateUpdateResource"
    /\ UNCHANGED << ResourceExists, ResourceIsReady >>

CreateUpdateResource == 
    \/ CreateUpdateResource_Success
    \/ CreateUpdateResource_Fail

\******* TransitionToReady Method ********

TransitionToReady_IsReady ==
    /\ State = "WaitForResourceToBeReady"
    /\ State' = "Ready"
    /\ ResourceIsReady' = TRUE
    /\ UNCHANGED << ResourceExists >>

TransitionToReady_IsNotReady ==
    /\ State = "WaitForResourceToBeReady"
    /\ State' = "WaitForResourceToBeReady"
    /\ UNCHANGED << ResourceExists, ResourceIsReady >>

TransitionToReady ==
    \/ TransitionToReady_IsReady
    \/ TransitionToReady_IsNotReady

\******* Delete Event ********

DeleteEventFired ==
    \/ State = "CreateUpdateResource"
    \/ State = "WaitForResourceToBeReady"
    \/ State = "CreateUpdatePaused"
    \/ State = "Ready"
    /\ State' = "Deleted"
    /\ ResourceExists' = FALSE
    /\ ResourceIsReady' = FALSE

\******* Pause Event ********

PauseEventFired_From_CreateUpdateResource ==
    /\ State = "CreateUpdateResource"
    /\ State' = "CreateUpdatePaused"
    /\ UNCHANGED << ResourceExists, ResourceIsReady >>

PauseEventFired_From_WaitForResourceToBeReady ==
    /\ State = "WaitForResourceToBeReady"
    /\ State' = "CreateUpdatePaused"
    /\ ResourceExists = TRUE
    /\ ResourceExists' = TRUE
    /\ UNCHANGED << ResourceIsReady >>

PauseEventFired == 
    \/ PauseEventFired_From_CreateUpdateResource
    \/ PauseEventFired_From_WaitForResourceToBeReady

Next == 
    \/ UpdateEventFired
    \/ PauseEventFired
    \/ CreateUpdateResource
    \/ TransitionToReady
    \/ DeleteEventFired
====