---- MODULE CRFP ----
EXTENDS TLC

VARIABLE MachineState, K8s_ResourceExists, K8s_ResourceState \** K8sSpecMatchesStateMachineSpec

MachineStates == { "CreateUpdateResource", "WaitForResourceToBeReady", "CreateUpdatePaused", "Ready", "Deleted"}

TypeOk ==
    /\ MachineState \in MachineStates
    /\ ResourceExists \in BOOLEAN
    /\ ResourceIsReady \in BOOLEAN

Init == 
    /\ MachineState = "CreateUpdateResource"
    /\ ResourceExists \in BOOLEAN
    /\ IF ResourceExists THEN ResourceIsReady \in BOOLEAN ELSE ResourceIsReady = FALSE

\******* Safety properties ********

ResourceIsReadyImpliesResourceExists ==
    [][ResourceIsReady => ResourceExists]_<< ResourceIsReady, ResourceExists >>

DeletionIsStable ==
    [][MachineState = "Deleted" => MachineState' = "Deleted"]_<< MachineState >>

ResourcesAreDeleted ==
    [][MachineState = "Deleted" => ResourceExists = FALSE]_<< MachineState, ResourceExists >>

Safe ==
    /\ [](TypeOk)
    /\ ResourceIsReadyImpliesResourceExists
    /\ DeletionIsStable
    /\ ResourcesAreDeleted

\******* Liveness properties ********

StableStateIsReached ==
    \/ <>(MachineState = "Ready")
    \/ <>(MachineState = "Deleted")

\******* Updated event fired ********

UpdateEventFired ==
    \/ MachineState = "CreateUpdateResource"
    \/ MachineState = "WaitForResourceToBeReady"
    \/ MachineState = "CreateUpdatePaused"
    \/ MachineState = "Ready"
    \* Skips over PreCreateUpdate Action
    /\ MachineState' = "CreateUpdateResource"

PauseEventFired == 
    \/ MachineState = "CreateUpdateResource"
    \/ MachineState = "WaitForResourceToBeReady"
    /\ MachineState' = "CreateUpdatePaused"

DeleteUpdateFired ==
    \/ MachineState = "CreateUpdateResource"
    \/ MachineState = "WaitForResourceToBeReady"
    \/ MachineState = "CreateUpdatePaused"
    \/ MachineState = "Ready"
    /\ MachineState' = "Deleted"

CreateUpdateResource
    /\ MachineState = "CreateUpateResource"
    

Live ==
    /\ TRUE
    /\ StableStateIsReached

Next == 
    \/ UpdateEventFired
    \/ PauseEventFired
    \/ DeleteUpdateFired`
====