---- MODULE CRFP ----
EXTENDS Integers, TLC, Naturals
CONSTANT MaxUpdates

VARIABLE MachineState, K8s_ResourceExists, K8s_ResourceReady, RemainingUpdates \** K8sSpecMatchesStateMachineSpec

MachineStates == { "CreateUpdateResource", "WaitForResourceToBeReady", "CreateUpdatePaused", "Ready", "Deleted"}

vars == << MachineState, K8s_ResourceExists, K8s_ResourceReady, RemainingUpdates >>

Init == 
    /\ MachineState = "CreateUpdateResource"
    /\ K8s_ResourceExists \in BOOLEAN
    /\ IF K8s_ResourceExists THEN K8s_ResourceReady \in BOOLEAN ELSE K8s_ResourceReady = FALSE
    /\ RemainingUpdates = MaxUpdates

\******* Updated event fired ********

UpdateEventFired ==
    /\  \/ MachineState = "CreateUpdateResource"
        \/ MachineState = "WaitForResourceToBeReady"
        \/ MachineState = "CreateUpdatePaused"
        \/ MachineState = "Ready"
    \* Skips over PreCreateUpdate Action
    /\ MachineState' = "CreateUpdateResource"
    /\ RemainingUpdates > 0
    /\ RemainingUpdates' = RemainingUpdates - 1
    /\ UNCHANGED << K8s_ResourceExists, K8s_ResourceReady >>

PauseEventFired == 
    \/ MachineState = "CreateUpdateResource"
    \/ MachineState = "WaitForResourceToBeReady"
    /\ MachineState' = "CreateUpdatePaused"
    /\ UNCHANGED << K8s_ResourceExists, K8s_ResourceReady, RemainingUpdates >>

DeleteUpdateFired ==
    \/ MachineState = "CreateUpdateResource"
    \/ MachineState = "WaitForResourceToBeReady"
    \/ MachineState = "CreateUpdatePaused"
    \/ MachineState = "Ready"
    /\ MachineState' = "Deleted"
    /\ UNCHANGED << K8s_ResourceExists, K8s_ResourceReady, RemainingUpdates >>

CreateUpdateResource ==
    /\ MachineState = "CreateUpateResource"
    /\ MachineState' = "WaitForResourceToBeReady"
    /\ K8s_ResourceExists' = TRUE
    /\ UNCHANGED << K8s_ResourceReady, RemainingUpdates >>

WaitForResourceToBeReady ==
    /\ MachineState = "WaitForResourceToBeReady"
    /\ IF K8s_ResourceReady THEN MachineState' = "Ready" ELSE MachineState' = "WaitForResourceToBeReady"
    /\ UNCHANGED << K8s_ResourceExists, K8s_ResourceReady, RemainingUpdates >>

ResourceBecomesReady ==
    /\ K8s_ResourceExists = TRUE
    /\ K8s_ResourceReady' = TRUE
    /\ UNCHANGED << MachineState, K8s_ResourceExists, RemainingUpdates >>

\******* Safety properties ********

ResourceIsReadyImpliesResourceExists ==
    [][K8s_ResourceReady => K8s_ResourceExists]_<< K8s_ResourceReady, K8s_ResourceExists >>

DeletionIsStable ==
    [][MachineState = "Deleted" => MachineState' = "Deleted"]_<< MachineState >>

ResourcesAreDeleted ==
    [][MachineState = "Deleted" => K8s_ResourceExists = FALSE]_<< MachineState, K8s_ResourceExists >>

TypeOk ==
    /\ MachineState \in MachineStates
    /\ K8s_ResourceExists \in BOOLEAN
    /\ K8s_ResourceReady \in BOOLEAN

Safe ==
    /\ [](TypeOk)
    /\ ResourceIsReadyImpliesResourceExists
    /\ DeletionIsStable
    /\ ResourcesAreDeleted

\******* Liveness properties ********

StableStateIsReached ==
    \/ <>(MachineState = "Ready")
    \/ <>(MachineState = "Deleted")

Live ==
    /\ TRUE
    /\ StableStateIsReached

Correct ==
    /\ Safe
    /\ Live

Next == 
    \/ UpdateEventFired
    \/ PauseEventFired
    \/ DeleteUpdateFired
    \/ CreateUpdateResource
    \/ WaitForResourceToBeReady
    \/ ResourceBecomesReady

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ResourceBecomesReady)

\******* Constraints ********

UpdatesAreFinite == 
    RemainingUpdates <= 3

====