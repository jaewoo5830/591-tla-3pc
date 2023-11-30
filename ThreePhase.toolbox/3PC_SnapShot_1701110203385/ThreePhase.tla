----------------------------- MODULE ThreePhase -----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT RM \* The set of resource managers

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared" messages.
  tmCanCommit,   \* The set of RMs that can commit.
  rmVote,        \* The vote of each RM.
  msgs

Message ==
  [type : {"Prepared", "CanCommit", "ReadyToCommit", "PreCommit", "Commit", "Abort"}, rm : RM]
   \cup  [type : {"Commit", "Abort"}]

TPTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "readyToCommit", "committed", "aborted"}]
  /\ tmState \in {"init", "waitingForVotes", "preCommit", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ tmCanCommit \subseteq RM
  /\ rmVote \in [RM -> {"Yes", "No"}]
  /\ msgs \subseteq Message

TPInit ==   
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ tmCanCommit = {}
  /\ rmVote = [rm \in RM |-> "No"]
  /\ msgs = {}

TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs, tmCanCommit, rmVote>>
  
TMStartVote ==
  /\ tmState = "init"
  /\ tmState' = "waitingForVotes"
  /\ UNCHANGED <<rmState, tmPrepared, tmCanCommit, rmVote, msgs>>

TMCollectVotes ==
  /\ tmState = "waitingForVotes"
  /\ tmCanCommit' = {rm \in RM : rmVote[rm] = "Yes"}
  /\ IF tmCanCommit' = RM
     THEN tmState' = "preCommit"
     ELSE tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "PreCommit"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmVote>>

TMCommit ==
  /\ tmState = "preCommit"
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, tmCanCommit, rmVote>>

TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, tmCanCommit, rmVote>>

RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ rmVote' = [rmVote EXCEPT ![rm] = "Yes"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit>>

RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ rmVote' = [rmVote EXCEPT ![rm] = "No"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, msgs>>

RMReadyToCommit(rm) ==
  /\ rmState[rm] = "prepared"
  /\ rmState' = [rmState EXCEPT ![rm] = "readyToCommit"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

RMRcvPreCommitMsg(rm) ==
  /\ [type |-> "PreCommit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "readyToCommit"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

TPNext ==
  \/ TMStartVote
  \/ TMCollectVotes \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
       \/ RMReadyToCommit(rm) \/ RMRcvPreCommitMsg(rm)
       \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)

-----------------------------------------------------------------------------
TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, tmCanCommit, rmVote, msgs>>
THEOREM TPSpec => []TPTypeOK
=============================================================================

\* Modification History
\* Last modified Mon Nov 27 13:35:51 EST 2023 by jaewoo
\* Created Mon Nov 27 13:35:25 EST 2023 by jaewoo
