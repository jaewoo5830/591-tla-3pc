------------------------------- MODULE ThreePhase -----------------------------
EXTENDS Integers, Sequences, TLC
\* This module named 'ThreePhase' represents a three-phase commit protocol
\* in a transaction processing system. It extends standard TLA+ modules for 
\* integer arithmetic, sequence operations, and model checking.

CONSTANT RM  \* The set of resource managers participating in the transactions.

VARIABLES
  rmState,       \* State of each resource manager (RM).
  tmState,       \* State of the transaction manager (TM).
  tmPrepared,    \* Set of RMs from which the TM has received "Prepared" messages.
  tmCanCommit,   \* Set of RMs that TM considers ready to commit.
  rmVote,        \* The vote ("Yes" or "No") of each RM.
  msgs           \* The set of messages exchanged in the system.

\* Message structure definition, encompassing various types related to transaction phases.
Message ==
  [type : {"Prepared", "CanCommit", "ReadyToCommit", "PreCommit", "Commit", "Abort"}, rm : RM]
   \cup  [type : {"Commit", "Abort"}]

\* Ensures all system variables are within their expected types or domains.
TPTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "readyToCommit", "committed", "aborted"}]
  /\ tmState \in {"init", "waitingForVotes", "preCommit", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ tmCanCommit \subseteq RM
  /\ rmVote \in [RM -> {"Yes", "No"}]
  /\ msgs \subseteq Message
  
\* Ensures that RMs cannot come to conflicting final states.
TPConsistent ==
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

\* Ensures liveness of the system; that it eventually makes progress
TPLive ==
  <>((\A rm \in RM : rmState[rm] = "aborted") \/ (\A rm \in RM : rmState[rm] = "committed"))

\* Defines the initial state of the system with the TM not started and RMs in 'working' state.
TPInit ==   
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ tmCanCommit = {}
  /\ rmVote = [rm \in RM |-> "No"]
  /\ msgs = {}

\* Action for TM to handle a 'Prepared' message from a RM.
TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs, tmCanCommit, rmVote>>
  
\* Action for TM to start the voting process.
TMStartVote ==
  /\ tmState = "init"
  /\ tmState' = "waitingForVotes"
  /\ UNCHANGED <<rmState, tmPrepared, tmCanCommit, rmVote, msgs>>

\* TM action to collect votes and decide on committing or aborting.
TMCollectVotes ==
  /\ tmState = "waitingForVotes"
  /\ tmCanCommit' = {rm \in RM : rmVote[rm] = "Yes"}
  /\ IF tmCanCommit' = RM
     THEN tmState' = "preCommit"
     ELSE tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "PreCommit"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmVote>>

\* TM action for committing the transaction.
TMCommit ==
  /\ tmState = "preCommit"
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, tmCanCommit, rmVote>>

\* TM action for aborting the transaction.
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, tmCanCommit, rmVote>>

\* Action for RM to prepare for a transaction.
RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ rmVote' = [rmVote EXCEPT ![rm] = "Yes"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit>>

\* Action for RM to decide to abort a transaction.
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ rmVote' = [rmVote EXCEPT ![rm] = "No"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, msgs>>

\* Action for RM to signal readiness to commit.
RMReadyToCommit(rm) ==
  /\ rmState[rm] = "prepared"
  /\ rmState' = [rmState EXCEPT ![rm] = "readyToCommit"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

\* Action for RM to handle a 'PreCommit' message.
RMRcvPreCommitMsg(rm) ==
  /\ [type |-> "PreCommit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "readyToCommit"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

\* Action for RM to handle a 'Commit' message.
RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

\* Action for RM to handle an 'Abort' message.
RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

\* Defines possible next states of the system based on TM and RM actions.
TPNext ==
  \/ TMStartVote
  \/ TMCollectVotes \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
       \/ RMReadyToCommit(rm) \/ RMRcvPreCommitMsg(rm)
       \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
       
\* DUMMY THING
DoNothing == UNCHANGED <<rmState, tmState, tmPrepared, tmCanCommit, rmVote, msgs>>

-----------------------------------------------------------------------------
\* Theorem stating the maintenance of type correctness throughout the system execution.
TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, tmCanCommit, rmVote, msgs>>
THEOREM TPSpec => [](TPTypeOK /\ TPConsistent /\ TPLive /\ FALSE)
=============================================================================

\* Modification History
\* Last modified Thu Nov 30 23:41:33 EST 2023 by andre
\* Last modified Thu Nov 30 23:26:44 EST 2023 by andre
\* Last modified Mon Nov 27 13:45:19 EST 2023 by jaewoo
\* Created Mon Nov 27 13:35:25 EST 2023 by jaewoo
