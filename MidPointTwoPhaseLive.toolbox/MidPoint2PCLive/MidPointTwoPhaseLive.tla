------------------------------- MODULE MidPointTwoPhaseLive ----------------------------- 
(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module $TCommit$.  In *)
(* this specification, RMs spontaneously issue $Prepared$ messages.  We    *)
(* ignore the $Prepare$ messages that the TM can send to the               *)
(* RMs.\vspace{.4em}                                                       *)
(*                                                                         *)
(* For simplicity, we also eliminate $Abort$ messages sent by an RM when   *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.\vspace{.4em}                                                  *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)
EXTENDS Integers, Naturals

CONSTANT RM, DEFAULT_TIMER \* The set of resource managers

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  rmTimer,       \* Timers for each resource manager.
  msgs           
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  Since we are specifying only safety, a process is not    *)
    (* required to receive a message, so there is no need to model message *)
    (* loss.  (There's no difference between a process not being able to   *)
    (* receive a message because the message was lost and a process simply *)
    (* ignoring the message.)  We therefore represent message passing with *)
    (* a variable $msgs$ whose value is the set of all messages that have  *)
    (* been sent.  Messages are never removed from $msgs$.  An action      *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the existence of that message in *)
    (* $msgs$.  (Receipt of the same message twice is therefore allowed;   *)
    (* but in this particular protocol, receiving a message for the second *)
    (* time has no effect.)                                                *)
    (***********************************************************************)


Message ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type $"Prepared"$ are  *)
  (* sent from the RM indicated by the message's $rm$ field to the TM\@.   *)
  (* Messages of type $"Commit"$ and $"Abort"$ are broadcast by the TM, to *)
  (* be received by all RMs.  The set $msgs$ contains just a single copy   *)
  (* of such a message.                                                    *)
  (*************************************************************************)
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
   
TPTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message
  /\ rmTimer \in [RM -> Nat]  \* Natural numbers for timers.

TPInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
  /\ rmTimer = [rm \in RM |-> DEFAULT_TIMER]  \* Initialize timers.
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs, rmTimer>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmTimer>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, rmTimer>>

RMPrepare(rm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, rmTimer>>
  
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmTimer>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmTimer>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmTimer>>
  
RMDecrementTimer(rm) ==
  /\ rmState[rm] \in {"working", "prepared"}
  /\ rmTimer[rm] > 0
  /\ rmTimer' = [rmTimer EXCEPT ![rm] = @ - 1]
  /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs>>

RMFail(rm) ==
  /\ rmTimer[rm] = 0
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, rmTimer>>

RMRecover(rm) ==
  /\ rmState[rm] = "aborted"
  /\ IF tmState = "committed" THEN rmState' = [rmState EXCEPT ![rm] = "committed"]
     ELSE rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ rmTimer' = [rmTimer EXCEPT ![rm] = DEFAULT_TIMER]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm)
       \/ RMChooseToAbort(rm) \/ RMRcvCommitMsg(rm)
       \/ RMRcvAbortMsg(rm) \/ RMFail(rm) \/ RMRecover(rm)
       \/ RMDecrementTimer(rm)
-----------------------------------------------------------------------------
TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, rmTimer, msgs>> /\ WF_<<rmState, tmState, tmPrepared, rmTimer, msgs>>(TPNext)
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

THEOREM TPSpec => []TPTypeOK
  (*************************************************************************)
  (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
  (* an invariant of the specification.                                    *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that the Two-Phase Commit protocol implements the         *)
(* Transaction Commit protocol of module $TCommit$.  The following         *)
(* statement defines $TC!TCSpec$ to be formula $TCSpec$ of module           *)
(* $TCommit$.  (The TLA$^+$ \textsc{instance} statement is used to rename  *)
(* the operators defined in module $TCommit$ avoids any name conflicts     *)
(* that might exist with operators in the current module.)                 *)
(***************************************************************************)
TC == INSTANCE TCommit 

THEOREM TPSpec => TC!TCSpec
  (*************************************************************************)
  (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
  (* Commit protocol implements the specification TCSpec of the            *)
  (* Transaction Commit protocol.                                          *)
  (*************************************************************************)
(***************************************************************************)
(* The two theorems in this module have been checked with TLC for six      *)
(* RMs, a configuration with 50816 reachable states, in a little over a    *)
(* minute on a 1 GHz PC.                                                   *)
(***************************************************************************)
=============================================================================