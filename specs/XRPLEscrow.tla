--------------------------- MODULE XRPLEscrow ---------------------------
(***************************************************************************
 * TLA+ Specification: XRPL Escrow
 * 
 * This spec serves as a PRECISE CONTRACT for LLM code generation.
 * An escrow locks XRP until a condition is met (time-based or crypto-condition).
 * 
 * USE THIS SPEC IN YOUR LLM PROMPT to generate correct implementations.
 ***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS
    EscrowIds,          \* Set of escrow IDs
    Accounts,           \* Set of account addresses  
    MaxAmount,          \* Maximum XRP amount (in drops)
    MaxLedgerSeq        \* Maximum ledger sequence for bounds

VARIABLES
    escrows,            \* escrowId -> EscrowRecord
    ledgerSeq           \* Current ledger sequence (models time)

(***************************************************************************
 * TYPE DEFINITIONS
 ***************************************************************************)
 
EscrowState == {"CREATED", "FINISHED", "CANCELLED"}

EscrowRecord == [
    escrowId: STRING,
    sender: Accounts,           \* Who locked the funds
    destination: Accounts,      \* Who can claim when conditions met
    amountDrops: 1..MaxAmount,  \* XRP locked (in drops)
    finishAfter: 0..MaxLedgerSeq,   \* Can finish AFTER this ledger (0 = no constraint)
    cancelAfter: 0..MaxLedgerSeq,   \* Can cancel AFTER this ledger (0 = no constraint)
    state: EscrowState
]

(***************************************************************************
 * INVARIANT 1: Escrow Amount is Always Positive
 * 
 * An escrow must always hold a positive amount.
 * Zero or negative amounts make no sense.
 ***************************************************************************)
AmountAlwaysPositive ==
    \A eid \in EscrowIds :
        escrows[eid] # NULL => escrows[eid].amountDrops > 0

(***************************************************************************
 * INVARIANT 2: Time Constraints are Logical
 * 
 * If both finishAfter and cancelAfter are set, cancel must be > finish.
 * Otherwise the escrow could never be finished (would be cancellable first).
 ***************************************************************************)
TimeConstraintsLogical ==
    \A eid \in EscrowIds :
        escrows[eid] # NULL =>
            (escrows[eid].finishAfter > 0 /\ escrows[eid].cancelAfter > 0) =>
                escrows[eid].cancelAfter > escrows[eid].finishAfter

(***************************************************************************
 * INVARIANT 3: Finished Escrows Cannot Change
 * 
 * Once an escrow is FINISHED or CANCELLED, it's immutable.
 ***************************************************************************)
FinalStatesImmutable ==
    \* This is enforced by action guards, not a state predicate
    TRUE

(***************************************************************************
 * INVARIANT 4: Sender and Destination Must Differ
 * 
 * You can't escrow funds to yourself (that's pointless).
 ***************************************************************************)
SenderDestinationDiffer ==
    \A eid \in EscrowIds :
        escrows[eid] # NULL => 
            escrows[eid].sender # escrows[eid].destination

(***************************************************************************
 * COMBINED SAFETY INVARIANT
 ***************************************************************************)
SafetyInvariant ==
    /\ AmountAlwaysPositive
    /\ TimeConstraintsLogical
    /\ SenderDestinationDiffer

(***************************************************************************
 * INITIAL STATE
 ***************************************************************************)
NULL == CHOOSE x : x \notin EscrowRecord

Init ==
    /\ escrows = [eid \in EscrowIds |-> NULL]
    /\ ledgerSeq = 1

(***************************************************************************
 * ACTION: Create Escrow (EscrowCreate transaction)
 * 
 * Sender locks XRP for destination with time conditions.
 * 
 * GUARDS (preconditions):
 *   G1: Escrow ID not already used
 *   G2: Sender and destination are different
 *   G3: Amount is positive
 *   G4: If both time constraints set, cancelAfter > finishAfter
 *   G5: At least one time constraint must be set
 ***************************************************************************)
CreateEscrow(eid, sender, destination, amount, finishAfter, cancelAfter) ==
    /\ escrows[eid] = NULL                              \* G1: ID available
    /\ sender # destination                              \* G2: Different parties
    /\ amount > 0                                        \* G3: Positive amount
    /\ (finishAfter > 0 \/ cancelAfter > 0)             \* G5: At least one constraint
    /\ (finishAfter > 0 /\ cancelAfter > 0) =>          \* G4: Logical time order
            cancelAfter > finishAfter
    /\ escrows' = [escrows EXCEPT ![eid] = [
            escrowId |-> eid,
            sender |-> sender,
            destination |-> destination,
            amountDrops |-> amount,
            finishAfter |-> finishAfter,
            cancelAfter |-> cancelAfter,
            state |-> "CREATED"
       ]]
    /\ UNCHANGED ledgerSeq

(***************************************************************************
 * ACTION: Finish Escrow (EscrowFinish transaction)
 * 
 * Destination (or sender) releases funds to destination.
 * 
 * GUARDS (preconditions):
 *   G1: Escrow exists
 *   G2: Escrow is in CREATED state
 *   G3: Current ledger > finishAfter (time condition met)
 *   G4: If cancelAfter is set, current ledger < cancelAfter (not yet cancellable)
 * 
 * POSTCONDITIONS:
 *   - State becomes FINISHED
 *   - Destination receives amountDrops
 ***************************************************************************)
FinishEscrow(eid) ==
    /\ escrows[eid] # NULL                              \* G1: Exists
    /\ escrows[eid].state = "CREATED"                   \* G2: Not already done
    /\ escrows[eid].finishAfter = 0 \/                  \* G3: Time condition met
            ledgerSeq > escrows[eid].finishAfter
    /\ escrows[eid].cancelAfter = 0 \/                  \* G4: Not past cancel window
            ledgerSeq < escrows[eid].cancelAfter
    /\ escrows' = [escrows EXCEPT ![eid].state = "FINISHED"]
    /\ UNCHANGED ledgerSeq

(***************************************************************************
 * ACTION: Cancel Escrow (EscrowCancel transaction)
 * 
 * Returns funds to sender (only after cancelAfter time).
 * 
 * GUARDS (preconditions):
 *   G1: Escrow exists
 *   G2: Escrow is in CREATED state  
 *   G3: cancelAfter is set (escrow is cancellable)
 *   G4: Current ledger > cancelAfter (cancel time reached)
 * 
 * POSTCONDITIONS:
 *   - State becomes CANCELLED
 *   - Sender receives amountDrops back
 ***************************************************************************)
CancelEscrow(eid) ==
    /\ escrows[eid] # NULL                              \* G1: Exists
    /\ escrows[eid].state = "CREATED"                   \* G2: Not already done
    /\ escrows[eid].cancelAfter > 0                     \* G3: Is cancellable
    /\ ledgerSeq > escrows[eid].cancelAfter             \* G4: Cancel time reached
    /\ escrows' = [escrows EXCEPT ![eid].state = "CANCELLED"]
    /\ UNCHANGED ledgerSeq

(***************************************************************************
 * ACTION: Advance Ledger (time passing)
 ***************************************************************************)
AdvanceLedger ==
    /\ ledgerSeq' = ledgerSeq + 1
    /\ UNCHANGED escrows

(***************************************************************************
 * NEXT STATE RELATION
 ***************************************************************************)
Next ==
    \/ \E eid \in EscrowIds, s, d \in Accounts, 
          amt \in 1..MaxAmount, fa, ca \in 0..MaxLedgerSeq :
        CreateEscrow(eid, s, d, amt, fa, ca)
    \/ \E eid \in EscrowIds : FinishEscrow(eid)
    \/ \E eid \in EscrowIds : CancelEscrow(eid)
    \/ AdvanceLedger

(***************************************************************************
 * SPECIFICATION
 ***************************************************************************)
Spec == Init /\ [][Next]_<<escrows, ledgerSeq>>

THEOREM Spec => []SafetyInvariant

=============================================================================
