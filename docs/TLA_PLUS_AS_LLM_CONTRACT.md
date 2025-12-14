# TLA+ as Contracts for LLM Code Generation

## The Problem: Vague Requirements → Buggy Code

When we give LLMs informal requirements, they generate plausible-looking but subtly incorrect code.

## The Solution: TLA+ Specs as Precise Contracts

TLA+ specifications provide **unambiguous, machine-checkable contracts** that LLMs can follow precisely.

---

## DEMONSTRATION: Two Approaches to the Same Problem

### Scenario: XRPL Payment Channel Implementation

---

## APPROACH 1: Informal Requirements (What Most Developers Do)

### Prompt Given to LLM:

```
Write a Java class for XRPL payment channels. 
- Source creates a channel with XRP funding
- Source can authorize claims for the destination  
- Destination can redeem claims to get XRP
- Source can close the channel to get remaining funds back
```

### What LLM Generates (Buggy Code):

See `without_tlaplus/XRPLPaymentChannelService.java`

### Bugs Introduced:
1. ❌ No check that authorized amount ≤ funded amount
2. ❌ No expiration delay on close (instant fund theft possible)
3. ❌ No monotonicity enforcement (replay attacks possible)
4. ❌ Race conditions in concurrent scenarios
5. ❌ Source gets ALL funds back on close, not just unclaimed

**Why?** The informal requirements don't specify these constraints!

---

## APPROACH 2: TLA+ Specification as Contract (The Right Way)

### Prompt Given to LLM:

```
Implement the following TLA+ specification in Java.
Each TLA+ guard becomes a precondition check.
Each invariant must be enforced.
State transitions must be atomic.

[TLA+ SPECIFICATION FOLLOWS]
```

### The TLA+ Contract:

```tla
--------------------------- MODULE XRPLPaymentChannel ---------------------------

VARIABLES
    channels,           \* channel ID -> {source, destination, funded, claimed, state, expiresAt}
    ledgerSeq,          \* current ledger sequence number
    authorizedClaims    \* channel ID -> max authorized amount

(* ============================================================================
   INVARIANTS - These must ALWAYS be true
   ============================================================================ *)

(* INVARIANT 1: Destination can never withdraw more than source deposited *)
ClaimNeverExceedsFunding ==
    \A chId \in ChannelIds :
        channels[chId] # NULL => 
            channels[chId].claimed <= channels[chId].funded

(* INVARIANT 2: Claims must monotonically increase (prevents replay attacks) *)
ClaimsAreMonotonic ==
    \A chId \in ChannelIds :
        channels[chId] # NULL =>
            authorizedClaims[chId] >= channels[chId].claimed

(* ============================================================================
   ACTIONS - State transitions with explicit GUARDS (preconditions)
   ============================================================================ *)

(* ACTION: Authorize a claim amount *)
AuthorizeClaim(chId, amount) ==
    /\ channels[chId] # NULL                    (* GUARD 1: Channel exists *)
    /\ channels[chId].state = "OPEN"            (* GUARD 2: Channel is open *)
    /\ amount <= channels[chId].funded          (* GUARD 3: Cannot authorize > funded *)
    /\ amount >= authorizedClaims[chId]         (* GUARD 4: Monotonic increase *)
    /\ authorizedClaims' = [authorizedClaims EXCEPT ![chId] = amount]
    /\ UNCHANGED <<channels, ledgerSeq>>

(* ACTION: Redeem a claim *)
RedeemClaim(chId, claimAmount) ==
    /\ channels[chId] # NULL                    (* GUARD 1: Channel exists *)
    /\ channels[chId].state # "CLOSED"          (* GUARD 2: Not finalized *)
    /\ claimAmount <= authorizedClaims[chId]    (* GUARD 3: Must be authorized *)
    /\ claimAmount <= channels[chId].funded     (* GUARD 4: Cannot exceed funding *)
    /\ claimAmount > channels[chId].claimed     (* GUARD 5: Must be increasing *)
    /\ (channels[chId].state = "PENDING_CLOSE" =>   (* GUARD 6: If pending close, *)
            ledgerSeq < channels[chId].expiresAt)   (*          must not be expired *)
    /\ channels' = [channels EXCEPT ![chId].claimed = claimAmount]
    /\ UNCHANGED <<ledgerSeq, authorizedClaims>>

(* ACTION: Request channel closure - MUST have expiration delay *)
RequestClose(chId) ==
    /\ channels[chId] # NULL                    (* GUARD 1: Channel exists *)
    /\ channels[chId].state = "OPEN"            (* GUARD 2: Must be open *)
    /\ channels' = [channels EXCEPT 
            ![chId].state = "PENDING_CLOSE",
            ![chId].expiresAt = ledgerSeq + ExpirationDelay]  (* KEY: Delay! *)
    /\ UNCHANGED <<ledgerSeq, authorizedClaims>>

(* ACTION: Finalize closure - only AFTER expiration *)
FinalizeClose(chId) ==
    /\ channels[chId] # NULL                        (* GUARD 1: Channel exists *)
    /\ channels[chId].state = "PENDING_CLOSE"       (* GUARD 2: Must be pending *)
    /\ ledgerSeq >= channels[chId].expiresAt        (* GUARD 3: Must be expired *)
    /\ channels' = [channels EXCEPT ![chId].state = "CLOSED"]
    (* NOTE: Source receives (funded - claimed), NOT all funds! *)
    /\ UNCHANGED <<ledgerSeq, authorizedClaims>>

=============================================================================
```

### What LLM Generates with TLA+ Contract:

See `with_tlaplus/XRPLPaymentChannelService.java`

### Key Mapping Pattern the LLM Follows:

```
TLA+ Element              →  Java Implementation
─────────────────────────────────────────────────────────────
INVARIANT                 →  Validation in record constructor
                             + runtime verification method

GUARD (precondition)      →  if-check at method start
                             returning Failure with guard name

ATOMIC action             →  Lock-protected critical section

State transition          →  Create new immutable record
                             (never mutate existing state)

expiresAt = ledgerSeq +   →  long expiresAt = currentLedger + 
  ExpirationDelay              EXPIRATION_DELAY_LEDGERS;
```

---

## SIDE-BY-SIDE: Generated Code Comparison

### AuthorizeClaim - WITHOUT TLA+ Spec:

```java
// LLM generates this from informal requirements
public boolean authorizeClaim(String channelId, long amountDrops) {
    PaymentChannel channel = channels.get(channelId);
    if (channel == null) return false;
    
    // BUG: No check that amount <= funded!
    // BUG: No check that channel is OPEN!
    // BUG: No monotonicity check!
    
    channel.authorizedDrops = amountDrops;  // BUG: Not thread-safe!
    return true;
}
```

### AuthorizeClaim - WITH TLA+ Spec:

```java
// LLM generates this from TLA+ specification
public OperationResult authorizeClaim(String channelId, long amountDrops) {
    
    lock.writeLock().lock();  // Atomic transition (from TLA+)
    try {
        PaymentChannel channel = channels.get(channelId);
        
        // GUARD 1: channels[chId] ≠ NULL
        if (channel == null) {
            return OperationResult.failure(
                "Channel not found",
                "channels[chId] ≠ NULL");
        }
        
        // GUARD 2: channels[chId].state = "OPEN"
        if (channel.state() != ChannelState.OPEN) {
            return OperationResult.failure(
                "Channel is not open",
                "channels[chId].state = OPEN");
        }
        
        // GUARD 3: amount ≤ channels[chId].funded
        if (amountDrops > channel.fundedDrops()) {
            return OperationResult.failure(
                "Cannot authorize more than funded",
                "amount ≤ channels[chId].funded");
        }
        
        // GUARD 4: amount ≥ authorizedClaims[chId] (monotonicity)
        if (amountDrops < channel.authorizedDrops()) {
            return OperationResult.failure(
                "Must be monotonically increasing",
                "amount ≥ authorizedClaims[chId]");
        }
        
        // State transition: authorizedClaims' = [... EXCEPT ![chId] = amount]
        PaymentChannel updated = new PaymentChannel(
            channel.channelId(),
            channel.source(),
            channel.destination(),
            channel.fundedDrops(),
            channel.claimedDrops(),
            amountDrops,  // Updated!
            channel.state(),
            channel.expiresAtLedger(),
            channel.createdAtLedger()
        );
        
        channels.put(channelId, updated);
        return OperationResult.success(updated, "Authorized");
        
    } finally {
        lock.writeLock().unlock();
    }
}
```

---

## WHY TLA+ WORKS AS AN LLM CONTRACT

| Aspect | Informal Requirements | TLA+ Specification |
|--------|----------------------|-------------------|
| **Ambiguity** | "Source can authorize claims" - how much? any amount? | `amount <= channels[chId].funded` - precise bound |
| **Edge Cases** | Not mentioned | Explicit guards cover all cases |
| **Concurrency** | Assumed "thread-safe" | Atomic transitions clearly defined |
| **State Machine** | Implicit | Explicit states and transitions |
| **Invariants** | Developer must infer | Listed explicitly, must always hold |
| **Testability** | What to test? | Test each guard, each invariant |

---

## THE LLM PROMPTING PATTERN

### Template for Using TLA+ with LLMs:

```
You are implementing a {system} in {language}.

Here is the TLA+ formal specification that defines the EXACT behavior:

```tla
{TLA+ SPECIFICATION}
```

Implementation requirements:
1. Each INVARIANT must be enforced (validate in constructors, check at runtime)
2. Each GUARD in an action becomes a precondition check at method start
3. If ANY guard fails, return a failure result naming the violated guard
4. State transitions must be ATOMIC (use appropriate synchronization)
5. Create IMMUTABLE state objects - transitions create new instances
6. Include the TLA+ guard name in error messages for traceability

Generate the {language} implementation.
```

---

## BENEFITS FOR YOUR ORGANIZATION

1. **Onboarding**: New developers read spec to understand system behavior
2. **Code Review**: "Does this match the spec?" is an objective question  
3. **LLM Assistance**: AI generates correct code from unambiguous specs
4. **Testing**: Specs define what properties to test
5. **Documentation**: Spec IS the documentation (always in sync)
6. **Debugging**: When behavior is wrong, check which invariant/guard failed

---

## CONCLUSION

TLA+ specifications transform LLM code generation from:

❌ "Generate code that sounds right based on vague requirements"

✅ "Generate code that implements this precise mathematical contract"

The spec is the single source of truth that both humans and LLMs can follow.
