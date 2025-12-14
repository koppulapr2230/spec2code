package com.example.llm_generated.from_tlaplus;

import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

/**
 * XRPLEscrowService - Generated from TLA+ SPECIFICATION
 * 
 * This implementation precisely follows the TLA+ spec in XRPLEscrow.tla.
 * Each guard and invariant from the spec is implemented with clear traceability.
 * 
 * ============================================================================
 * TLA+ SPEC → JAVA MAPPING:
 * ============================================================================
 * 
 * INVARIANTS:
 *   AmountAlwaysPositive      → Validated in Escrow record constructor
 *   TimeConstraintsLogical    → Validated in Escrow record constructor
 *   SenderDestinationDiffer   → Validated in Escrow record constructor
 * 
 * ACTIONS:
 *   CreateEscrow  → createEscrow() method with G1-G5 guards
 *   FinishEscrow  → finishEscrow() method with G1-G4 guards
 *   CancelEscrow  → cancelEscrow() method with G1-G4 guards
 */
public class XRPLEscrowService {

    // ========================================================================
    // DATA TYPES (from TLA+ type definitions)
    // ========================================================================
    
    /**
     * Escrow states - maps to TLA+: EscrowState == {"CREATED", "FINISHED", "CANCELLED"}
     */
    public enum EscrowState {
        CREATED,
        FINISHED,
        CANCELLED
    }
    
    /**
     * Immutable Escrow record - maps to TLA+: EscrowRecord
     * 
     * INVARIANTS are enforced in the constructor:
     * - AmountAlwaysPositive: amountDrops > 0
     * - TimeConstraintsLogical: cancelAfter > finishAfter (when both set)
     * - SenderDestinationDiffer: sender != destination
     */
    public record Escrow(
        String escrowId,
        String sender,
        String destination,
        long amountDrops,
        long finishAfter,      // 0 = no constraint
        long cancelAfter,      // 0 = no constraint
        EscrowState state,
        long createdAtLedger
    ) {
        // Constructor validates TLA+ invariants
        public Escrow {
            // INVARIANT: AmountAlwaysPositive
            // TLA+: escrows[eid].amountDrops > 0
            if (amountDrops <= 0) {
                throw new IllegalArgumentException(
                    "INVARIANT VIOLATION (AmountAlwaysPositive): " +
                    "amountDrops must be > 0, got: " + amountDrops);
            }
            
            // INVARIANT: SenderDestinationDiffer
            // TLA+: escrows[eid].sender # escrows[eid].destination
            if (sender.equals(destination)) {
                throw new IllegalArgumentException(
                    "INVARIANT VIOLATION (SenderDestinationDiffer): " +
                    "sender and destination must be different");
            }
            
            // INVARIANT: TimeConstraintsLogical
            // TLA+: (finishAfter > 0 /\ cancelAfter > 0) => cancelAfter > finishAfter
            if (finishAfter > 0 && cancelAfter > 0 && cancelAfter <= finishAfter) {
                throw new IllegalArgumentException(
                    "INVARIANT VIOLATION (TimeConstraintsLogical): " +
                    "cancelAfter (" + cancelAfter + ") must be > finishAfter (" + finishAfter + ")");
            }
        }
    }
    
    /**
     * Result type for operations - explicit success/failure with guard info.
     */
    public sealed interface OperationResult permits 
            OperationResult.Success, OperationResult.Failure {
        
        record Success(Escrow escrow, String message, long payout) implements OperationResult {
            public Success(Escrow escrow, String message) {
                this(escrow, message, 0);
            }
        }
        
        record Failure(String reason, String tlaGuard) implements OperationResult {}
    }

    // ========================================================================
    // STATE VARIABLES (from TLA+ VARIABLES)
    // ========================================================================
    
    // TLA+: escrows in [EscrowIds -> EscrowRecord union {NULL}]
    private final Map<String, Escrow> escrows = new ConcurrentHashMap<>();
    
    // Per-escrow locks for atomic transitions
    private final Map<String, ReadWriteLock> escrowLocks = new ConcurrentHashMap<>();
    
    // TLA+: ledgerSeq \in Nat
    private final AtomicLong ledgerSeq = new AtomicLong(1);

    // ========================================================================
    // ACTION: CreateEscrow
    // ========================================================================
    
    /**
     * Create a new escrow.
     * 
     * Maps to TLA+ action:
     *   CreateEscrow(eid, sender, destination, amount, finishAfter, cancelAfter)
     * 
     * GUARDS:
     *   G1: escrows[eid] = NULL                    (ID available)
     *   G2: sender # destination                    (Different parties)
     *   G3: amount > 0                              (Positive amount)
     *   G4: finishAfter > 0 \/ cancelAfter > 0     (At least one constraint)
     *   G5: (both > 0) => cancelAfter > finishAfter (Logical time order)
     */
    public OperationResult createEscrow(
            String escrowId, 
            String sender, 
            String destination,
            long amountDrops, 
            long finishAfter, 
            long cancelAfter) {
        
        // GUARD G1: escrows[eid] = NULL
        // TLA+: escrows[eid] = NULL
        if (escrows.containsKey(escrowId)) {
            return new OperationResult.Failure(
                "Escrow ID already exists: " + escrowId,
                "escrows[eid] = NULL");
        }
        
        // GUARD G2: sender # destination
        // TLA+: sender # destination
        if (sender.equals(destination)) {
            return new OperationResult.Failure(
                "Sender and destination must be different",
                "sender # destination");
        }
        
        // GUARD G3: amount > 0
        // TLA+: amount > 0
        if (amountDrops <= 0) {
            return new OperationResult.Failure(
                "Amount must be positive, got: " + amountDrops,
                "amount > 0");
        }
        
        // GUARD G4: finishAfter > 0 \/ cancelAfter > 0
        // TLA+: (finishAfter > 0 \/ cancelAfter > 0)
        if (finishAfter <= 0 && cancelAfter <= 0) {
            return new OperationResult.Failure(
                "At least one time constraint (finishAfter or cancelAfter) must be set",
                "finishAfter > 0 \\/ cancelAfter > 0");
        }
        
        // GUARD G5: (finishAfter > 0 /\ cancelAfter > 0) => cancelAfter > finishAfter
        // TLA+: (finishAfter > 0 /\ cancelAfter > 0) => cancelAfter > finishAfter
        if (finishAfter > 0 && cancelAfter > 0 && cancelAfter <= finishAfter) {
            return new OperationResult.Failure(
                "cancelAfter (" + cancelAfter + ") must be > finishAfter (" + finishAfter + ")",
                "(finishAfter > 0 /\\ cancelAfter > 0) => cancelAfter > finishAfter");
        }
        
        // STATE TRANSITION
        // TLA+: escrows' = [escrows EXCEPT ![eid] = [...]]
        try {
            Escrow escrow = new Escrow(
                escrowId,
                sender,
                destination,
                amountDrops,
                finishAfter,
                cancelAfter,
                EscrowState.CREATED,
                ledgerSeq.get()
            );
            
            escrowLocks.put(escrowId, new ReentrantReadWriteLock(true));
            escrows.put(escrowId, escrow);
            
            System.out.println("[TLA+] Created escrow " + escrowId + 
                              ": " + sender + " -> " + destination + 
                              " (" + dropsToXrp(amountDrops) + " XRP)");
            
            return new OperationResult.Success(escrow, "Escrow created");
            
        } catch (IllegalArgumentException e) {
            return new OperationResult.Failure(e.getMessage(), "INVARIANT");
        }
    }

    // ========================================================================
    // ACTION: FinishEscrow
    // ========================================================================
    
    /**
     * Finish an escrow - release funds to destination.
     * 
     * Maps to TLA+ action:
     *   FinishEscrow(eid)
     * 
     * GUARDS:
     *   G1: escrows[eid] # NULL                           (Exists)
     *   G2: escrows[eid].state = "CREATED"                (In CREATED state)
     *   G3: finishAfter = 0 \/ ledgerSeq > finishAfter    (Time condition met)
     *   G4: cancelAfter = 0 \/ ledgerSeq < cancelAfter    (Not past cancel window)
     */
    public OperationResult finishEscrow(String escrowId) {
        
        ReadWriteLock lock = escrowLocks.get(escrowId);
        
        // GUARD G1: escrows[eid] # NULL
        // TLA+: escrows[eid] # NULL
        if (lock == null || !escrows.containsKey(escrowId)) {
            return new OperationResult.Failure(
                "Escrow not found: " + escrowId,
                "escrows[eid] # NULL");
        }
        
        lock.writeLock().lock();
        try {
            Escrow escrow = escrows.get(escrowId);
            long currentLedger = ledgerSeq.get();
            
            // GUARD G2: escrows[eid].state = "CREATED"
            // TLA+: escrows[eid].state = "CREATED"
            if (escrow.state() != EscrowState.CREATED) {
                return new OperationResult.Failure(
                    "Escrow is not in CREATED state (current: " + escrow.state() + ")",
                    "escrows[eid].state = \"CREATED\"");
            }
            
            // GUARD G3: escrows[eid].finishAfter = 0 \/ ledgerSeq > escrows[eid].finishAfter
            // TLA+: escrows[eid].finishAfter = 0 \/ ledgerSeq > escrows[eid].finishAfter
            // NOTE: Uses STRICT > (not >=) as per TLA+ spec!
            if (escrow.finishAfter() > 0 && currentLedger <= escrow.finishAfter()) {
                return new OperationResult.Failure(
                    "Cannot finish yet: ledger " + currentLedger + 
                    " must be > finishAfter " + escrow.finishAfter(),
                    "finishAfter = 0 \\/ ledgerSeq > finishAfter");
            }
            
            // GUARD G4: escrows[eid].cancelAfter = 0 \/ ledgerSeq < escrows[eid].cancelAfter
            // TLA+: escrows[eid].cancelAfter = 0 \/ ledgerSeq < escrows[eid].cancelAfter
            // CRITICAL: If past cancel window, finish is no longer allowed!
            if (escrow.cancelAfter() > 0 && currentLedger >= escrow.cancelAfter()) {
                return new OperationResult.Failure(
                    "Cancel window has opened: ledger " + currentLedger + 
                    " >= cancelAfter " + escrow.cancelAfter(),
                    "cancelAfter = 0 \\/ ledgerSeq < cancelAfter");
            }
            
            // STATE TRANSITION
            // TLA+: escrows' = [escrows EXCEPT ![eid].state = "FINISHED"]
            Escrow finished = new Escrow(
                escrow.escrowId(),
                escrow.sender(),
                escrow.destination(),
                escrow.amountDrops(),
                escrow.finishAfter(),
                escrow.cancelAfter(),
                EscrowState.FINISHED,
                escrow.createdAtLedger()
            );
            
            escrows.put(escrowId, finished);
            
            System.out.println("[TLA+] Finished escrow " + escrowId + 
                              ": " + dropsToXrp(escrow.amountDrops()) + 
                              " XRP released to " + escrow.destination());
            
            return new OperationResult.Success(finished, "Escrow finished", escrow.amountDrops());
            
        } finally {
            lock.writeLock().unlock();
        }
    }

    // ========================================================================
    // ACTION: CancelEscrow
    // ========================================================================
    
    /**
     * Cancel an escrow - return funds to sender.
     * 
     * Maps to TLA+ action:
     *   CancelEscrow(eid)
     * 
     * GUARDS:
     *   G1: escrows[eid] # NULL                   (Exists)
     *   G2: escrows[eid].state = "CREATED"        (In CREATED state)
     *   G3: escrows[eid].cancelAfter > 0          (Is cancellable)
     *   G4: ledgerSeq > escrows[eid].cancelAfter  (Cancel time reached)
     */
    public OperationResult cancelEscrow(String escrowId) {
        
        ReadWriteLock lock = escrowLocks.get(escrowId);
        
        // GUARD G1: escrows[eid] # NULL
        // TLA+: escrows[eid] # NULL
        if (lock == null || !escrows.containsKey(escrowId)) {
            return new OperationResult.Failure(
                "Escrow not found: " + escrowId,
                "escrows[eid] # NULL");
        }
        
        lock.writeLock().lock();
        try {
            Escrow escrow = escrows.get(escrowId);
            long currentLedger = ledgerSeq.get();
            
            // GUARD G2: escrows[eid].state = "CREATED"
            // TLA+: escrows[eid].state = "CREATED"
            if (escrow.state() != EscrowState.CREATED) {
                return new OperationResult.Failure(
                    "Escrow is not in CREATED state (current: " + escrow.state() + ")",
                    "escrows[eid].state = \"CREATED\"");
            }
            
            // GUARD G3: escrows[eid].cancelAfter > 0
            // TLA+: escrows[eid].cancelAfter > 0
            if (escrow.cancelAfter() <= 0) {
                return new OperationResult.Failure(
                    "Escrow is not cancellable (cancelAfter not set)",
                    "escrows[eid].cancelAfter > 0");
            }
            
            // GUARD G4: ledgerSeq > escrows[eid].cancelAfter
            // TLA+: ledgerSeq > escrows[eid].cancelAfter
            // NOTE: Uses STRICT > (not >=) as per TLA+ spec!
            if (currentLedger <= escrow.cancelAfter()) {
                return new OperationResult.Failure(
                    "Cannot cancel yet: ledger " + currentLedger + 
                    " must be > cancelAfter " + escrow.cancelAfter(),
                    "ledgerSeq > escrows[eid].cancelAfter");
            }
            
            // STATE TRANSITION
            // TLA+: escrows' = [escrows EXCEPT ![eid].state = "CANCELLED"]
            Escrow cancelled = new Escrow(
                escrow.escrowId(),
                escrow.sender(),
                escrow.destination(),
                escrow.amountDrops(),
                escrow.finishAfter(),
                escrow.cancelAfter(),
                EscrowState.CANCELLED,
                escrow.createdAtLedger()
            );
            
            escrows.put(escrowId, cancelled);
            
            System.out.println("[TLA+] Cancelled escrow " + escrowId + 
                              ": " + dropsToXrp(escrow.amountDrops()) + 
                              " XRP returned to " + escrow.sender());
            
            return new OperationResult.Success(cancelled, "Escrow cancelled", escrow.amountDrops());
            
        } finally {
            lock.writeLock().unlock();
        }
    }

    // ========================================================================
    // UTILITY METHODS
    // ========================================================================
    
    /**
     * Advance ledger sequence (time passing).
     * Maps to TLA+: AdvanceLedger action
     */
    public long advanceLedger() {
        return ledgerSeq.incrementAndGet();
    }
    
    public long advanceLedgers(int count) {
        return ledgerSeq.addAndGet(count);
    }
    
    public long getCurrentLedger() {
        return ledgerSeq.get();
    }
    
    public Optional<Escrow> getEscrow(String escrowId) {
        return Optional.ofNullable(escrows.get(escrowId));
    }
    
    private String dropsToXrp(long drops) {
        return String.format("%.6f", drops / 1_000_000.0);
    }
    
    /**
     * Verify all invariants hold for all escrows.
     */
    public boolean verifySafetyInvariant() {
        boolean valid = true;
        
        for (Escrow escrow : escrows.values()) {
            // AmountAlwaysPositive
            if (escrow.amountDrops() <= 0) {
                System.err.println("INVARIANT VIOLATION (AmountAlwaysPositive): " + escrow.escrowId());
                valid = false;
            }
            
            // SenderDestinationDiffer
            if (escrow.sender().equals(escrow.destination())) {
                System.err.println("INVARIANT VIOLATION (SenderDestinationDiffer): " + escrow.escrowId());
                valid = false;
            }
            
            // TimeConstraintsLogical
            if (escrow.finishAfter() > 0 && escrow.cancelAfter() > 0 &&
                escrow.cancelAfter() <= escrow.finishAfter()) {
                System.err.println("INVARIANT VIOLATION (TimeConstraintsLogical): " + escrow.escrowId());
                valid = false;
            }
        }
        
        if (valid) {
            System.out.println("[TLA+] All safety invariants verified ✓");
        }
        
        return valid;
    }
}
