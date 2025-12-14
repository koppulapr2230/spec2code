package com.example.llm_generated.informal;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * XRPLEscrowService - Generated from INFORMAL requirements
 * 
 * This is what an LLM typically generates from vague requirements.
 * It looks correct but contains several subtle bugs.
 * 
 * ============================================================================
 * BUGS IN THIS CODE (that TLA+ spec would have prevented):
 * ============================================================================
 * 
 * BUG 1: No validation that sender != destination
 *        → User can escrow funds to themselves (pointless, potential exploit)
 * 
 * BUG 2: No validation that cancelAfter > finishAfter
 *        → Can create impossible escrows (cancellable before finishable)
 * 
 * BUG 3: No requirement for at least one time constraint
 *        → Can create escrows with no conditions (stuck forever or instant)
 * 
 * BUG 4: Finish check uses >= instead of >
 *        → Off-by-one error in time comparison
 * 
 * BUG 5: Can finish escrow even after cancelAfter time
 *        → Race condition between finish and cancel
 * 
 * BUG 6: No atomicity - state can be corrupted by concurrent access
 *        → Race conditions in multi-threaded environment
 * 
 * BUG 7: Allows zero or negative amounts
 *        → Invalid escrows can be created
 */
public class XRPLEscrowService {

    // Simple escrow data structure
    public static class Escrow {
        public String escrowId;
        public String sender;
        public String destination;
        public long amountDrops;
        public long finishAfter;  // 0 means no constraint
        public long cancelAfter;  // 0 means no constraint
        public String state;      // "CREATED", "FINISHED", "CANCELLED"
        
        public Escrow(String escrowId, String sender, String destination,
                     long amountDrops, long finishAfter, long cancelAfter) {
            this.escrowId = escrowId;
            this.sender = sender;
            this.destination = destination;
            this.amountDrops = amountDrops;
            this.finishAfter = finishAfter;
            this.cancelAfter = cancelAfter;
            this.state = "CREATED";
        }
    }
    
    private final Map<String, Escrow> escrows = new ConcurrentHashMap<>();
    private long currentLedger = 1;
    
    /**
     * Create a new escrow.
     * 
     * BUG 1: No check that sender != destination
     * BUG 2: No check that cancelAfter > finishAfter (if both set)
     * BUG 3: No check that at least one time constraint exists
     * BUG 7: No check that amount > 0
     */
    public Escrow createEscrow(String escrowId, String sender, String destination,
                                long amountDrops, long finishAfter, long cancelAfter) {
        
        // Only checks if escrow exists
        if (escrows.containsKey(escrowId)) {
            System.out.println("Escrow already exists");
            return null;
        }
        
        // BUG: Missing validations that TLA+ spec would require:
        // - sender != destination (G2)
        // - amount > 0 (G3)
        // - finishAfter > 0 || cancelAfter > 0 (G5)
        // - cancelAfter > finishAfter when both set (G4)
        
        Escrow escrow = new Escrow(escrowId, sender, destination, 
                                   amountDrops, finishAfter, cancelAfter);
        escrows.put(escrowId, escrow);
        
        System.out.println("[INFORMAL] Created escrow " + escrowId);
        return escrow;
    }
    
    /**
     * Finish an escrow - release funds to destination.
     * 
     * BUG 4: Uses >= instead of > for time check
     * BUG 5: Doesn't check if we're past cancelAfter time
     * BUG 6: Not atomic - race condition possible
     */
    public boolean finishEscrow(String escrowId) {
        Escrow escrow = escrows.get(escrowId);
        
        if (escrow == null) {
            System.out.println("Escrow not found");
            return false;
        }
        
        if (!escrow.state.equals("CREATED")) {
            System.out.println("Escrow not in CREATED state");
            return false;
        }
        
        // BUG 4: Should be > not >= (off-by-one)
        // TLA+ spec says: ledgerSeq > finishAfter
        if (escrow.finishAfter > 0 && currentLedger >= escrow.finishAfter) {
            // Looks correct but it's wrong!
        }
        
        // BUG 5: Missing check - what if we're past cancelAfter?
        // TLA+ spec says: cancelAfter = 0 \/ ledgerSeq < cancelAfter
        // This allows finishing even when cancel window has opened!
        
        // BUG 6: Not atomic
        escrow.state = "FINISHED";
        
        System.out.println("[INFORMAL] Finished escrow " + escrowId + 
                          " - " + escrow.amountDrops + " drops to " + escrow.destination);
        return true;
    }
    
    /**
     * Cancel an escrow - return funds to sender.
     * 
     * BUG 4: Uses >= instead of > for time check  
     * BUG 6: Not atomic
     */
    public boolean cancelEscrow(String escrowId) {
        Escrow escrow = escrows.get(escrowId);
        
        if (escrow == null) {
            System.out.println("Escrow not found");
            return false;
        }
        
        if (!escrow.state.equals("CREATED")) {
            System.out.println("Escrow not in CREATED state");
            return false;
        }
        
        // Checks cancel time but with wrong comparison
        // BUG 4: Should be > not >= 
        if (escrow.cancelAfter == 0 || currentLedger < escrow.cancelAfter) {
            System.out.println("Cannot cancel yet");
            return false;
        }
        
        // BUG 6: Not atomic
        escrow.state = "CANCELLED";
        
        System.out.println("[INFORMAL] Cancelled escrow " + escrowId + 
                          " - " + escrow.amountDrops + " drops back to " + escrow.sender);
        return true;
    }
    
    public void advanceLedger() {
        currentLedger++;
    }
    
    public void advanceLedgers(int count) {
        currentLedger += count;
    }
    
    public long getCurrentLedger() {
        return currentLedger;
    }
    
    public Escrow getEscrow(String escrowId) {
        return escrows.get(escrowId);
    }
}
