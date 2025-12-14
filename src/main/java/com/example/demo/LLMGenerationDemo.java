package com.example.demo;

import com.example.llm_generated.from_tlaplus.XRPLEscrowService.OperationResult;

/**
 * Demonstration: LLM Code Generation with Informal vs TLA+ Specifications
 * 
 * This demo shows how TLA+ specs serve as precise contracts that help LLMs
 * generate correct code, vs informal requirements that lead to subtle bugs.
 */
public class LLMGenerationDemo {

    private static final long DROPS_PER_XRP = 1_000_000L;

    public static void main(String[] args) {
        System.out.println("═".repeat(80));
        System.out.println("  TLA+ AS CONTRACTS FOR LLM CODE GENERATION");
        System.out.println("═".repeat(80));
        System.out.println();
        System.out.println("This demo compares code generated from:");
        System.out.println("  1. INFORMAL requirements (vague English description)");
        System.out.println("  2. TLA+ SPECIFICATION (precise mathematical contract)");
        System.out.println();
        
        // Run all bug demonstrations
        demonstrateBug1_SenderEqualsDestination();
        demonstrateBug2_InvalidTimeConstraints();
        demonstrateBug3_NoTimeConstraints();
        demonstrateBug4_FinishAfterCancelWindow();
        demonstrateBug5_OffByOneTimeCheck();
        
        printSummary();
    }

    // ========================================================================
    // BUG 1: Sender = Destination (Escrow to yourself)
    // ========================================================================
    
    private static void demonstrateBug1_SenderEqualsDestination() {
        System.out.println();
        System.out.println("─".repeat(80));
        System.out.println("BUG 1: SENDER = DESTINATION");
        System.out.println("─".repeat(80));
        System.out.println();
        System.out.println("Scenario: Alice tries to create an escrow TO HERSELF.");
        System.out.println("This is pointless and could be an exploit vector.");
        System.out.println();
        
        // INFORMAL - Bug: Allows self-escrow
        System.out.println(">>> FROM INFORMAL PROMPT (buggy):");
        var informal = new com.example.llm_generated.informal.XRPLEscrowService();
        var result1 = informal.createEscrow("escrow-1", "Alice", "Alice", 
                                            100 * DROPS_PER_XRP, 10, 0);
        if (result1 != null) {
            System.out.println("    ⚠️  BUG: Self-escrow was ALLOWED!");
            System.out.println("    The informal prompt didn't specify this constraint.");
        }
        System.out.println();
        
        // TLA+ - Correct: Rejects self-escrow
        System.out.println(">>> FROM TLA+ SPEC (correct):");
        var tlaplus = new com.example.llm_generated.from_tlaplus.XRPLEscrowService();
        var result2 = tlaplus.createEscrow("escrow-1", "Alice", "Alice",
                                           100 * DROPS_PER_XRP, 10, 0);
        switch (result2) {
            case OperationResult.Failure f -> {
                System.out.println("    ✓ Self-escrow correctly REJECTED");
                System.out.println("    TLA+ Guard: " + f.tlaGuard());
            }
            case OperationResult.Success s -> 
                System.out.println("    Unexpected success!");
        }
    }

    // ========================================================================
    // BUG 2: cancelAfter <= finishAfter (Impossible escrow)
    // ========================================================================
    
    private static void demonstrateBug2_InvalidTimeConstraints() {
        System.out.println();
        System.out.println("─".repeat(80));
        System.out.println("BUG 2: INVALID TIME CONSTRAINTS (cancelAfter <= finishAfter)");
        System.out.println("─".repeat(80));
        System.out.println();
        System.out.println("Scenario: Create escrow with finishAfter=100, cancelAfter=50.");
        System.out.println("This creates an IMPOSSIBLE escrow - it becomes cancellable");
        System.out.println("before it can ever be finished!");
        System.out.println();
        
        // INFORMAL - Bug: Allows impossible time constraints
        System.out.println(">>> FROM INFORMAL PROMPT (buggy):");
        var informal = new com.example.llm_generated.informal.XRPLEscrowService();
        var result1 = informal.createEscrow("escrow-2", "Alice", "Bob",
                                            100 * DROPS_PER_XRP, 
                                            100,  // finishAfter
                                            50);  // cancelAfter (before finishAfter!)
        if (result1 != null) {
            System.out.println("    ⚠️  BUG: Impossible escrow was CREATED!");
            System.out.println("    finishAfter=100 but cancelAfter=50");
            System.out.println("    Bob can NEVER claim - Alice can cancel first!");
        }
        System.out.println();
        
        // TLA+ - Correct: Rejects illogical constraints
        System.out.println(">>> FROM TLA+ SPEC (correct):");
        var tlaplus = new com.example.llm_generated.from_tlaplus.XRPLEscrowService();
        var result2 = tlaplus.createEscrow("escrow-2", "Alice", "Bob",
                                           100 * DROPS_PER_XRP, 100, 50);
        switch (result2) {
            case OperationResult.Failure f -> {
                System.out.println("    ✓ Invalid time constraints correctly REJECTED");
                System.out.println("    TLA+ Guard: " + f.tlaGuard());
            }
            case OperationResult.Success s -> 
                System.out.println("    Unexpected success!");
        }
    }

    // ========================================================================
    // BUG 3: No time constraints at all
    // ========================================================================
    
    private static void demonstrateBug3_NoTimeConstraints() {
        System.out.println();
        System.out.println("─".repeat(80));
        System.out.println("BUG 3: NO TIME CONSTRAINTS");
        System.out.println("─".repeat(80));
        System.out.println();
        System.out.println("Scenario: Create escrow with no finishAfter and no cancelAfter.");
        System.out.println("This creates an escrow that can be finished IMMEDIATELY");
        System.out.println("and can NEVER be cancelled - funds could be stuck forever!");
        System.out.println();
        
        // INFORMAL - Bug: Allows no constraints
        System.out.println(">>> FROM INFORMAL PROMPT (buggy):");
        var informal = new com.example.llm_generated.informal.XRPLEscrowService();
        var result1 = informal.createEscrow("escrow-3", "Alice", "Bob",
                                            100 * DROPS_PER_XRP, 0, 0);
        if (result1 != null) {
            System.out.println("    ⚠️  BUG: Escrow with NO constraints was CREATED!");
            System.out.println("    This can be finished immediately - defeats the purpose.");
        }
        System.out.println();
        
        // TLA+ - Correct: Requires at least one constraint
        System.out.println(">>> FROM TLA+ SPEC (correct):");
        var tlaplus = new com.example.llm_generated.from_tlaplus.XRPLEscrowService();
        var result2 = tlaplus.createEscrow("escrow-3", "Alice", "Bob",
                                           100 * DROPS_PER_XRP, 0, 0);
        switch (result2) {
            case OperationResult.Failure f -> {
                System.out.println("    ✓ Missing constraints correctly REJECTED");
                System.out.println("    TLA+ Guard: " + f.tlaGuard());
            }
            case OperationResult.Success s -> 
                System.out.println("    Unexpected success!");
        }
    }

    // ========================================================================
    // BUG 4: Finish after cancel window opens (race condition)
    // ========================================================================
    
    private static void demonstrateBug4_FinishAfterCancelWindow() {
        System.out.println();
        System.out.println("─".repeat(80));
        System.out.println("BUG 4: FINISH AFTER CANCEL WINDOW OPENS");
        System.out.println("─".repeat(80));
        System.out.println();
        System.out.println("Scenario: Escrow with finishAfter=10, cancelAfter=20.");
        System.out.println("At ledger 25, BOTH finish and cancel should be possible.");
        System.out.println("But only CANCEL should work - the finish window has passed!");
        System.out.println();
        
        // INFORMAL - Bug: Allows finish after cancel window
        System.out.println(">>> FROM INFORMAL PROMPT (buggy):");
        var informal = new com.example.llm_generated.informal.XRPLEscrowService();
        informal.createEscrow("escrow-4", "Alice", "Bob", 100 * DROPS_PER_XRP, 10, 20);
        informal.advanceLedgers(25);  // Now at ledger 26
        System.out.println("    Current ledger: " + informal.getCurrentLedger());
        
        boolean finished = informal.finishEscrow("escrow-4");
        if (finished) {
            System.out.println("    ⚠️  BUG: Finish was ALLOWED at ledger 26!");
            System.out.println("    But cancelAfter=20 means cancel window opened at ledger 21.");
            System.out.println("    Destination should no longer be able to claim!");
        }
        System.out.println();
        
        // TLA+ - Correct: Rejects finish after cancel window
        System.out.println(">>> FROM TLA+ SPEC (correct):");
        var tlaplus = new com.example.llm_generated.from_tlaplus.XRPLEscrowService();
        tlaplus.createEscrow("escrow-4", "Alice", "Bob", 100 * DROPS_PER_XRP, 10, 20);
        tlaplus.advanceLedgers(25);  // Now at ledger 26
        System.out.println("    Current ledger: " + tlaplus.getCurrentLedger());
        
        var result = tlaplus.finishEscrow("escrow-4");
        switch (result) {
            case OperationResult.Failure f -> {
                System.out.println("    ✓ Finish correctly REJECTED (cancel window is open)");
                System.out.println("    TLA+ Guard: " + f.tlaGuard());
            }
            case OperationResult.Success s -> 
                System.out.println("    Unexpected success!");
        }
    }

    // ========================================================================
    // BUG 5: Off-by-one error in time comparison
    // ========================================================================
    
    private static void demonstrateBug5_OffByOneTimeCheck() {
        System.out.println();
        System.out.println("─".repeat(80));
        System.out.println("BUG 5: OFF-BY-ONE IN TIME COMPARISON");
        System.out.println("─".repeat(80));
        System.out.println();
        System.out.println("Scenario: Escrow with finishAfter=10.");
        System.out.println("At ledger EXACTLY 10, should finish be allowed?");
        System.out.println("TLA+ says: ledgerSeq > finishAfter (STRICT greater than)");
        System.out.println("So ledger 10 should NOT allow finish - need ledger 11!");
        System.out.println();
        
        // TLA+ - Shows correct behavior
        System.out.println(">>> FROM TLA+ SPEC (correct):");
        var tlaplus = new com.example.llm_generated.from_tlaplus.XRPLEscrowService();
        tlaplus.createEscrow("escrow-5", "Alice", "Bob", 100 * DROPS_PER_XRP, 10, 0);
        
        // Try at ledger exactly 10
        tlaplus.advanceLedgers(9);  // Now at ledger 10
        System.out.println("    At ledger " + tlaplus.getCurrentLedger() + " (== finishAfter):");
        
        var result1 = tlaplus.finishEscrow("escrow-5");
        switch (result1) {
            case OperationResult.Failure f -> 
                System.out.println("    ✓ Finish correctly REJECTED (need > not >=)");
            case OperationResult.Success s -> 
                System.out.println("    Unexpected success!");
        }
        
        // Advance to ledger 11
        tlaplus.advanceLedger();
        System.out.println("    At ledger " + tlaplus.getCurrentLedger() + " (> finishAfter):");
        
        var result2 = tlaplus.finishEscrow("escrow-5");
        switch (result2) {
            case OperationResult.Success s -> 
                System.out.println("    ✓ Finish correctly ALLOWED now");
            case OperationResult.Failure f -> 
                System.out.println("    Unexpected failure: " + f.reason());
        }
    }

    // ========================================================================
    // SUMMARY
    // ========================================================================
    
    private static void printSummary() {
        System.out.println();
        System.out.println("═".repeat(80));
        System.out.println("  SUMMARY: WHY TLA+ SPECS MATTER FOR LLM CODE GENERATION");
        System.out.println("═".repeat(80));
        System.out.println("""
        
        ┌─────────────────────────────────────────────────────────────────────────────┐
        │  INFORMAL PROMPT                      │  TLA+ SPEC PROMPT                   │
        ├─────────────────────────────────────────────────────────────────────────────┤
        │  "sender can create escrow"           │  sender # destination (Guard G2)   │
        │  → Allows self-escrow (BUG!)          │  → Rejects self-escrow ✓           │
        ├─────────────────────────────────────────────────────────────────────────────┤
        │  "has finish and cancel times"        │  cancelAfter > finishAfter (G5)    │
        │  → Allows illogical times (BUG!)      │  → Rejects illogical times ✓       │
        ├─────────────────────────────────────────────────────────────────────────────┤
        │  "can have time constraints"          │  finishAfter > 0 \\/ cancelAfter > 0│
        │  → Allows no constraints (BUG!)       │  → Requires at least one ✓         │
        ├─────────────────────────────────────────────────────────────────────────────┤
        │  "destination can finish"             │  ledgerSeq < cancelAfter (G4)      │
        │  → Finishes after cancel window (BUG!)│  → Respects cancel window ✓        │
        ├─────────────────────────────────────────────────────────────────────────────┤
        │  "after finish time"                  │  ledgerSeq > finishAfter (G3)      │
        │  → Uses >= (off-by-one BUG!)          │  → Uses > (correct) ✓              │
        └─────────────────────────────────────────────────────────────────────────────┘
        
        KEY INSIGHT:
        ============
        
        When you give an LLM a TLA+ specification:
        
        1. Every GUARD becomes a precondition check in the code
        2. Every INVARIANT becomes validation logic
        3. The LLM includes TLA+ guard names in error messages
        4. Edge cases are EXPLICIT, not implicit
        5. The spec is the single source of truth
        
        PROMPT PATTERN FOR LLM CODE GENERATION:
        =======================================
        
        "Implement this TLA+ specification in [language].
         Each guard becomes a precondition check.
         Each invariant is enforced in constructors.
         State transitions are atomic.
         Include TLA+ guard names in error messages."
         
         [PASTE TLA+ SPEC]
        
        This transforms LLM code generation from guesswork to precise implementation.
        """);
    }
}
