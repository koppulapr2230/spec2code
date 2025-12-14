# spec2code

## TLA+ Guardrails: Formal Specs for Reliable LLM Code Generation

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Java](https://img.shields.io/badge/Java-21+-orange.svg)](https://openjdk.org/)
[![TLA+](https://img.shields.io/badge/TLA%2B-Formal%20Methods-blue.svg)](https://lamport.azurewebsites.net/tla/tla.html)

**spec2code** demonstrates how TLA+ formal specifications serve as precise contracts that help LLMs generate correct, bug-free code—compared to vague English requirements that lead to subtle bugs.

---

## 🎯 The Problem

When you prompt an LLM with informal requirements like:

> "Write code for XRPL escrow - sender locks funds, destination can claim after a time"

You get **plausible-looking but subtly buggy code** because:
- Edge cases aren't specified
- Invariants are implicit
- Concurrency issues are ignored
- Time boundary conditions are ambiguous

## ✅ The Solution

Give the LLM a **TLA+ specification as a contract**:

```tla
FinishEscrow(eid) ==
    /\ escrows[eid] # NULL                    (* G1: Exists *)
    /\ escrows[eid].state = "CREATED"         (* G2: In CREATED state *)
    /\ ledgerSeq > escrows[eid].finishAfter   (* G3: Time condition - STRICT > *)
    /\ ledgerSeq < escrows[eid].cancelAfter   (* G4: Not past cancel window *)
    /\ escrows' = [escrows EXCEPT ![eid].state = "FINISHED"]
```

The LLM generates **precise, correct code** with:
- Every guard as a precondition check
- Every invariant enforced
- TLA+ references in error messages
- Atomic state transitions

---

## 📊 Results: 5 Bugs Caught

| Bug | Informal Prompt | TLA+ Spec |
|-----|-----------------|-----------|
| Self-escrow (Alice → Alice) | ⚠️ Allowed | ✓ Rejected |
| Invalid times (cancel ≤ finish) | ⚠️ Allowed | ✓ Rejected |
| No time constraints | ⚠️ Allowed | ✓ Rejected |
| Finish after cancel window | ⚠️ Allowed | ✓ Rejected |
| Off-by-one (≥ vs >) | ⚠️ Wrong | ✓ Correct |

---

## 🚀 Quick Start

### Prerequisites
- Java 21+
- (Optional) TLA+ Toolbox for viewing/model-checking specs

### Run the Demo

```bash
# Clone the repository
git clone https://github.com/YOUR_USERNAME/spec2code.git
cd spec2code

# Compile
./gradlew build

# Or without Gradle:
mkdir -p out
javac --enable-preview --release 21 -d out $(find src -name "*.java")

# Run the comparison demo
java --enable-preview -cp out com.example.demo.LLMGenerationDemo
```

### Expected Output

```
════════════════════════════════════════════════════════════════════════════════
  TLA+ AS CONTRACTS FOR LLM CODE GENERATION
════════════════════════════════════════════════════════════════════════════════

BUG 1: SENDER = DESTINATION
────────────────────────────────────────────────────────────────────────────────
>>> FROM INFORMAL PROMPT (buggy):
    ⚠️  BUG: Self-escrow was ALLOWED!

>>> FROM TLA+ SPEC (correct):
    ✓ Self-escrow correctly REJECTED
    TLA+ Guard: sender # destination
```

---

## 📁 Project Structure

```
spec2code/
├── docs/
│   └── TLA_PLUS_AS_LLM_CONTRACT.md    # Detailed explanation
│
├── prompts/
│   ├── 01_informal_prompt.txt          # ❌ Vague English requirements
│   └── 02_tlaplus_prompt.txt           # ✅ TLA+ spec as contract
│
├── specs/
│   └── XRPLEscrow.tla                  # Formal TLA+ specification
│
├── src/main/java/com/example/
│   ├── llm_generated/
│   │   ├── informal/                   # Code from informal prompt (buggy)
│   │   │   └── XRPLEscrowService.java
│   │   └── from_tlaplus/               # Code from TLA+ spec (correct)
│   │       └── XRPLEscrowService.java
│   └── demo/
│       └── LLMGenerationDemo.java      # Side-by-side comparison
│
├── build.gradle                        # Gradle build configuration
├── LICENSE                             # MIT License
└── README.md                           # This file
```

---

## 🔧 The Prompting Pattern

Use this template when asking LLMs to generate code:

```
Implement the following TLA+ specification in [language].

IMPLEMENTATION RULES:
1. Each GUARD becomes a precondition check at method start
2. Each INVARIANT is enforced in constructors + runtime verification
3. Return a Result type - include TLA+ guard name on failure
4. State transitions must be ATOMIC (use appropriate synchronization)
5. Use IMMUTABLE data structures for state

TLA+ SPECIFICATION:
```tla
[PASTE YOUR TLA+ SPEC HERE]
```

Generate the implementation with clear comments showing which 
TLA+ guard each check implements.
```

---

## 🔑 Key Mapping: TLA+ → Java

| TLA+ Element | Java Implementation |
|--------------|---------------------|
| `INVARIANT` | Validation in record constructor |
| `GUARD` (precondition) | `if` check returning `Failure` with guard name |
| `ATOMIC action` | Lock-protected critical section |
| `State transition` | Create new immutable record |
| `escrows' = [... EXCEPT ...]` | `new Record(...updatedField...)` |

### Example

**TLA+ Guard:**
```tla
/\ amount <= channels[chId].funded   (* Cannot authorize > funded *)
```

**Java Implementation:**
```java
// GUARD: amount <= channels[chId].funded
if (amountDrops > channel.fundedDrops()) {
    return OperationResult.failure(
        "Cannot authorize more than funded: " + amountDrops + " > " + channel.fundedDrops(),
        "amount <= channels[chId].funded");  // TLA+ guard reference
}
```

---

## 🌐 XRPL Context

This project uses **XRPL (XRP Ledger)** features as examples:

- **Escrow**: Lock XRP until time conditions are met
- **Payment Channels**: Off-ledger streaming payments (see `tlaplus-java-example/`)

These are real blockchain primitives with critical correctness requirements—perfect for demonstrating formal methods.

---

## 📚 Resources

### TLA+
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html) - Leslie Lamport's official site
- [Learn TLA+](https://learntla.com/) - Interactive tutorial
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html) - Free video lectures

### XRPL
- [XRPL Documentation](https://xrpl.org/)
- [Escrow](https://xrpl.org/escrow.html)
- [Payment Channels](https://xrpl.org/payment-channels.html)

### Formal Methods + LLMs
- [Using Formal Specifications with LLMs](https://arxiv.org/abs/2310.01234) (example paper)

---

## 🤝 Contributing

Contributions are welcome! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

Ideas for contributions:
- Add more XRPL features (Checks, NFTs, AMM)
- Port examples to other languages (Rust, Go, TypeScript)
- Add property-based tests derived from TLA+ specs
- Create GitHub Action for TLA+ model checking

---

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

---

## 🙏 Acknowledgments

- **Leslie Lamport** for creating TLA+
- **XRPL Community** for real-world use cases

---

<p align="center">
  <i>Turning formal specifications into reliable code, one guard at a time.</i>
</p>
