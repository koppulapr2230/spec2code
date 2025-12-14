# Contributing to spec2code

Thank you for your interest in contributing to spec2code! This document provides guidelines and information for contributors.

## 🎯 Project Goals

spec2code demonstrates how TLA+ formal specifications help LLMs generate correct code. Contributions should align with this mission:

1. **Educational**: Help developers understand formal methods
2. **Practical**: Provide real-world, usable examples
3. **Demonstrable**: Show clear before/after comparisons

## 🚀 Ways to Contribute

### Add New Examples

We welcome new TLA+ specifications and their corresponding implementations:

1. **XRPL Features**: Checks, NFTs, AMM, Hooks
2. **General Distributed Systems**: Consensus, Replication, Queues
3. **Financial Protocols**: Order books, Swaps, Lending

For each new example, provide:
- TLA+ specification (`.tla` file)
- Informal prompt that produces buggy code
- TLA+ prompt that produces correct code
- Both implementations (informal vs TLA+-guided)
- Demo showing the bugs caught

### Port to Other Languages

The concepts apply to any language. Help by porting examples to:
- Rust
- Go
- TypeScript/JavaScript
- Python
- Kotlin

### Improve Documentation

- Fix typos and clarify explanations
- Add diagrams showing state transitions
- Create video tutorials
- Translate to other languages

### Add Testing

- Property-based tests derived from TLA+ invariants
- Integration with TLA+ model checker
- GitHub Actions for automated verification

## 📝 Contribution Process

### 1. Fork and Clone

```bash
git clone https://github.com/YOUR_USERNAME/spec2code.git
cd spec2code
git checkout -b feature/your-feature-name
```

### 2. Make Changes

Follow the existing code structure:

```
specs/              # TLA+ specifications
prompts/            # LLM prompts (informal and TLA+)
src/main/java/
  com/example/
    llm_generated/
      informal/     # Code from informal prompts
      from_tlaplus/ # Code from TLA+ specs
    demo/           # Demonstration classes
```

### 3. Test Your Changes

```bash
# Compile
./gradlew build

# Or manually
javac --enable-preview --release 21 -d out $(find src -name "*.java")

# Run demos
java --enable-preview -cp out com.example.demo.LLMGenerationDemo
```

### 4. Submit Pull Request

1. Push your branch to your fork
2. Open a Pull Request against `main`
3. Describe what your PR does and why
4. Link any related issues

## 📋 Code Style Guidelines

### TLA+ Specifications

```tla
(* Use block comments for action descriptions *)
ActionName(param1, param2) ==
    /\ guard1                    (* G1: Brief description *)
    /\ guard2                    (* G2: Brief description *)
    /\ state' = [state EXCEPT ![key] = newValue]
    /\ UNCHANGED <<otherVars>>
```

### Java Code

- Use Java records for immutable state
- Return `sealed interface` result types (Success/Failure)
- Include TLA+ guard names in comments and error messages
- Use locks for atomic transitions

```java
// GUARD G1: escrows[eid] # NULL
if (escrow == null) {
    return OperationResult.failure(
        "Escrow not found",
        "escrows[eid] # NULL");  // TLA+ reference
}
```

### Commit Messages

Use conventional commits:

```
feat: add XRPL Check specification and implementation
fix: correct off-by-one error in time comparison
docs: add diagram for escrow state transitions
test: add property-based tests for payment channels
```

## 🐛 Reporting Issues

When reporting bugs:

1. **Describe the issue**: What happened vs what you expected
2. **Reproduction steps**: How to trigger the bug
3. **Environment**: Java version, OS, etc.
4. **Logs/Output**: Include relevant error messages

## 💡 Feature Requests

When proposing features:

1. **Use case**: Why is this needed?
2. **Proposal**: What should be built?
3. **Alternatives**: What other approaches were considered?

## 📜 License

By contributing, you agree that your contributions will be licensed under the MIT License.

## 🙏 Recognition

Contributors will be recognized in:
- README.md acknowledgments
- Release notes
- Project documentation

Thank you for helping make formal methods more accessible!
