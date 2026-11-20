# Verification Record

Checked on 20 November 2026 with Lean **`v4.35.0-rc2`** (`leanprover/lean4:v4.35.0-rc2`)
and Mathlib **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**.

## Summary of Mechanical Checks

1. **Fresh-clone build (`lake exe cache get && lake build Challenge Erdos1172`)**:
   - Completed cleanly with exit code `0` from a fresh Git clone with no pre-existing local build artifacts.
2. **Trust-zero statement and axiom audit (`lake env lean --trust=0 audit/Statement.lean`)**:
   - Completed cleanly with exit code `0`.
   - Every main theorem in `Erdos1172/Solution.lean` (`Erdos1172.erdos_1172`, `erdos_1172.parts.i`, `erdos_1172.parts.ii`, `erdos_1172.parts.iii`, `erdos_1172.parts.iv`, `part1_of_gch`, `erdos_1172.part1`, `erdos_1172.part2`, `erdos_1172.part3`, `exact_parts123`, `exact_parts123_and_gchPart4_consistency_of_huge`) and every faithfulness equivalence / refutation check in `audit/Statement.lean` depends exclusively on:
     ```text
     [propext, Classical.choice, Quot.sound]
     ```
3. **Fresh environment replay (`lake env leanchecker --fresh Erdos1172.Solution` and `Challenge`)**:
   - Replayed all imported declarations from scratch in Lean's kernel with exit code `0`.
4. **Multi-kernel Comparator check (`lake comparator --paranoid`)**:
   - Compared `Challenge` against `Erdos1172.Solution` across all five target declarations in [comparator.json](comparator.json) with permitted axioms `["propext", "Classical.choice", "Quot.sound"]` and `enable_nanoda: true`.
   - Accepted (`Your solution is okay!`, exit code `0`) by all six independent/paranoid checkers:
     - `nanoda` (`nanoda_bin`)
     - `Lean paranoid` (`leanchecker-paranoid` at maximal kernel paranoia)
     - `lean4lean` (`checked 21344 declarations`)
     - `con-leche` (`accepted 21343 declarations (--verified)`)
     - `con-ron` (`accepted 21343 declarations (--verified)`)
     - `Lean default`
5. **Source and Palomar preflight scan**:
   - Every `.lean` source file begins with `module`, uses LF line endings, and stays below Palomar's 10,000-line per-file limit (maximum file length: 5,472 lines in `vendor/flypitch4/Flypitch4/BvmExtras.lean`; `Challenge.lean`: 796 lines, 42.6 KiB, Mathlib-only imports).
   - Comment-stripped token scan across all proof `.lean` files found **0** occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `opaque`, `partial_fixpoint`, `ofReduceBool`, or `ofReduceNat` (outside the five deliberate statement placeholders in `Challenge.lean`).

See [README.md](README.md) for exact reproduction commands.
