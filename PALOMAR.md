# Palomar Submission Account

Responsible author and maintainer: **Tokengrinder**
([GitHub: tokengr1nder](https://github.com/tokengr1nder)).
The repository license is [Apache License 2.0](LICENSE).

## Declarations Selected by `comparator.json`

[comparator.json](comparator.json) compares three theorem declarations between [Challenge.lean](Challenge.lean) and [Erdos1172/Solution.lean](Erdos1172/Solution.lean):

1. `Erdos1172.erdos_1172.parts.ii` — `Cardinal.GCH → OrdinalRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω)` (new result matching `[BHT93, p. 2]` and `[Va99, 7.87]` verbatim).
2. `Erdos1172.erdos_1172.parts.iii` — `Cardinal.GCH → OrdinalRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2)` (new result matching `[BHT93, p. 2]` and `[Va99, 7.87]` verbatim).
3. `Erdos1172.erdos_1172.parts.iv` — `IsHugeWithTarget κ θ → (∀ μ ≥ θ, 2 ^ μ = Order.succ μ) → gchPart4Theory.is_consistent` (first formalisation of the Laver 1982 / Foreman–Hajnal 2003 relative consistency theorem for `ω₁ + ω`).

Permitted axioms are strictly `["propext", "Classical.choice", "Quot.sound"]`, with `enable_nanoda: true`.

## Scope, Primary Sources, and Open Boundaries

- **Parts (ii) and (iii) (new mathematical results):** Match Baumgartner, Hajnal, and Todorčević (`[BHT93, p. 2]`, `arXiv:math/9311207`) and `[Va99, 7.87]` (*Some of Paul's favorite problems*, Budapest 1999, p. 13) verbatim under `Cardinal.GCH`, and were open in the set-theory literature prior to these proofs (`[BHT93]`, Larson 2017, Komjáth 2025). Universe-polymorphic `Ordinal.{u}` liftings (`erdos_1172.part2`, `erdos_1172.part3`) are also proved in [Erdos1172/Solution.lean](Erdos1172/Solution.lean).
- **Part (iv) (first formalisation of known consistency for `ω₁ + ω`):** Answers the `ω₁ + ω` consistency question of Erdős–Hajnal (`[ErHa74, p. 272]`) relative to a huge cardinal, providing the first machine-checked formalisation of the consistency result established mathematically by Laver (1982) and strengthened by Foreman–Hajnal (2003). Neither the stronger simultaneous all-target question `∀ ξ < ω₂, ω₂ → (ξ)²_2` under `GCH` (`[Va99, 7.86]`, Erdős Problem 1170) nor a reduction of the large-cardinal hypothesis below a huge cardinal is claimed.
- **Original Part (i) (`ω₃ → (ω₂ + 2)²_ω` open; unselected `ω₂ + 1` remark):** In `[BHT93, p. 2]` (cropped at the right margin of `[Va99, 7.87]` after `\omega_3 \to (\omega_2`), the original Part (i) problem asks under `GCH` whether `ω₃ → (ω₂ + 2)²_ω` holds. The `erdosproblems.com/1172` cropped-scan binary reconstruction is omitted from this publication, and the original `ω₃ → (ω₂ + 2)²_ω` under `GCH` **remains open** and is not claimed. As an unselected remark in [Erdos1172/CountableNeighborhoodStep.lean](Erdos1172/CountableNeighborhoodStep.lean) (`omegaThree_to_omegaTwo_add_one_countable_of_gch`), our `< ℵ₂`-complete countable-color neighborhood ideal on `ω₃` recovers the known `ω₂ + 1` relation `GCH → ω₃ → (ω₂ + 1)²_ω` due to Erdős and Rado (`[ErRa56]`; `[BHT93, Theorem 2.1]`).
- **Statement audit ([audit/Statement.lean](audit/Statement.lean)):** Mechanically verifies equivalence of `Cardinal.GCH` with `ℶ_ o = ℵ_ o` and `2 ^ κ = κ⁺`; equivalence of `OrdinalRamsey` and `OrdinalCountableRamsey` with `[α]² → Bool` and `[α]² → ℕ` pair colorings and strictly increasing embeddings; derived inaccessibility and Mostowski-collapsed ground elementary embedding with $\theta$-closure from `IsHugeWithTarget`; and classical Tarski soundness, explicit refutation of negated sentences, and two-valued (`V Prop`) Tarski realization of `fullGCHSentence` and `part4Sentence`.

## Provenance and Prior Work

This repository contains a standalone, compacted Lean 4 proof development:

- **Mathematical literature:** Parts (ii) and (iii) present new proofs of open problems from Baumgartner–Hajnal–Todorčević (1993, p. 2) and `[Va99, 7.87]`, building on foundational partition-calculus concepts of Erdős–Rado (1956), Dushnik–Miller (1941), Erdős–Hajnal (1971, 1974), and Baumgartner–Hajnal–Todorčević (1993). Part (iv) formalizes and adapts huge-cardinal collapse and normal saturated/dense ideal techniques due to Kunen (1978), Laver (1982), Foreman–Hajnal (2003), Shioya, and Kanamori (*The Higher Infinite*, Theorem 24.8); see [PROOF.md](PROOF.md) and [formalization.yaml](formalization.yaml). No endorsement by any cited author or by the Erdős Problems catalogue is claimed.
- **Vendored formal library:** `vendor/flypitch4/` vendors a minimal 8-file subset of Ian Klatzco's Lean 4 port (`ianklatzco/flypitch` at `ad649f89e9f3107b7e2ea97a58b2eafdfc80b815`, Apache-2.0) of the Lean 3 *Flypitch* library by Jesse Han and Floris van Doorn (2019, Apache-2.0); see [vendor/flypitch4/PROVENANCE.md](vendor/flypitch4/PROVENANCE.md).
- **Related formalizations:** Unmerged PR `#3793` in `google-deepmind/formal-conjectures` records `sorry`-only statement stubs for Erdős 1172 using shared definitions from merged PR `#4195` (`Cardinal.GCH`, `Cardinal.CH`, `OrdinalRamsey`, which match ours token-for-token); it is independent and not imported here.

## Production, AI Involvement, and Review

Tokengrinder directed the mathematical targets, statement invariants, proof architecture, primary-source verification, compaction, audits, and publication criteria. AI agents (OpenAI Codex and Anthropic Claude / Google Gemini coding agents) made substantive mathematical and Lean 4 contributions across proof construction, refactoring, module-system porting, compaction, and documentation. Exact model build identifiers, complete prompt transcripts, per-agent token/cost totals, and wall-clock splits were not uniformly logged and are not reconstructed retrospectively.

Separate agent review, primary-source literature checks, and adversarial statement/axiom audit passes were conducted under user direction. **This is not a claim of independent human expert peer review.** Mechanical verification results (fresh-clone `lake build`, `--trust=0` statement audit, `leanchecker --fresh`, and multi-kernel `lake comparator --paranoid`) are recorded in [VERIFICATION.md](VERIFICATION.md).

## Submission Boundary

[Challenge.lean](Challenge.lean) imports **only** Lean core and pinned canonical Mathlib (`065356127b1dc0016f66b7283ce0ce2c4055aa55`) and uses `sorry` solely for the three Comparator target theorem declarations. [Erdos1172/Solution.lean](Erdos1172/Solution.lean) does not import `Challenge.lean`. Every `.lean` file in the repository uses Lean's `module` system and stays well under Palomar's 10,000-line per-file cap.
