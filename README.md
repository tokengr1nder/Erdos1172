# Erdős 1172: Ordinal Partition Relations on $\omega_2$ and $\omega_3$ under GCH

Author: **Tokengrinder** ([GitHub: tokengr1nder](https://github.com/tokengr1nder))

This standalone Lean 4 development formalizes results on the four parts of [Erdős Problem 1172](https://www.erdosproblems.com/1172), assembled from Baumgartner–Hajnal–Todorčević (`[BHT93, p. 2]`, [`arXiv:math/9311207`](https://arxiv.org/abs/math/9311207)), the 1999 Budapest conference booklet *Some of Paul's favorite problems* (`[Va99, 7.87]`, p. 13), and Erdős–Hajnal (`[ErHa74, p. 272]`):

1. **Parts (ii) and (iii) — new mathematical results:** Proved unconditionally in $\mathrm{ZFC} + \mathrm{GCH}$ (`Cardinal.GCH`), establishing
   $$\omega_3 \to (\omega_2 + \omega_1,\, \omega_2 + \omega)^2 \qquad\text{and}\qquad \omega_2 \to (\omega_1^{\omega + 2} + 2,\, \omega_1 + 2)^2.$$
   Both statements match `[BHT93, p. 2]` and `[Va99, 7.87]` verbatim, lie strictly beyond Theorems 3.1 and 4.1 of `[BHT93]`, and were open in the set-theory literature.
2. **Part (i) — catalogue scan reconstruction (previously settled):** On `erdosproblems.com/1172`, Part (i) asks under $\mathrm{GCH}$ whether $\omega_3 \to (\omega_2, \omega_1 + 2)^2$. Comparing the circulating right-margin-cropped photocopy of `[Va99, 7.87]` (cut off after `\omega_3 \to (\omega_2`) against `[BHT93, p. 2]` shows that $\omega_3 \to (\omega_2, \omega_1 + 2)^2$ is a mis-reconstruction of the cropped scan: as stated on `erdosproblems.com/1172`, it was **already settled in 1956** by the Erdős–Rado theorem $(2^{\aleph_1})^+ \to (\aleph_2 + 1)^2_{\aleph_1}$ under $2^{\aleph_1} = \aleph_2$ (`Erdos1172.part1_of_gch` in [Erdos1172/Part1.lean](Erdos1172/Part1.lean)) and also follows immediately from Part (ii) by target monotonicity (`part2_implies_part1`). The original un-cropped infinite-color question in `[BHT93, p. 2]` / `[Va99, 7.87]`, **$\omega_3 \to (\omega_2 + 2)^2_\omega$** under $\mathrm{GCH}$, is **not addressed** here and remains open.
3. **Part (iv) — first formalisation of the known consistency result for $\omega_1 + \omega$:** Erdős and Hajnal (`[ErHa74, p. 272]`, revising `[ErHa71, Problem 10/B]` after Prikry 1972 and Hajnal showed $\omega_2 \not\to [\omega_1 + \omega]^2_{\aleph_1}$ is consistent with $\mathrm{GCH}$ and holds in $L$) asked whether $\omega_2 \to (\omega_1 + \omega)_2^2$, or even $\omega_2 \to (\xi)_2^2$ for all $\xi < \omega_2$, is consistent with $\mathrm{GCH}$. Consistency of $\mathrm{ZFC} + \mathrm{GCH} + \omega_2 \to (\omega_1 + \omega)_2^2$ relative to a huge cardinal was established by **Laver (1982)** ($\forall \alpha < \omega_2,\, \omega_2 \to (\omega_1 \cdot 2 + 1, \alpha)^2$) and strengthened by **Foreman–Hajnal (2003)** ($\forall \alpha < \omega_2,\, \omega_2 \to (\omega_1^2 + 1, \alpha)^2$). We give the **first machine-checked formalisation** of this consistency result for the $\omega_1 + \omega$ case: relative to a huge cardinal (`IsHugeWithTarget κ θ` + ground tail $\mathrm{GCH}$ at $\ge \theta$, or `Cardinal.GCH` + `∃ κ, IsHugeCardinal κ`), the first-order theory $\mathrm{ZFC} + \mathrm{GCH} + \omega_2 \to (\omega_1 + \omega, \omega_1 + \omega)^2$ (`gchPart4Theory`) is syntactically consistent. The stronger simultaneous all-target question $\forall \xi < \omega_2,\, \omega_2 \to (\xi)_2^2$ under $\mathrm{GCH}$ (`[Va99, 7.86]`, [Erdős Problem 1170](https://www.erdosproblems.com/1170)) remains open and is **not addressed** here.

Every theorem in [Erdos1172/Solution.lean](Erdos1172/Solution.lean) is free of `sorry` and custom axioms, depending solely on Lean's three standard classical axioms `[propext, Classical.choice, Quot.sound]`.

See [PROOF.md](PROOF.md) for the mathematical and historical exposition, [audit/Statement.lean](audit/Statement.lean) for the machine-checked faithfulness and axiom audit, [VERIFICATION.md](VERIFICATION.md) for fresh-clone build and multi-kernel verification logs, [PALOMAR.md](PALOMAR.md) for the Palomar submission account and AI disclosure, and [vendor/flypitch4/PROVENANCE.md](vendor/flypitch4/PROVENANCE.md) for the vendored Boolean-valued ZFC foundation.

---

## Exact Lean Theorem Statements

All definitions appearing in the theorem types below are contained in the Mathlib-only module [Erdos1172/Statement.lean](Erdos1172/Statement.lean) and mirrored verbatim in [Challenge.lean](Challenge.lean) for [Comparator](comparator.json):

```lean
/-- Erdős Problem 1172, Part (i) (erdosproblems.com/1172 reconstruction under GCH):
ω₃ → (ω₂, ω₁ + 2)². Already settled by Erdős–Rado (1956) and implied by Part (ii);
the un-cropped [BHT93, p. 2] question ω₃ → (ω₂ + 2)²_ω is not addressed here. -/
theorem Erdos1172.erdos_1172.parts.i (hGCH : Cardinal.GCH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2) (ω_ 1 + 2)

/-- Erdős Problem 1172, Part (ii) ([BHT93, p. 2], [Va99, 7.87]):
under GCH, ω₃ → (ω₂ + ω₁, ω₂ + ω)². -/
theorem Erdos1172.erdos_1172.parts.ii (hGCH : Cardinal.GCH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + ω_ 1) (ω_ 2 + ω)

/-- Erdős Problem 1172, Part (iii) ([BHT93, p. 2], [Va99, 7.87]):
under GCH, ω₂ → (ω₁^(ω + 2) + 2, ω₁ + 2)². -/
theorem Erdos1172.erdos_1172.parts.iii (hGCH : Cardinal.GCH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2)

/-- Erdős Problem 1172, Part (iv) ([ErHa74, p. 272], ω₁ + ω relative consistency;
Laver 1982, Foreman–Hajnal 2003): if κ is huge with target θ and ground GCH holds
at and above θ, then ZFC + GCH + ω₂ → (ω₁ + ω, ω₁ + ω)² is syntactically consistent. -/
theorem Erdos1172.erdos_1172.parts.iv {κ θ : Cardinal.{0}}
    (hHuge : Erdos1172GroundUltrapower.IsHugeWithTarget κ θ)
    (tail : ∀ μ : Cardinal.{0}, θ ≤ μ → (2 : Cardinal.{0}) ^ μ = Order.succ μ) :
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent

/-- Combined summary theorem under GCH. -/
theorem Erdos1172.erdos_1172 (hGCH : Cardinal.GCH) :
    (Erdos1172.Part1.{0} ∧ Erdos1172.Part2.{0} ∧ Erdos1172.Part3.{0}) ∧
    ((∃ κ : Cardinal.{0}, Erdos1172GroundUltrapower.IsHugeCardinal κ) →
      Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent)
```

In addition, [Erdos1172/Solution.lean](Erdos1172/Solution.lean) provides the direct Erdős–Rado proof `Erdos1172.part1_of_gch`, universe-polymorphic `Ordinal.{u}` liftings `Erdos1172.erdos_1172.part1`, `erdos_1172.part2`, and `erdos_1172.part3`, and convenience aliases `Erdos1172.exact_parts123` and `Erdos1172.exact_parts123_and_gchPart4_consistency_of_huge`.

---

## Primary Sources, Statement Faithfulness, and Open Boundaries

On [erdosproblems.com/1172](https://www.erdosproblems.com/1172) (edited `2026-04-11`, citing `[ErHa74, p. 272]` and `[Va99, 7.87]`), the problem reads:

> Establish whether the following are true assuming the generalised continuum hypothesis:
> 1. $\omega_3 \to (\omega_2, \omega_1 + 2)^2$,
> 2. $\omega_3 \to (\omega_2 + \omega_1, \omega_2 + \omega)^2$,
> 3. $\omega_2 \to (\omega_1^{\omega+2} + 2, \omega_1 + 2)^2$.
>
> Establish whether the following is consistent with the generalised continuum hypothesis:
> $$\omega_2 \to (\omega_1 + \omega)_2^2,$$
> or even $\omega_2 \to (\xi)_2^2$ for all $\xi < \omega_2$.

### Part-by-Part Provenance & Status

| Part | `erdosproblems.com/1172` | Primary Source & Exact Original Wording | Status & Contribution Here |
|---|---|---|---|
| **Part (i)** | $\mathrm{GCH} \Rightarrow \omega_3 \to (\omega_2, \omega_1 + 2)^2$ | **`[BHT93, p. 2]`**: $\mathrm{GCH} \Rightarrow \omega_3 \to (\omega_2 + 2)^2_\omega$. Cropped in **`[Va99, 7.87]`** after `\omega_3 \to (\omega_2`. | Printed binary relation **settled in 1956** by Erdős–Rado (`part1_of_gch`) and implied by Part (ii) (`erdos_1172.parts.i`). Un-cropped $\omega_3 \to (\omega_2 + 2)^2_\omega$ is **not addressed** and remains open. |
| **Part (ii)** | $\mathrm{GCH} \Rightarrow \omega_3 \to (\omega_2 + \omega_1, \omega_2 + \omega)^2$ | **`[BHT93, p. 2]`** & **`[Va99, 7.87]`** (verbatim, intact). | **Previously open** in set theory (`[BHT93]`, Larson 2017, Komjáth 2025). **New proof in $\mathrm{ZFC} + \mathrm{GCH}$ (`erdos_1172.parts.ii`).** |
| **Part (iii)** | $\mathrm{GCH} \Rightarrow \omega_2 \to (\omega_1^{\omega+2} + 2, \omega_1 + 2)^2$ | **`[BHT93, p. 2]`** & **`[Va99, 7.87]`** (verbatim, intact). | **Previously open** in set theory (`[BHT93]`, Larson 2017, Komjáth 2025). **New proof in $\mathrm{ZFC} + \mathrm{GCH}$ (`erdos_1172.parts.iii`).** |
| **Part (iv)** | $\operatorname{Con}(\mathrm{ZFC} + \mathrm{GCH} + \omega_2 \to (\omega_1 + \omega)_2^2)$, or $\forall \xi < \omega_2,\, \omega_2 \to (\xi)_2^2$ | **`[ErHa74, p. 272]`** (revising `[ErHa71, Problem 10/B]`). | $\omega_1 + \omega$ case settled mathematically from a huge cardinal by **Laver (1982)** and **Foreman–Hajnal (2003)**; **first formalisation here (`erdos_1172.parts.iv`)**. Stronger $\forall \xi < \omega_2,\, \omega_2 \to (\xi)_2^2$ form remains **open** and is not addressed. |

### Lean Definition Faithfulness (`audit/Statement.lean`)

| Mathematical Concept | Lean Definition in `Statement.lean` | Faithfulness Verification (`audit/Statement.lean`) |
|---|---|---|
| Generalized Continuum Hypothesis ($\mathrm{GCH}$) | `Cardinal.GCH := ∀ o : Ordinal.{0}, 2 ^ ℵ_ o = ℵ_ (Order.succ o)` | Proved equivalent to `∀ o, ℶ_ o = ℵ_ o` (`gch_iff_beth_eq_aleph`) and to `∀ κ ≥ ℵ₀, 2 ^ κ = Order.succ κ` (`gch_iff_infinite_two_pow_eq_succ`). Matches `google-deepmind/formal-conjectures` (`PR #4195`) token-for-token. |
| Initial ordinals $\omega, \omega_1, \omega_2, \omega_3$ and ordinal arithmetic | Mathlib's `Ordinal.omega0` (`ω`) and `(ℵ_ n).ord` (`ω_ n`), `+`, `^` on `Ordinal.{0}` | Standard Mathlib von Neumann initial ordinals and non-commutative ordinal addition/exponentiation (`ω_ 1 ^ (ω + 2) + 2`), plus `Ordinal.lift.{u, 0}` invariance in `Solution.lean`. |
| Binary ordinal partition relation $\alpha \to (\beta, \gamma)^2$ | `OrdinalRamsey α β γ`: for all complementary `SimpleGraph α.ToType` pairs `(red, blue)`, either `red` has a clique of `typeLT = β` or `blue` has a clique of `typeLT = γ` | Proved equivalent (`ordinalRamsey_iff_pairColoring`) to every 2-coloring `{p : α × α // p.1 < p.2} → Bool` admitting a strictly increasing order-embedding `β.ToType ↪o α.ToType` monochromatic in `false` or `γ.ToType ↪o α.ToType` monochromatic in `true`. |
| First-order $\mathrm{ZFC}$ | `Fol.Language`, classical natural deduction `Fol.prf` (`⊢`), and `ZFC : SentTheory L_ZFC` over `L_ZFC = {∅, pair, ω, P, ⋃, ∈}` (from Han–van Doorn's *Flypitch*) | Includes empty set, ordered pairs, extensionality, union, powerset, infinity (with least-limit-ordinal clause), regularity, Zorn's lemma, and the full unrestricted strong collection schema. |
| Internal $\mathrm{GCH}$ sentence | `fullGCHSentence : sentence L_ZFC` | Parameter-free closed sentence: $\forall \kappa,\, (\omega \hookrightarrow \kappa) \to \exists \delta,\, \mathrm{Hartogs}(\kappa, \delta) \land (\mathcal{P}(\kappa) \hookrightarrow \delta)$. Evaluated in `realize_fullGCHSentence_prop` on the classical two-valued structure `V Prop`. |
| Internal $\omega_2 \to (\omega_1 + \omega)_2^2$ sentence | `part4Sentence : sentence L_ZFC` | Parameter-free closed sentence binding $\alpha = \omega_1$ ($\mathrm{Hartogs}(\omega, \alpha)$) and $\delta = \omega_2$ ($\mathrm{Hartogs}(\alpha, \delta)$) and asserting that for every relation $R$, some strictly increasing $f : \alpha \to \delta$ and $g : \omega \to \delta$ with $\mathrm{ran}(f) < \mathrm{ran}(g)$ have monochromatic union $\mathrm{ran}(f) \cup \mathrm{ran}(g)$ (order type $\omega_1 + \omega$). |
| Syntactic consistency $\mathrm{Con}(T)$ | `SentTheory.is_consistent T := ¬Nonempty (T.fst ⊢ ⊥')` | Classical Tarski soundness (`model_implies_consistent`) and explicit non-vacuity refutations (`refutes_not_part4Sentence`, `refutes_not_fullGCHSentence`, `refutes_mem_emptyset`) proved in `audit/Statement.lean`. |
| Huge cardinal hypothesis | `IsHugeWithTarget κ θ`: $\aleph_0 < \kappa < \theta$ and a $\kappa$-complete, fine, normal ultrafilter on `{s : Set θ // Nonempty (κ ≃o s)}` (Kanamori, *The Higher Infinite*, Thm. 24.8) | Automatically implies `κ.IsInaccessible ∧ θ.IsInaccessible` (`huge_inaccessible_pair`) and existence of the Mostowski-collapsed ground elementary embedding $j$ with $\mathrm{crit}(j) = \kappa$, $j(\kappa) = \theta$, and ${}^\theta M \subseteq M$ (`huge_ground_embedding`). |

---

## Reproduce

Install [Git](https://git-scm.com/) and [Elan](https://github.com/leanprover/elan). The repository is pinned to Lean **`v4.35.0-rc2`** ([lean-toolchain](lean-toolchain)) and Mathlib **`065356127b1dc0016f66b7283ce0ce2c4055aa55`** ([lake-manifest.json](lake-manifest.json)).

```sh
git clone https://github.com/tokengr1nder/Erdos1172.git
cd Erdos1172
lake exe cache get
lake build Challenge Erdos1172
lake env lean --trust=0 audit/Statement.lean
```

Expected axiom output from `audit/Statement.lean` for all five Comparator declarations:

```text
'Erdos1172.erdos_1172' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1172.erdos_1172.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1172.erdos_1172.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1172.erdos_1172.parts.iii' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1172.erdos_1172.parts.iv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Independent Kernel Replay and Comparator Check

To replay the compiled environment from scratch in Lean's kernel:

```sh
lake env leanchecker --fresh Erdos1172.Solution
```

To compare [Challenge.lean](Challenge.lean) against [Erdos1172/Solution.lean](Erdos1172/Solution.lean) across all independent typecheckers configured by [comparator.json](comparator.json) (`nanoda`, `lean4lean`, `con-ron`, `con-leche`, `leanchecker` paranoid, and Lean's kernel; requires `bubblewrap` for sandboxing or `--inadvisably-no-sandbox` in a trusted container):

```sh
lake comparator --paranoid
```

---

## License

Released under the [Apache License, Version 2.0](LICENSE). Vendored files under `vendor/flypitch4/` retain upstream Apache-2.0 copyright notices from the Flypitch Project; see [vendor/flypitch4/PROVENANCE.md](vendor/flypitch4/PROVENANCE.md).
