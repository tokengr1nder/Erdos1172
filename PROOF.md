# Proof Architecture and Historical Context: Erdős Problem 1172 in Lean 4

**Author:** Tokengrinder ([GitHub: tokengr1nder](https://github.com/tokengr1nder))

---

## 1. Historical Provenance and Summary of Results

[Erdős Problem 1172](https://www.erdosproblems.com/1172) combines items from two classic set-theoretic problem lists: **Baumgartner, Hajnal, and Todorčević** (`[BHT93, p. 2]`, [`arXiv:math/9311207`](https://arxiv.org/abs/math/9311207)), condensed by the 18 Budapest conference editors (including A. Hajnal and P. Komjáth) in *Some of Paul's favorite problems* (`[Va99, 7.87]`, July 1999, p. 13), and **Erdős and Hajnal** (`[ErHa74, p. 272]`, Tarski Symposium, updating `[ErHa71, Problem 10 & 10/B, p. 23]`):

1. **Parts (ii) and (iii) — New Mathematical Results (`[BHT93, p. 2]`, `[Va99, 7.87]`):**
   - **Part (ii):** Does $\mathrm{GCH}$ imply $\omega_3 \to (\omega_2 + \omega_1,\, \omega_2 + \omega)^2$?
   - **Part (iii):** Does $\mathrm{GCH}$ imply $\omega_2 \to (\omega_1^{\omega + 2} + 2,\, \omega_1 + 2)^2$?
   Both relations appear intact in `[Va99, 7.87]`, match `[BHT93, p. 2]` verbatim, lie strictly beyond Theorems 3.1 and 4.1 of `[BHT93]` (Theorem 3.1 gives $(2^{<\kappa})^+ \to (\kappa + \xi)^2_k$ only for $\xi < \log \kappa$, stopping short of $\omega_2 + \omega_1$ at $\kappa = \omega_2$; Theorem 4.1 gives $(2^{<\kappa})^+ \to (\kappa^{\omega+2} + 1, (\kappa + n)_k)^2$ for $n, k < \omega$, stopping short of $\omega_2 + \omega$ at $\kappa = \omega_2$ and stopping at $+1$ rather than $+2$ at $\kappa = \omega_1$), and remained genuinely open in the set-theory literature (cf. Larson 2017, §3.16, pp. 33–34; Komjáth 2025). Here both are proved unconditionally in $\mathrm{ZFC} + \mathrm{GCH}$ (`Erdos1172.erdos_1172.parts.ii`, `Erdos1172.erdos_1172.parts.iii`).

2. **Part (iv) — First Formalisation of the Known Huge-Cardinal Consistency Result for $\omega_1 + \omega$:**
   - After Prikry (1972) and Hajnal (`[ErHa74, pp. 272, 285]`) proved $\operatorname{Con}(\mathrm{ZF}) \Rightarrow \operatorname{Con}(\mathrm{ZFC} + \mathrm{GCH} + \omega_2 \not\to [\omega_1 + \omega]^2_{\aleph_1})$ (which holds in Gödel's $L$ by Jensen), $\mathrm{GCH}$ alone cannot prove $\omega_2 \to (\omega_1 + \omega)_2^2$. Erdős and Hajnal (`[ErHa74, p. 272]`) therefore asked: *"Is $\omega_2 \to (\omega_1 + \omega)_2^2$ or even $\omega_2 \to (\xi)_2^2$ for $\xi < \omega_2$ consistent with G.C.H.?"*
   - Mathematically, the consistency of $\mathrm{ZFC} + \mathrm{GCH} + \omega_2 \to (\omega_1 + \omega)_2^2$ relative to a **huge cardinal** was established by **Laver (1982)** ($\forall \alpha < \omega_2,\, \omega_2 \to (\omega_1 \cdot 2 + 1, \alpha)^2$) and strengthened by **Foreman and Hajnal (2003)** ($\forall \alpha < \omega_2,\, \omega_2 \to (\omega_1^2 + 1, \alpha)^2$), as noted in `[Va99, 7.86]` and Komjáth (2025).
   - `Erdos1172.erdos_1172.parts.iv` provides the **first machine-checked formalisation** of this consistency theorem for the $\omega_1 + \omega$ case: if $\kappa$ is huge with target $\theta$ (`IsHugeWithTarget κ θ`) and ground $\mathrm{GCH}$ holds at and above $\theta$, then the first-order theory $\mathrm{ZFC} \cup \{\mathtt{fullGCHSentence},\, \mathtt{part4Sentence}\}$ (`gchPart4Theory`) is syntactically consistent.
   - Consistency of the stronger simultaneous all-target relation $\forall \xi < \omega_2,\, \omega_2 \to (\xi)_2^2$ with $\mathrm{GCH}$ (`[Va99, 7.86]`, [Erdős Problem 1170](https://www.erdosproblems.com/1170)) and any weakening of the large-cardinal hypothesis below a huge cardinal remain **open** and are not addressed here.

3. **Original Part (i) (`[BHT93, p. 2]` — Open) and the Unselected $\omega_2 + 1$ Remark:**
   - In the circulating photocopy of `[Va99, 7.87]`, the right margin of p. 13 is physically cropped immediately after `$\omega_3 \to (\omega_2$`. Matching `[Va99, 7.87]` word-for-word against `[BHT93, p. 2]` shows that the original Part (i) problem was the countably-infinite-color relation **$\omega_3 \to (\omega_2 + 2)^2_\omega$** under $\mathrm{GCH}$.
   - We omit `erdosproblems.com/1172`'s cropped-scan binary reconstruction from this publication, and record that the original `[BHT93, p. 2]` question **$\omega_3 \to (\omega_2 + 2)^2_\omega$ under $\mathrm{GCH}$ remains open** (as does `[BHT93, p. 2]`'s fourth item $\mathrm{CH} \implies \omega_3 \to (\omega_1 + \omega)^2_3$).
   - As an unselected background remark (`Erdos1172CountableNeighborhoodStep.omegaThree_to_omegaTwo_add_one_countable_of_gch` in `Erdos1172/CountableNeighborhoodStep.lean`), extending our $< \aleph_2$-complete neighborhood-ideal machinery on $\omega_3$ to $\mathbb{N}$-many colors recovers the weaker known relation **$\mathrm{GCH} \implies \omega_3 \to (\omega_2 + 1)^2_\omega$** due to **Erdős and Rado** (`[ErRa56]`; `[BHT93, Theorem 2.1]`: $(2^{<\kappa})^+ \to (\kappa + 1)^2_\mu$ for $\mu < \kappa$ at $\kappa = \omega_2, \mu = \omega$).

Every theorem in `Erdos1172/Solution.lean` is axiom-clean, depending only on `[propext, Classical.choice, Quot.sound]`.

---

## 2. Bibliography and Attribution

- **P. Erdős and R. Rado (1956):** *A partition calculus in set theory*, Bull. Amer. Math. Soc. **62**, 427–489 (`Erdos1172/ForMathlib/SetTheory/Ordinal/`).
- **P. Erdős and A. Hajnal (1971, 1974):** *Unsolved problems in set theory*, Proc. Sympos. Pure Math. **13.1**, 17–48; *Unsolved and solved problems in set theory*, Proc. Sympos. Pure Math. **25**, 269–287 (MR 0357122).
- **K. Prikry (1972):** *On a problem of Erdős, Hajnal and Rado*, Discrete Math. **2**, 51–59.
- **K. Kunen (1978):** *Saturated ideals*, J. Symbolic Logic **43**, 65–76.
- **R. Laver (1982):** *An $(\aleph_2, \aleph_2, \aleph_0)$-saturated ideal on $\omega_1$*, in *Logic Colloquium '80*, Studies in Logic and the Foundations of Mathematics **108**, North-Holland, 173–180.
- **J. E. Baumgartner, A. Hajnal, and S. Todorčević (1993):** *Extensions of the Erdős-Rado Theorem*, in *Finite and Infinite Combinatorics in Sets and Logic* (NATO ASI Series, Banff, 1991), Kluwer, 1–17 (`arXiv:math/9311207`; Theorem 2.1 and favorable-order ideas in `Erdos1172/BHT*.lean`).
- **B. Bollobás et al., eds. (`[Va99]`, 1999):** *Some of Paul's favorite problems*, Conference booklet, *"Paul Erdős and his mathematics"*, Budapest, July 1999, Section 7 (*Set theory*), items 7.86 and 7.87, p. 13.
- **M. Foreman and A. Hajnal (2003):** *A partition relation for successors of large cardinals*, Math. Ann. **325** (3), 583–623 (huge-cardinal collapse / normal ideal partition background for Part (iv), alongside M. Shioya's Easton/Lévy–Cohen collapse analysis).
- **A. Kanamori (2009):** *The Higher Infinite: Large Cardinals in Set Theory from Their Beginnings*, 2nd ed., Springer, §24, Theorem 24.8 (`IsHugeWithTarget κ θ`).
- **J. M. Han and F. van Doorn (2019, 2020, *Flypitch*) and I. Klatzco (`Flypitch4`):** Boolean-valued universe $\mathbf{V}^{(B)}$ (`bSet B`), Boolean forcing semantics for first-order logic (`Fol`), and Boolean soundness of $\mathrm{ZFC}$ (`vendor/flypitch4/`).
- **J. A. Larson (2017) & P. Komjáth (2025):** *In memoriam: James Earl Baumgartner (1943–2011)*, Arch. Math. Logic **56**, 877–909 (`arXiv:1705.02219`); *The Erdős–Hajnal Problem List*, Bull. Symb. Log. **31** (3), 418–461.

No endorsement of this formalization by any cited author or editor is claimed.

---

## 3. Neighborhood Ideals on $\omega_3$: Part (ii) and the Unselected $\omega_2 + 1$ Remark

### 3.1 Countable-Color Neighborhood Ideal (Unselected Remark: $\omega_3 \to (\omega_2 + 1)^2_\omega$)

In `Erdos1172/CountableNeighborhoodStep.lean`, given any countable-color pair coloring $\mathrm{col} : [\omega_3]^2 \to \mathbb{N}$, replacing binary graph atoms by `OmegaAtom := (ℕ ⊕ Unit) × W3` preserves `#OmegaAtom ≤ ℵ₃` and `#OmegaCode ≤ ℵ₃` under $\mathrm{GCH}$ ($2^{\aleph_1} = \aleph_2$, whence $\aleph_3^{\aleph_1} = \aleph_3$). Intersecting countably many atom-closure clubs on $\omega_3$ ($\mathrm{cof}(\omega_3) = \aleph_3 > \aleph_0$) yields stationary cofinality-$\omega_2$ `OmegaGoodCut` points $a < \omega_3$ whose local coded ideal `OmegaSmall r col a` is proper and $< \aleph_2$-complete (in particular countably complete). Because $\mathrm{Iio}(a) = \bigcup_{n \in \mathbb{N}} \{x < a : \mathrm{col}\{x, a\} = n\}$ is not `OmegaSmall` and $\#\mathbb{N} < \aleph_2$, some color fiber $n \in \mathbb{N}$ is `OmegaSmall`-positive; Zorn's lemma and $< \aleph_2$-completeness (`omegaExists_core`) extract a monochromatic $\omega_2$-core below $a$, and adjoining $a$ yields a color-$n$ set of order type $\omega_2 + 1$. This gives an unselected neighborhood-ideal proof (`omegaThree_to_omegaTwo_add_one_countable_of_gch`) of Erdős and Rado's relation $\mathrm{GCH} \implies \omega_3 \to (\omega_2 + 1)^2_\omega$ (`[ErRa56]`; `[BHT93, Theorem 2.1]`), while leaving the original Part (i) two-point apex question $\omega_3 \to (\omega_2 + 2)^2_\omega$ open.

### 3.2 Stable Pattern Spectra on $\omega_3$ (New Proof of Part (ii))

Under $\mathrm{GCH}$, $2^{\aleph_0} = \aleph_1$ and $2^{\aleph_1} = \aleph_2$, so subsets of initial segments of size $\le \aleph_1$ admit a code space `Code` of cardinality $\le \aleph_3$ (`Erdos1172/NeighborhoodCode.lean`). Given complementary graphs $(G, H)$ on $\omega_3$:

1. **Neighborhood Ideal and Derived Core (`NeighborhoodIdeal.lean`, `NeighborhoodIdealCore.lean`, `NeighborhoodDerivedIdeal.lean`):** Fixing a coding injection $r : \mathrm{Code} \hookrightarrow \omega_3$, we classify subsets of $\omega_3$ whose small blue/red neighborhood patterns fail to extend stationarily, forming a $\sigma$-complete / $< \aleph_2$-complete derived-ideal hierarchy.
2. **Favorable Closure and BHT Endpoint Selection (`BHT*.lean`, `NeighborhoodMixedBlocks.lean`, `NeighborhoodFavorableClosure.lean`):** If no blue $(\omega_2 + \omega)$-clique exists, blue extensions of order type $\omega$ above $\omega_2$-blocks are obstructed. Using Baumgartner–Hajnal–Todorčević favorable-order selection and $\mathrm{GCH}$ ramification ($2^{\aleph_1} = \aleph_2$), we isolate a closed unbounded locus where finite words of pattern codes stabilize (`NeighborhoodStableSpectrum.lean`).
3. **Future Transfer and Two-Block Assembly (`NeighborhoodFutureTransfer.lean`, `Part2NeighborhoodClosure.lean`):** When a pattern fails to extend across a club tail, `target_of_absent_extension` extracts a blue $(\omega_2 + \omega)$-clique; otherwise, transfinite diagonalization along the stable spectrum builds a red $(\omega_2 + \omega_1)$-clique, proving `part2_of_gch`.

---

## 4. Part (iii): $\omega_2 \to (\omega_1^{\omega + 2} + 2, \omega_1 + 2)^2$ under GCH (New Proof)

Part (iii) works one cardinal lower, at source $\omega_2$, under $\mathrm{CH}$ ($2^{\aleph_0} = \aleph_1$) and $2^{\aleph_1} = \aleph_2$, where the red target $\omega_1^{\omega + 2} + 2$ requires climbing past $\omega$ levels of $\omega_1$-powers plus two terminal steps against blue target $\omega_1 + 2$, overcoming the $+1$ ceiling of `[BHT93, Theorem 4.1]`.

1. **Two-Successor Bootstrap (`Part3RedCoreIdeal.lean`, `Part3RedCoreDerivedIdeal.lean`, `Part3TwoSuccessorBootstrap.lean`):** Suppose $(G, H)$ on $\omega_2$ avoids blue cliques of order type $\omega_1 + 2$. By analyzing the red-core neighborhood ideal on $\omega_2$, `part3_iff_core` reduces the $+2$ tail of $\omega_1^{\omega + 2} + 2$ to constructing stationary local red cores of order type $\omega_1^{\omega + 1}$ whose common red futures remain stationary.
2. **Hechler Profile Posets and Supported Short Covers (`Part3CliqueDecisionComposition.lean`–`Part3NamedStationaryShortCovers.lean`):** Finite and countable approximations to $\omega_1^{\omega + 1}$-configurations are organized into Hechler-style tree conditions with countable support. Using $2^{\aleph_0} = \aleph_1$, stationary pressing-down (Fodor's lemma) aligns local decision profiles on stationary subsets of $\mathrm{cof}(\omega_1) \cap \omega_2$.
3. **Ordered-Embedding Smallness and Pullback Core Traces (`Part3OrderedEmbeddingSmallness.lean`, `Part3OrderedCoreTrace.lean`, `Part3OrderedCoreExtraction.lean`, `Part3OrderedTraceRestriction.lean`):** Rather than tracking raw cardinality, smallness of a set of vertices relative to a tree of decisions is measured by the non-existence of order-preserving embeddings of $\omega_1^n$-towers (`hasOrderedEmbeddingBelow`). Pullback traces propagate non-smallness down the tower; failure at a stage yields a blue $\omega_1 + 2$ witness.
4. **Stationary Ordered-Loss Thinning and the $\omega$-Successor Factory (`Part3StationaryOrderedLoss.lean`, `Part3FullOrderedTraceLoss.lean`, `Part3StationaryOrderedThinning.lean`, `Part3FullStationaryOmegaSuccessor.lean`, `Part3Solution.lean`):** Countably many hereditary ordered-loss obstructions are eliminated simultaneously across a club on $\omega_2$. `omega_successor_factory` then glues an $\omega_1$-sequence of $\omega_1^{\omega + 1}$-blocks with two-point apex witnesses, establishing `part3_of_gch`.

---

## 5. Part (iv): Relative Consistency of $\mathrm{ZFC} + \mathrm{GCH} + \omega_2 \to (\omega_1 + \omega, \omega_1 + \omega)^2$ from a Huge Cardinal

Because $\mathrm{ZFC}$ cannot prove the existence of a model of $\mathrm{ZFC}$, Part (iv) is formulated syntactically over Flypitch's first-order language `L_ZFC` ($= \{\emptyset, \mathrm{pair}, \omega, \mathcal{P}, \bigcup, \in\}$) and natural-deduction proof system `Fol.prf`: given a huge cardinal $\kappa$ with target $\theta$ and ground tail $\mathrm{GCH}$ above $\theta$, the theory
$$\mathtt{gchPart4Theory} \;=\; \mathrm{ZFC} \;\cup\; \{\mathtt{fullGCHSentence},\, \mathtt{part4Sentence}\}$$
is consistent ($\neg(\mathtt{gchPart4Theory} \vdash \bot)$).

The formalisation adapts the huge-cardinal collapse and normal saturated/dense ideal paradigm of Kunen (1978), Laver (1982), Foreman–Hajnal (2003), and Shioya into three modular Boolean-valued layers.

### 5.1 Layer A: Closed First-Order Sentences and Internal Boolean-Valued Partition Theorem

1. **Parameter-Free Internal Cardinal & Partition Sentences (`Part4InternalCardinalLanguage.lean`–`Part4InternalGCHPart4Theory.lean`):**
   - `least_noninjecting_ordinal_f` expresses that $\alpha$ is the Hartogs ordinal of $\kappa$ ($\mathrm{Ord}(\alpha) \land (\alpha \not\hookrightarrow \kappa) \land \forall \gamma \in \alpha,\, \gamma \hookrightarrow \kappa$).
   - `fullGCHSentence` asserts $\forall \kappa,\, (\omega \hookrightarrow \kappa) \to \exists \delta,\, \mathrm{Hartogs}(\kappa, \delta) \land (\mathcal{P}(\kappa) \hookrightarrow \delta)$, capturing full $\mathrm{GCH}$ across all infinite sets without ground-cardinal constants.
   - `part4Sentence` binds $\alpha = \omega_1$ ($\mathrm{Hartogs}(\omega, \alpha)$) and $\delta = \omega_2$ ($\mathrm{Hartogs}(\alpha, \delta)$) and asserts that for every binary relation $R$, there exist strictly increasing functions $f : \alpha \to \delta$ and $g : \omega \to \delta$ with $\mathrm{ran}(f) < \mathrm{ran}(g)$ such that $\mathrm{ran}(f) \cup \mathrm{ran}(g)$ is monochromatic for $R$ (order type $\alpha + \omega = \omega_1 + \omega$).
   - Using internal Hartogs existence and uniqueness (`Part4InternalHartogs*.lean`, `Part4InternalOmegaTwo.lean`), `realize_fullGCHSentence` and `realize_part4Sentence` identify the Boolean truth values $\llbracket \mathtt{fullGCHSentence} \rrbracket_{\mathbf{V}^{(B)}}$ and $\llbracket \mathtt{part4Sentence} \rrbracket_{\mathbf{V}^{(B)}}$ in any nontrivial complete Boolean algebra $B$.
2. **Internal Partition Theorem from a Normal Dense Ideal (`Part4InternalDenseBasis.lean`–`Part4InternalPartitionFromIdeal.lean`):**
   Inside $\mathbf{V}^{(B)}$, suppose $\llbracket \mathrm{GCH} \rrbracket = \top$ and internal $\mathcal{P}(\omega_1)$ carries a normal, proper, $\omega_1$-complete ideal $I$ whose $I^+$-quotient admits a dense family indexed by $\check{\omega}_1$ / countable generic covers (equivalently a normal Boolean valuation factoring through a small dense basis). Given any internal graph name $R$ on $\omega_2$:
   - Each vertex $\xi < \omega_2$ colors $\omega_1$ and induces a behavior on the dense basis of $I^+$.
   - Countable generic fusion (`Part4InternalFusion*.lean`) and internal pressing-down (`Part4InternalNonstationaryPressingDown.lean`) either build an $\omega_1$-block + $\omega$-tail in color $0$ or an $\omega_1$-block + $\omega$-tail in color $1$ via the internal greedy selector (`Part4InternalGreedy*.lean`).
   - Consequently, `forces_gchPart4Theory_of_ideal` + Flypitch's `boolean_formula_soundness` reduce `gchPart4Theory.is_consistent` to exhibiting a nontrivial complete Boolean algebra $B$ forcing full $\mathrm{GCH}$ and carrying this internal normal dense-basis structure.

### 5.2 Layer B: Huge Cardinals and the Ground Mostowski Ultrapower

In `Part4GroundElementaryEmbedding.lean`, `Part4GroundFineSeed*.lean`, and `Part4HugeCardinalCharacterization.lean`:

- Following Kanamori (*The Higher Infinite*, Theorem 24.8), `IsHugeWithTarget κ θ` states $\aleph_0 < \kappa < \theta$ and the existence of a $\kappa$-complete (`CardinalInterFilter`), fine (`FineOn`), normal (`NormalOn`) ultrafilter $U$ on `HugeFiberSpace κ θ` ($= \{s \subseteq \theta \mid \mathrm{ot}(s) = \kappa\}$).
- `IsHugeWithTarget.inaccessible_pair` proves in $\mathrm{ZFC}$ (without extra hypotheses) that both $\kappa$ and $\theta$ are strongly inaccessible.
- Forming the ground `ZFSet` ultrapower by $U$ and taking its Mostowski collapse (`collapse U`) yields the transitive target class $M = \mathrm{targetClass}\,U$ and elementary map `groundEmbedding U` with critical point $\kappa$, image $j(\kappa) = \theta$, and closure under $\theta$-sequences (`IsHugeWithTarget.exists_groundEmbedding_closure`).

### 5.3 Layer C: Anonymous Internal Lévy–Cohen Collapse and Master-Condition Valuation

The final forcing construction (`Part4BooleanUltrapower*.lean`, `Part4Shioya*.lean`, `Part4Levy*.lean`, `Part4AnonymousInternalLevy*.lean`) builds the complete Boolean algebra `AmbientInternalLevy κ θ` and lifts the huge-cardinal ultrapower:

1. **Presentation-Invariant Easton/Lévy–Cohen Preparation (`Part4AnonymousInternalLevyCollapse.lean`, `Part4AnonymousInternalLevyReasonable.lean`):**
   At inaccessible stages below $\kappa$, Lévy–Cohen collapse factors are iterated anonymously so that stage algebras depend canonically on ordinals rather than external well-order choices, followed by an internal $\omega_1$-closed Lévy collapse of $[\kappa, \theta)$ turning $\check{\kappa}$ into internal $\omega_1$ and $\check{\theta}$ into internal $\omega_2$, commuting with an auxiliary Cohen factor (`AuxiliaryAmbient κ`).
2. **Full Internal GCH (`Part4AnonymousInternalLevyGCH.lean`, `Part4ShioyaBoundedDensePowerset.lean`, `Part4ShioyaIterationTailGCH.lean`):**
   - Below $\omega_1 = \check{\kappa}$: preservation of reals and $\kappa$-cc bounds force $\mathrm{CH}$ ($2^{\aleph_0} = \aleph_1$).
   - At $\omega_1 = \check{\kappa}$: $\theta$-cc and bounded dense size $\theta$ (with $\theta^{<\kappa} = \theta$ at inaccessible $\theta$) force $2^{\aleph_1} = \aleph_2$.
   - At $\mu \ge \theta$: bounded-label powerset counting combined with ground $\mathrm{GCH}$ above $\theta$ ($\forall \mu \ge \theta,\, 2^\mu = \mu^+$) forces $2^\lambda = \lambda^+$ for every higher internal cardinal $\lambda$, yielding `internalLevy_fullGCH_eq_top`.
3. **Boolean Ultrapower Lift, Master Graph, and Coding Compression (`Part4BooleanUltrapowerSubalgebra.lean`, `Part4LevyCohenBoundedUltrapowerIso.lean`, `Part4LevyMatchingAnonymousLift.lean`, `Part4AnonymousInternalLevyMaster.lean`–`Part4AnonymousInternalLevyValuation.lean`):**
   - Taking the Boolean ultrapower of the $\kappa$-stage algebra by $U$ stretches the $\kappa$-iteration to $\theta$; `levyCohenUltrapowerIso` and `exists_stageOne_anonymous_lift` identify the bounded ultrapower subalgebra with the first stage + tail collapse up to $\theta$.
   - Using ${}^\theta M \subseteq M$, the pointwise images $j(p)$ amalgamate into `< κ`-supported stage master graphs (`stageMasterGraph`) compatible with `< θ`-chains (`amalgamateChainWithMaster`).
   - Fresh-Cohen-bit coding (`code_small_ground_func_into_stage`) and lifted-witness compression (`compress_lifted_witness_to_R`) construct a $\kappa$-normal Boolean valuation into `AmbientInternalLevy κ θ` (`exists_internalLevy_fullGCH_and_normal_dense_ideal_of_hugeWithTarget`).
4. **Conclusion (`gchPart4Theory_is_consistent_of_hugeWithTarget`):**
   Combining `internalLevy_fullGCH_eq_top` with Layer A's `forces_gchPart4Theory_of_ideal` and Flypitch's Boolean soundness theorem establishes `gchPart4Theory.is_consistent`.
