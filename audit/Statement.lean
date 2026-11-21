/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Solution
public import Erdos1172.ForMathlib.SetTheory.Cardinal.ContinuumHypothesis
public import Flypitch4.ZfcCore
public import Erdos1172.Part4InternalGCHPart4Theory

public section

/-!
# Statement Faithfulness and Axiom Audit for Erdős Problem 1172

This audit file mechanically verifies the faithfulness of every definition and theorem
appearing in [Challenge.lean](../Challenge.lean) and [Erdos1172/Solution.lean](../Erdos1172/Solution.lean)
against the published formulations of [Erdős Problem 1172](https://www.erdosproblems.com/1172)
(Baumgartner–Hajnal–Todorčević `[BHT93, p. 2]`, `arXiv:math/9311207`; the 1999 Budapest
problem booklet `[Va99, 7.87]`, p. 13; Erdős–Hajnal `[ErHa74, p. 272]`):

1. **Generalized Continuum Hypothesis (`Cardinal.GCH`)**:
   - Equivalent to `∀ o, ℶ_ o = ℵ_ o` (`gch_iff_beth_eq_aleph`) and to `2 ^ κ = κ⁺` for every
     infinite cardinal `κ` (`gch_iff_infinite_two_pow_eq_succ`).
2. **Binary & Countable-Color Ordinal Partition Relations (`OrdinalRamsey α β γ` and
   `OrdinalCountableRamsey α β`)**:
   - `OrdinalRamsey α β γ` is equivalent to the standard `[α]² → {0, 1}` coloring formulation
     with strictly increasing embeddings `β.ToType ↪o α.ToType` and `γ.ToType ↪o α.ToType`
     (`ordinalRamsey_iff_pairColoring`), instantiated at Parts (ii) and (iii)
     (`parts_ii_pairColoring`, `parts_iii_pairColoring`).
   - `OrdinalCountableRamsey α β` is equivalent to the standard `[α]² → ℕ` countable-color
     formulation with strictly increasing embeddings `β.ToType ↪o α.ToType`
     (`ordinalCountableRamsey_iff_pairColoring`), instantiated at the unselected remark
     `ω₃ → (ω₂ + 1)²_ω` (`omegaThree_to_omegaTwo_add_one_pairColoring`, due to Erdős–Rado
     `[ErRa56]` / `[BHT93, Theorem 2.1]`), while the original `[BHT93, p. 2]` Part (i) question
     `ω₃ → (ω₂ + 2)²_ω` under `GCH` remains open.
3. **Huge Cardinal Hypothesis (`IsHugeWithTarget κ θ` / `IsHugeCardinal κ`)**:
   - Automatically entails strong inaccessibility of both `κ` and `θ` (`huge_inaccessible_pair`),
     and yields the ground ultrapower elementary embedding `j : ZFSet.{0} → targetClass U`
     with critical point `κ`, `j(κ) = θ`, and `θ`-sequence closure (`huge_ground_embedding`).
4. **First-Order `ZFC + GCH + ω₂ → (ω₁ + ω, ω₁ + ω)²` Theory (`gchPart4Theory`)**:
   - Classical Tarski soundness (`model_implies_consistent`): any classical `L_ZFC`-structure
     satisfying `gchPart4Theory` witnesses `gchPart4Theory.is_consistent`.
   - Explicit refutation checks (`refutes_not_part4Sentence`, `refutes_not_fullGCHSentence`,
     `refutes_mem_emptyset`) confirming that `gchPart4Theory` non-vacuously entails
     `part4Sentence`, `fullGCHSentence`, and `ZFC`'s axioms.
   - Exact two-valued (`V Prop`) Tarski realization of `fullGCHSentence` and `part4Sentence`
     (`realize_fullGCHSentence_prop`, `realize_part4Sentence_prop`).
5. **Axiom Audit**:
   - `#print axioms` on all three `comparator.json` endpoints (`parts.ii`, `parts.iii`, `parts.iv`),
     the unselected remark `omegaThree_to_omegaTwo_add_one_countable_of_gch`, and every audit
     theorem below confirms dependence solely on `[propext, Classical.choice, Quot.sound]`.
-/

namespace StatementAudit

open Cardinal Ordinal Fol Erdos1172 Erdos1172GroundUltrapower
open Erdos1172Part4InternalFullGCHSentence Erdos1172Part4InternalPartitionSentence
open Erdos1172Part4InternalGCHTheory

/-! ## 1. Faithfulness of `Cardinal.GCH` -/

theorem gch_iff_beth_eq_aleph :
    Cardinal.GCH ↔ ∀ o : Ordinal.{0}, ℶ_ o = ℵ_ o :=
  Cardinal.GCH_iff_beth_eq_aleph

theorem gch_iff_infinite_two_pow_eq_succ :
    Cardinal.GCH ↔ ∀ κ : Cardinal.{0}, ℵ₀ ≤ κ → (2 : Cardinal.{0}) ^ κ = Order.succ κ := by
  constructor
  · intro h κ hκ
    obtain ⟨o, rfl⟩ := Cardinal.mem_range_aleph_iff.mpr hκ
    rw [h o, Cardinal.succ_aleph, Order.succ_eq_add_one]
  · intro h o
    rw [h (ℵ_ o) (Cardinal.aleph0_le_aleph o), Cardinal.succ_aleph, Order.succ_eq_add_one]

/-! ## 2. Faithfulness of `OrdinalRamsey` & `OrdinalCountableRamsey` -/

/-- Textbook `[α]² → {false, true}` pair-coloring formulation of `α → (β, γ)²`. -/
def PairColoringRamsey (α β γ : Ordinal.{0}) : Prop :=
  ∀ c : {p : α.ToType × α.ToType // p.1 < p.2} → Bool,
    (∃ f : β.ToType ↪o α.ToType, ∀ x y (h : x < y), c ⟨(f x, f y), f.strictMono h⟩ = false) ∨
    (∃ g : γ.ToType ↪o α.ToType, ∀ x y (h : x < y), c ⟨(g x, g y), g.strictMono h⟩ = true)

private noncomputable def embeddingOfTypeLT {α β : Ordinal.{0}} {s : Set α.ToType}
    (htype : typeLT s = β) : β.ToType ↪o α.ToType :=
  (OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp
    ((Ordinal.type_toType β).trans htype.symm)))).toOrderEmbedding.trans
    (OrderEmbedding.subtype (· ∈ s))

private theorem embeddingOfTypeLT_mem {α β : Ordinal.{0}} {s : Set α.ToType}
    (htype : typeLT s = β) (x : β.ToType) : embeddingOfTypeLT htype x ∈ s :=
  Subtype.prop _

theorem ordinalRamsey_iff_pairColoring (α β γ : Ordinal.{0}) :
    OrdinalRamsey α β γ ↔ PairColoringRamsey α β γ := by
  classical
  constructor
  · intro h c
    let red : SimpleGraph α.ToType :=
      { Adj := fun x y =>
          if hxy : x < y then c ⟨(x, y), hxy⟩ = false
          else if hyx : y < x then c ⟨(y, x), hyx⟩ = false
          else False
        symm := ⟨fun x y h1 => by
          by_cases hxy : x < y
          · simpa [hxy, lt_asymm hxy] using h1
          · by_cases hyx : y < x <;> simp_all⟩
        loopless := ⟨fun x hx => by simp at hx⟩ }
    obtain ⟨s, hs, htype⟩ | ⟨s, hs, htype⟩ := h red redᶜ isCompl_compl
    · let f := embeddingOfTypeLT htype
      refine Or.inl ⟨f, fun x y hxy => ?_⟩
      have hadj := hs (embeddingOfTypeLT_mem htype x) (embeddingOfTypeLT_mem htype y) (f.strictMono hxy).ne
      change (if h : f x < f y then c ⟨(f x, f y), h⟩ = false
              else if h' : f y < f x then c ⟨(f y, f x), h'⟩ = false else False) at hadj
      rw [dif_pos (f.strictMono hxy)] at hadj
      exact hadj
    · let g := embeddingOfTypeLT htype
      refine Or.inr ⟨g, fun x y hxy => ?_⟩
      have h2 := (SimpleGraph.compl_adj _ _ _ |>.mp
        (hs (embeddingOfTypeLT_mem htype x) (embeddingOfTypeLT_mem htype y) (g.strictMono hxy).ne)).2
      change ¬(if h : g x < g y then c ⟨(g x, g y), h⟩ = false
               else if h' : g y < g x then c ⟨(g y, g x), h'⟩ = false else False) at h2
      rw [dif_pos (g.strictMono hxy)] at h2
      exact Bool.eq_true_of_not_eq_false h2
  · intro h red blue hcompl
    let c : {p : α.ToType × α.ToType // p.1 < p.2} → Bool :=
      fun p => if red.Adj p.1.1 p.1.2 then false else true
    obtain ⟨f, hf⟩ | ⟨g, hg⟩ := h c
    · refine Or.inl ⟨Set.range f, ?_, f.orderIso.ordinalType_congr.symm.trans (Ordinal.type_toType β)⟩
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
      rcases lt_trichotomy x y with hlt | rfl | hgt
      · by_contra hnr; have hc := hf x y hlt; simp [c, hnr] at hc
      · exact absurd rfl hne
      · refine red.adj_symm (by by_contra hnr; have hc := hf y x hgt; simp [c, hnr] at hc)
    · refine Or.inr ⟨Set.range g, ?_, g.orderIso.ordinalType_congr.symm.trans (Ordinal.type_toType γ)⟩
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨hne, fun hr => ?_⟩
      rcases lt_trichotomy x y with hlt | rfl | hgt
      · have hc := hg x y hlt; simp [c, hr] at hc
      · exact absurd rfl hne
      · have hc := hg y x hgt; simp [c, red.adj_symm hr] at hc

/-- Textbook `[α]² → ℕ` pair-coloring formulation of `α → (β)²_ω`. -/
def PairColoringCountableRamsey (α β : Ordinal.{0}) : Prop :=
  ∀ c : {p : α.ToType × α.ToType // p.1 < p.2} → ℕ,
    ∃ (n : ℕ) (f : β.ToType ↪o α.ToType),
      ∀ x y (h : x < y), c ⟨(f x, f y), f.strictMono h⟩ = n

theorem ordinalCountableRamsey_iff_pairColoring (α β : Ordinal.{0}) :
    OrdinalCountableRamsey α β ↔ PairColoringCountableRamsey α β := by
  classical
  constructor
  · intro h c
    let colFun : α.ToType → α.ToType → ℕ := fun x y =>
      if hxy : x < y then c ⟨(x, y), hxy⟩
      else if hyx : y < x then c ⟨(y, x), hyx⟩
      else 0
    have hsymm (x y) : colFun x y = colFun y x := by
      dsimp only [colFun]
      by_cases hxy : x < y
      · simp [hxy, lt_asymm hxy]
      · by_cases hyx : y < x <;> simp [hxy, hyx]
    obtain ⟨n, s, hs, htype⟩ := h (Sym2.lift ⟨colFun, hsymm⟩)
    let f := embeddingOfTypeLT htype
    refine ⟨n, f, fun x y hxy => ?_⟩
    have hlt : f x < f y := f.strictMono hxy
    simpa [colFun, hlt] using hs (f x) (embeddingOfTypeLT_mem htype x) (f y) (embeddingOfTypeLT_mem htype y) hlt.ne
  · intro h col
    obtain ⟨n, f, hf⟩ := h (fun p => col s(p.1.1, p.1.2))
    refine ⟨n, Set.range f, ?_, f.orderIso.ordinalType_congr.symm.trans (Ordinal.type_toType β)⟩
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact hf x y hlt
    · exact absurd rfl hne
    · rw [Sym2.eq_swap]; exact hf y x hgt

theorem omegaThree_to_omegaTwo_add_one_pairColoring (hGCH : Cardinal.GCH) :
    PairColoringCountableRamsey (ω_ 3) (ω_ 2 + 1) :=
  (ordinalCountableRamsey_iff_pairColoring _ _).mp
    (Erdos1172CountableNeighborhoodStep.omegaThree_to_omegaTwo_add_one_countable_of_gch hGCH)

theorem parts_ii_pairColoring (hGCH : Cardinal.GCH) :
    PairColoringRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω) :=
  (ordinalRamsey_iff_pairColoring _ _ _).mp (Erdos1172.erdos_1172.parts.ii hGCH)

theorem parts_iii_pairColoring (hGCH : Cardinal.GCH) :
    PairColoringRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) :=
  (ordinalRamsey_iff_pairColoring _ _ _).mp (Erdos1172.erdos_1172.parts.iii hGCH)

/-! ## 3. Faithfulness of `IsHugeWithTarget` -/

theorem huge_inaccessible_pair {κ θ : Cardinal.{0}} (h : IsHugeWithTarget κ θ) :
    κ.IsInaccessible ∧ θ.IsInaccessible :=
  h.inaccessible_pair

theorem huge_ground_embedding {κ θ : Cardinal.{0}} (h : IsHugeWithTarget κ θ) :
    ∃ U : Ultrafilter (HugeFiberSpace κ θ),
      ∃ _ : CountableInterFilter (U : Filter (HugeFiberSpace κ θ)),
        (∀ α < κ.ord, (groundEmbedding U α.toZFSet).val = α.toZFSet) ∧
        κ.ord.toZFSet ∈ (groundEmbedding U κ.ord.toZFSet).val ∧
        (groundEmbedding U κ.ord.toZFSet).val = θ.ord.toZFSet ∧
        ∀ S F : ZFSet.{0}, ZFSet.IsFunc θ.ord.toZFSet S F →
          (∀ (ξ : θ.ord.ToType) y, ZFSet.pair ξ.toOrd.val.toZFSet y ∈ F → y ∈ targetClass U) →
          F ∈ targetClass U :=
  h.exists_groundEmbedding_closure

/-! ## 4. Soundness, Non-Vacuity, and Two-Valued Semantics of `gchPart4Theory` -/

/-- Any classical Tarski `L_ZFC`-model of `gchPart4Theory` implies syntactic consistency. -/
theorem model_implies_consistent (M : Fol.Structure L_ZFC) (hM : Nonempty M.carrier)
    (hsat : Fol.all_realize_sentence M gchPart4Theory) :
    gchPart4Theory.is_consistent := by
  intro hbot
  obtain ⟨d⟩ := hbot
  obtain ⟨m₀⟩ := hM
  exact Fol.formula_soundness d M (fun _ => m₀) fun f hf => by
    rcases hf with ⟨s, hs, rfl⟩
    exact (Fol.realize_sentence_iff (fun _ => m₀) s).mp (hsat hs)

private theorem refutes_not_of_mem {s : Fol.sentence L_ZFC} (hs : s ∈ gchPart4Theory) :
    ¬ (insert (Fol.bd_not s) gchPart4Theory).is_consistent := fun hcons =>
  hcons ⟨Fol.prf.impE s.fst
    (Fol.prf.axm ⟨Fol.bd_not s, Set.mem_insert _ _, rfl⟩)
    (Fol.prf.axm ⟨s, Set.mem_insert_of_mem _ hs, rfl⟩)⟩

/-- `gchPart4Theory` explicitly refutes `¬ part4Sentence`. -/
theorem refutes_not_part4Sentence :
    ¬ (insert (Fol.bd_not part4Sentence) gchPart4Theory).is_consistent :=
  refutes_not_of_mem (Or.inr (Or.inr rfl))

/-- `gchPart4Theory` explicitly refutes `¬ fullGCHSentence`. -/
theorem refutes_not_fullGCHSentence :
    ¬ (insert (Fol.bd_not fullGCHSentence) gchPart4Theory).is_consistent :=
  refutes_not_of_mem (Or.inr (Or.inl rfl))

/-- `gchPart4Theory` explicitly refutes `∃ x, x ∈ ∅'` via `axiom_of_emptyset ∈ ZFC`. -/
theorem refutes_mem_emptyset :
    ¬ (insert (Fol.bd_ex (mem' (Fol.bd_var ⟨0, Nat.zero_lt_succ 0⟩) ∅')) gchPart4Theory).is_consistent := by
  intro hcons
  apply hcons
  let φ : Fol.bounded_formula L_ZFC 1 := mem' (Fol.bd_var ⟨0, Nat.zero_lt_succ 0⟩) ∅'
  have hex_mem : (Fol.bd_ex φ).fst ∈ (insert (Fol.bd_ex φ) gchPart4Theory).fst :=
    ⟨Fol.bd_ex φ, Set.mem_insert _ _, rfl⟩
  have hemp_mem : axiom_of_emptyset.fst ∈ (insert (Fol.bd_ex φ) gchPart4Theory).fst :=
    ⟨axiom_of_emptyset, Set.mem_insert_of_mem _ (Or.inl (Or.inl (Set.mem_insert _ _))), rfl⟩
  exact ⟨Fol.prf.impE (Fol.preformula.all (Fol.not' φ.fst))
    (Fol.prf.axm hex_mem) (Fol.prf.axm hemp_mem)⟩

noncomputable instance propNontrivialCBA : NontrivialCompleteBooleanAlgebra Prop where
  toCompleteBooleanAlgebra := inferInstance
  bot_lt_top := lt_of_le_of_ne (fun h => h.elim) (fun h => by simp at h)

/-- In the classical two-valued universe `V Prop`, `fullGCHSentence` evaluates to `fullGCHValue`. -/
theorem realize_fullGCHSentence_prop :
    Fol.boolean_realize_bounded_formula (S := V Prop) DVec.nil fullGCHSentence DVec.nil =
      (bSet.ErdosFullGCH.fullGCHValue : Prop) :=
  realize_fullGCHSentence (β := Prop)

/-- In the classical two-valued universe `V Prop`, `part4Sentence` evaluates to `part4Value`. -/
theorem realize_part4Sentence_prop :
    Fol.boolean_realize_bounded_formula (S := V Prop) DVec.nil part4Sentence DVec.nil =
      (bSet.ErdosPartition.part4Value : Prop) :=
  realize_part4Sentence (β := Prop)

#check Erdos1172.erdos_1172.parts.ii
#check Erdos1172.erdos_1172.parts.iii
#check Erdos1172.erdos_1172.parts.iv
#check Erdos1172.erdos_1172.part2
#check Erdos1172.erdos_1172.part3
#check Erdos1172.exact_parts23
#check Erdos1172.exact_parts23_and_gchPart4_consistency_of_huge
#check Erdos1172CountableNeighborhoodStep.omegaThree_to_omegaTwo_add_one_countable_of_gch

#print axioms Erdos1172.erdos_1172.parts.ii
#print axioms Erdos1172.erdos_1172.parts.iii
#print axioms Erdos1172.erdos_1172.parts.iv
#print axioms Erdos1172.erdos_1172.part2
#print axioms Erdos1172.erdos_1172.part3
#print axioms Erdos1172.exact_parts23
#print axioms Erdos1172.exact_parts23_and_gchPart4_consistency_of_huge
#print axioms Erdos1172CountableNeighborhoodStep.omegaThree_to_omegaTwo_add_one_countable_of_gch
#print axioms gch_iff_beth_eq_aleph
#print axioms gch_iff_infinite_two_pow_eq_succ
#print axioms ordinalRamsey_iff_pairColoring
#print axioms ordinalCountableRamsey_iff_pairColoring
#print axioms omegaThree_to_omegaTwo_add_one_pairColoring
#print axioms parts_ii_pairColoring
#print axioms parts_iii_pairColoring
#print axioms huge_inaccessible_pair
#print axioms huge_ground_embedding
#print axioms model_implies_consistent
#print axioms refutes_not_part4Sentence
#print axioms refutes_not_fullGCHSentence
#print axioms refutes_mem_emptyset
#print axioms realize_fullGCHSentence_prop
#print axioms realize_part4Sentence_prop

end StatementAudit
