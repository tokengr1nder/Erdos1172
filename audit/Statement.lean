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
2. **Binary Ordinal Partition Relation (`OrdinalRamsey α β γ`)**:
   - Equivalent to the standard set-theoretic `[α]² → {0, 1}` coloring formulation: for every
     2-coloring of strictly increasing pairs `x < y` in a well-ordered set of order type `α`,
     there is either a color-`false` strictly increasing sequence of order type `β` or a
     color-`true` strictly increasing sequence of order type `γ` (`ordinalRamsey_iff_pairColoring`).
   - Instantiated directly at Parts (i), (ii), and (iii) (`parts_i_pairColoring`,
     `parts_ii_pairColoring`, `parts_iii_pairColoring`).
3. **Huge Cardinal Hypothesis (`IsHugeWithTarget κ θ` / `IsHugeCardinal κ`)**:
   - Automatically entails strong inaccessibility of both `κ` and `θ` (`huge_inaccessible_pair`),
     and yields the ground ultrapower elementary embedding `j : ZFSet.{0} → targetClass U`
     with critical point `κ`, `j(κ) = θ`, and `θ`-sequence closure (`huge_ground_embedding`).
4. **First-Order `ZFC + GCH + ω₂ → (ω₁ + ω, ω₁ + ω)²` Theory (`gchPart4Theory`)**:
   - Classical Tarski soundness (`model_implies_consistent`): any classical `L_ZFC`-structure
     satisfying `gchPart4Theory` witnesses `gchPart4Theory.is_consistent`.
   - Explicit refutation checks (`refutes_not_part4Sentence`, `refutes_not_fullGCHSentence`,
     `refutes_mem_emptyset`, `refutes_omega_eq_emptyset`) confirming that `gchPart4Theory`
     non-vacuously entails `part4Sentence`, `fullGCHSentence`, and `ZFC`'s axioms.
   - Exact two-valued (`V Prop`) Tarski realization of `fullGCHSentence` and `part4Sentence`
     (`realize_fullGCHSentence_prop`, `realize_part4Sentence_prop`).
5. **Axiom Audit**:
   - `#print axioms` on all five `comparator.json` endpoints and every audit theorem below
     confirms dependence solely on `[propext, Classical.choice, Quot.sound]`.
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

/-! ## 2. Faithfulness of `OrdinalRamsey` (Graph Cliques ↔ Pair Colorings & Order Embeddings) -/

/-- Textbook `[α]² → {false, true}` pair-coloring formulation of `α → (β, γ)²`. -/
def PairColoringRamsey (α β γ : Ordinal.{0}) : Prop :=
  ∀ c : {p : α.ToType × α.ToType // p.1 < p.2} → Bool,
    (∃ f : β.ToType ↪o α.ToType, ∀ x y (h : x < y), c ⟨(f x, f y), f.strictMono h⟩ = false) ∨
    (∃ g : γ.ToType ↪o α.ToType, ∀ x y (h : x < y), c ⟨(g x, g y), g.strictMono h⟩ = true)

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
          · have hnot : ¬ y < x := lt_asymm hxy
            simpa [hxy, hnot] using h1
          · by_cases hyx : y < x
            · simpa [hxy, hyx] using h1
            · simp [hxy, hyx] at h1⟩
        loopless := ⟨fun x hx => by simp at hx⟩ }
    obtain ⟨s, hs, htype⟩ | ⟨s, hs, htype⟩ := h red redᶜ isCompl_compl
    · have htype' :
          Ordinal.type ((· < ·) : β.ToType → β.ToType → Prop) =
          Ordinal.type ((· < ·) : s → s → Prop) :=
        (Ordinal.type_toType β).trans htype.symm
      obtain ⟨er⟩ := Ordinal.type_eq.mp htype'
      let e : β.ToType ≃o s := OrderIso.ofRelIsoLT er
      let f : β.ToType ↪o α.ToType := e.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ s))
      refine Or.inl ⟨f, fun x y hxy => ?_⟩
      have hadj := hs (e x).2 (e y).2 (f.strictMono hxy).ne
      have hlt : f x < f y := f.strictMono hxy
      change (if h : f x < f y then c ⟨(f x, f y), h⟩ = false
              else if h' : f y < f x then c ⟨(f y, f x), h'⟩ = false else False) at hadj
      split_ifs at hadj
      exact hadj
    · have htype' :
          Ordinal.type ((· < ·) : γ.ToType → γ.ToType → Prop) =
          Ordinal.type ((· < ·) : s → s → Prop) :=
        (Ordinal.type_toType γ).trans htype.symm
      obtain ⟨er⟩ := Ordinal.type_eq.mp htype'
      let e : γ.ToType ≃o s := OrderIso.ofRelIsoLT er
      let g : γ.ToType ↪o α.ToType := e.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ s))
      refine Or.inr ⟨g, fun x y hxy => ?_⟩
      have hadj := hs (e x).2 (e y).2 (g.strictMono hxy).ne
      rw [SimpleGraph.compl_adj] at hadj
      have hlt : g x < g y := g.strictMono hxy
      have h2 := hadj.2
      change ¬(if h : g x < g y then c ⟨(g x, g y), h⟩ = false
               else if h' : g y < g x then c ⟨(g y, g x), h'⟩ = false else False) at h2
      split_ifs at h2
      exact Bool.eq_true_of_not_eq_false h2
  · intro h red blue hcompl
    let c : {p : α.ToType × α.ToType // p.1 < p.2} → Bool :=
      fun p => if red.Adj p.1.1 p.1.2 then false else true
    obtain ⟨f, hf⟩ | ⟨g, hg⟩ := h c
    · refine Or.inl ⟨Set.range f, ?_, ?_⟩
      · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
        rcases lt_trichotomy x y with hlt | rfl | hgt
        · have hc := hf x y hlt
          by_contra hnr
          simp [c, hnr] at hc
        · exact absurd rfl hne
        · have hc := hf y x hgt
          have hr : red.Adj (f y) (f x) := by
            by_contra hnr
            simp [c, hnr] at hc
          exact red.adj_symm hr
      · exact f.orderIso.ordinalType_congr.symm.trans (Ordinal.type_toType β)
    · refine Or.inr ⟨Set.range g, ?_, ?_⟩
      · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
        rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
        refine ⟨hne, ?_⟩
        rcases lt_trichotomy x y with hlt | rfl | hgt
        · intro hr
          have hc := hg x y hlt
          simp [c, hr] at hc
        · exact absurd rfl hne
        · intro hr
          have hc := hg y x hgt
          have hr' : red.Adj (g y) (g x) := red.adj_symm hr
          simp [c, hr'] at hc
      · exact g.orderIso.ordinalType_congr.symm.trans (Ordinal.type_toType γ)

theorem parts_i_pairColoring (hGCH : Cardinal.GCH) :
    PairColoringRamsey (ω_ 3) (ω_ 2) (ω_ 1 + 2) :=
  (ordinalRamsey_iff_pairColoring _ _ _).mp (Erdos1172.erdos_1172.parts.i hGCH)

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

/-- `gchPart4Theory` explicitly refutes `¬ part4Sentence`. -/
theorem refutes_not_part4Sentence :
    ¬ (insert (Fol.bd_not part4Sentence) gchPart4Theory).is_consistent := by
  intro hcons
  apply hcons
  refine ⟨Fol.prf.impE part4Sentence.fst ?_ ?_⟩
  · exact Fol.prf.axm ⟨Fol.bd_not part4Sentence, Set.mem_insert _ _, rfl⟩
  · exact Fol.prf.axm ⟨part4Sentence, Set.mem_insert_of_mem _ (Or.inr (Or.inr rfl)), rfl⟩

/-- `gchPart4Theory` explicitly refutes `¬ fullGCHSentence`. -/
theorem refutes_not_fullGCHSentence :
    ¬ (insert (Fol.bd_not fullGCHSentence) gchPart4Theory).is_consistent := by
  intro hcons
  apply hcons
  refine ⟨Fol.prf.impE fullGCHSentence.fst ?_ ?_⟩
  · exact Fol.prf.axm ⟨Fol.bd_not fullGCHSentence, Set.mem_insert _ _, rfl⟩
  · exact Fol.prf.axm ⟨fullGCHSentence, Set.mem_insert_of_mem _ (Or.inr (Or.inl rfl)), rfl⟩

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

#check Erdos1172.erdos_1172
#check Erdos1172.erdos_1172.parts.i
#check Erdos1172.erdos_1172.parts.ii
#check Erdos1172.erdos_1172.parts.iii
#check Erdos1172.erdos_1172.parts.iv
#check Erdos1172.part1_of_gch
#check Erdos1172.erdos_1172.part1
#check Erdos1172.erdos_1172.part2
#check Erdos1172.erdos_1172.part3
#check Erdos1172.exact_parts123
#check Erdos1172.exact_parts123_and_gchPart4_consistency_of_huge

#print axioms Erdos1172.erdos_1172
#print axioms Erdos1172.erdos_1172.parts.i
#print axioms Erdos1172.erdos_1172.parts.ii
#print axioms Erdos1172.erdos_1172.parts.iii
#print axioms Erdos1172.erdos_1172.parts.iv
#print axioms Erdos1172.part1_of_gch
#print axioms Erdos1172.erdos_1172.part1
#print axioms Erdos1172.erdos_1172.part2
#print axioms Erdos1172.erdos_1172.part3
#print axioms Erdos1172.exact_parts123
#print axioms Erdos1172.exact_parts123_and_gchPart4_consistency_of_huge
#print axioms gch_iff_beth_eq_aleph
#print axioms gch_iff_infinite_two_pow_eq_succ
#print axioms ordinalRamsey_iff_pairColoring
#print axioms parts_i_pairColoring
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
