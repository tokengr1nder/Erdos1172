/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalLineCover
public import Erdos1172.Part3ExactOmegaIndex

@[expose] public section

/-!
# Countable completeness of genuine finite-power order-type ideals

Every countable coloring of omegaOne^(n+1) has a full-type monochromatic
subset. Consequently, in any well-order, a countable union of subsets
of order type strictly below that finite power is still strictly below
it. The bound concerns the entire subset and is independent of any
chosen block presentation or named weak trace.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FiniteOrderTypeIdeal

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index)

theorem exists_monochromatic_line (color : W1 → ℕ) :
    ∃ k : ℕ, ∃ e : W1 ↪o W1, ∀ i : W1, color (e i) = k := by
  classical
  have hlarge : ∃ k : ℕ, ¬({i : W1 | color i = k} : Set W1).Countable := by
    by_contra! h
    have hall : (Set.univ : Set W1).Countable := by
      have hu : (⋃ k : ℕ, {i : W1 | color i = k}) = Set.univ := by ext i; simp
      rw [← hu]
      exact Set.countable_iUnion h
    have hcard := Cardinal.le_aleph0_iff_set_countable.mpr hall
    simp only [Cardinal.mk_univ, W1, Cardinal.mk_toType, Ordinal.card_omega] at hcard
    exact (Cardinal.aleph0_lt_aleph.mpr (by norm_num : (0 : Ordinal) < 1)).not_ge hcard
  obtain ⟨k, hk⟩ := hlarge
  have htype : typeLT W1 ≤ typeLT ({i : W1 | color i = k} : Set W1) := by
    rw [show typeLT W1 = ω_ 1 from Ordinal.type_toType _]
    by_contra h
    have hlt := (Cardinal.lt_omega_iff_card_lt).mp (lt_of_not_ge h)
    rw [Ordinal.card_type] at hlt
    exact hk (Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp hlt))
  obtain ⟨e⟩ := Ordinal.type_le_iff.mp htype
  exact ⟨k, e.toOrderEmbedding.trans (OrderEmbedding.subtype _), fun i => (e i).property⟩

theorem exists_monochromatic_finite_power (n : ℕ) (color : Index n → ℕ) :
    ∃ k : ℕ, ∃ e : Index n ↪o Index n, ∀ i : Index n, color (e i) = k := by
  classical
  induction n with
  | zero => exact exists_monochromatic_line color
  | succ n ih =>
    have hrow (a : W1) := ih (fun i => color (toLex (a, i)))
    choose rowColor rowMap hrowMap using hrow
    obtain ⟨k, outer, houter⟩ := exists_monochromatic_line rowColor
    let f : Index (n + 1) → Index (n + 1) := fun z =>
      toLex (outer (ofLex z).1, rowMap (outer (ofLex z).1) (ofLex z).2)
    have hf : StrictMono f := by
      intro x y hxy
      change x < y at hxy
      rw [Prod.Lex.lt_iff] at hxy
      change f x < f y
      rw [Prod.Lex.lt_iff]
      dsimp only [f, ofLex_toLex]
      rcases hxy with hfirst | ⟨heq, hsecond⟩
      · exact Or.inl (outer.strictMono hfirst)
      · refine Or.inr ⟨congrArg outer heq, ?_⟩
        rw [heq]
        exact (rowMap (outer (ofLex y).1)).strictMono hsecond
    refine ⟨k, OrderEmbedding.ofStrictMono f hf, fun i => ?_⟩
    exact (hrowMap (outer (ofLex i).1) (ofLex i).2).trans (houter (ofLex i).1)

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

theorem iUnion_type_lt_finite_power (n : ℕ) (A : ℕ → Set V)
    (hA : ∀ k : ℕ, typeLT (A k) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    typeLT (⋃ k : ℕ, A k) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  classical
  by_contra h
  have htype : typeLT (Index n) ≤ typeLT (⋃ k : ℕ, A k) := by
    rw [typeLT_index]
    exact le_of_not_gt h
  obtain ⟨e⟩ := Ordinal.type_le_iff.mp htype
  have hmem (i : Index n) : ∃ k : ℕ, (e i).val ∈ A k := Set.mem_iUnion.mp (e i).property
  choose color hcolor using hmem
  obtain ⟨k, sub, hsub⟩ := exists_monochromatic_finite_power n color
  let f : Index n → A k := fun i => ⟨(e (sub i)).val, hsub i ▸ hcolor (sub i)⟩
  have hf : StrictMono f := fun _ _ hxy => e.map_rel_iff.mpr (sub.strictMono hxy)
  have hle := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  change typeLT (Index n) ≤ typeLT (A k) at hle
  rw [typeLT_index] at hle
  exact (hA k).not_ge hle

theorem countable_biUnion_type_lt_finite_power (n : ℕ) {I : Type} (S : Set I)
    (hS : S.Countable) (A : I → Set V)
    (hA : ∀ i ∈ S, typeLT (A i) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    typeLT (⋃ i ∈ S, A i) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
    have heq : (⋃ i ∈ Set.range f, A i) = ⋃ k : ℕ, A (f k) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨i, ⟨k, rfl⟩, hx⟩
        exact ⟨k, hx⟩
      · rintro ⟨k, hx⟩
        exact ⟨f k, ⟨k, rfl⟩, hx⟩
    rw [heq]
    exact iUnion_type_lt_finite_power n (fun k => A (f k))
      (fun k => hA (f k) (Set.mem_range_self k))
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    rw [Set.biUnion_empty, Ordinal.type_eq_zero_of_empty]
    exact Ordinal.opow_pos _ (Ordinal.omega_pos 1)

end Erdos1172Part3FiniteOrderTypeIdeal
