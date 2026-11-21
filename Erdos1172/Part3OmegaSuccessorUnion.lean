/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3BoundedPrefixCovers

@[expose] public section

/-!
# Binary unions of short subsets of the omega-successor power

Every short subset of an ambient order of type omegaOne^(omega+1)
is contained in a bounded prefix together with a set of strictly short
finite-power type. Two such remainders have a common finite-power bound.
This proves binary-union closure without a natural-sum API or any
additional cardinal, forcing, or closure hypothesis.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OmegaSuccessorUnion

open Erdos1172Part3BoundedPrefixCovers

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

theorem exists_prefix_and_finite_tail
    (hV : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (A : Set V) (hA : typeLT A < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) :
    ∃ cut : V, ∃ n : ℕ, ∃ T : Set V,
      A ⊆ Set.Iio cut ∪ T ∧
      typeLT T < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  classical
  by_cases hcofinal : IsCofinal A
  · obtain ⟨n, T, -, -, hT, cut, hrest⟩ := exists_cofinal_power_tail hV A hcofinal hA
    refine ⟨cut, n + 1, T, ?_, ?_⟩
    · intro x hx
      by_cases hxT : x ∈ T
      · exact Or.inr hxT
      · exact Or.inl (hrest ⟨hx, hxT⟩)
    · rw [hT]
      exact Erdos1172Part3CoverProfileTools.lower_power_lt (n + 1) n (Nat.lt_succ_self n)
  · obtain ⟨cut, hcut⟩ := not_forall.mp hcofinal
    refine ⟨cut, 0, ∅, ?_, ?_⟩
    · intro x hx
      apply Or.inl
      apply lt_of_not_ge
      exact fun hcx => hcut ⟨x, hx, hcx⟩
    · rw [Ordinal.type_eq_zero_of_empty]
      exact Ordinal.opow_pos _ (Ordinal.omega_pos 1)

theorem union_type_lt
    (hV : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    {A B : Set V}
    (hA : typeLT A < (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (hB : typeLT B < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) :
    typeLT (A ∪ B : Set V) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
  obtain ⟨a, n, S, hAS, hS⟩ := exists_prefix_and_finite_tail hV A hA
  obtain ⟨b, m, T, hBT, hT⟩ := exists_prefix_and_finite_tail hV B hB
  have hS' : typeLT S < (ω_ 1 : Ordinal.{0}) ^ ((max n m + 1 : ℕ) : Ordinal) := by
    apply hS.trans_le
    apply Ordinal.opow_le_opow_right (Ordinal.omega_pos 1)
    exact_mod_cast Nat.succ_le_succ (le_max_left n m)
  have hT' : typeLT T < (ω_ 1 : Ordinal.{0}) ^ ((max n m + 1 : ℕ) : Ordinal) := by
    apply hT.trans_le
    apply Ordinal.opow_le_opow_right (Ordinal.omega_pos 1)
    exact_mod_cast Nat.succ_le_succ (le_max_right n m)
  have hST := Erdos1172Part3CoverProfileTools.union_type_lt (max n m) hS' hT'
  have hpower : (ω_ 1 : Ordinal.{0}) ^ ((max n m + 1 : ℕ) : Ordinal) <
      (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
    apply (Ordinal.opow_lt_opow_iff_right
      (Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1))).mpr
    exact (Ordinal.natCast_lt_omega0 (max n m + 1)).trans_le le_self_add
  have hcut : typeLT (Set.Iio (max a b)) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
    rw [Ordinal.type_Iio_lt]
    exact (Ordinal.typein_lt_type _ (max a b)).trans_eq hV
  have hsub : A ∪ B ⊆ Set.Iio (max a b) ∪ (S ∪ T) := by
    intro x hx
    rcases hx with hx | hx
    · rcases hAS hx with hxa | hxS
      · exact Or.inl (hxa.trans_le (le_max_left a b))
      · exact Or.inr (Or.inl hxS)
    · rcases hBT hx with hxb | hxT
      · exact Or.inl (hxb.trans_le (le_max_right a b))
      · exact Or.inr (Or.inr hxT)
  have hmono : typeLT (A ∪ B : Set V) ≤ typeLT (Set.Iio (max a b) ∪ (S ∪ T) : Set V) :=
    Ordinal.type_mono hsub
  exact (hmono.trans (typeLT_prefix_union_le (max a b) (S ∪ T))).trans_lt
    (Ordinal.isPrincipal_add_opow_of_isPrincipal_add
      (Ordinal.isPrincipal_add_omega 1) _ hcut (hST.trans hpower))

end Erdos1172Part3OmegaSuccessorUnion
