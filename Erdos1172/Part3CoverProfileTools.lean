/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalCoverSupport

@[expose] public section

/-!
# Countable profiles for cofinal covering

Countably many covering functions have a pointwise bound. Endpoint
supports with row witnesses have countable prefixes. The two-dimensional
profile coordinates are coded into omegaOne without CH.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CoverProfileTools

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)
open Erdos1172Part3FiniteOrderTypeIdeal (countable_biUnion_type_lt_finite_power)

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

theorem countable_type_lt_omegaOne (A : Set V) (hA : A.Countable) : typeLT A < ω_ 1 := by
  rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_type]
  exact Cardinal.lt_aleph_one_iff.mpr (Cardinal.le_aleph0_iff_set_countable.mpr hA)

theorem countable_iUnion_type_lt (n : ℕ) {I : Type} [Countable I] (A : I → Set V)
    (hA : ∀ i, typeLT (A i) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    typeLT (⋃ i, A i) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  have h := countable_biUnion_type_lt_finite_power n (Set.univ : Set I)
    (Set.to_countable _) A (fun i _ => hA i)
  have heq : (⋃ i ∈ (Set.univ : Set I), A i) = ⋃ i, A i := by ext x; simp
  rw [heq] at h
  exact h

theorem union_type_lt (n : ℕ) {A B : Set V}
    (hA : typeLT A < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal))
    (hB : typeLT B < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    typeLT (A ∪ B : Set V) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  have hsmall := countable_biUnion_type_lt_finite_power n ({A, B} : Set (Set V))
    (by simp) id (by
      intro C hC
      rcases Set.mem_insert_iff.mp hC with rfl | hC
      · exact hA
      · exact Set.mem_singleton_iff.mp hC ▸ hB)
  apply (Ordinal.type_mono (show A ∪ B ⊆ ⋃ C ∈ ({A, B} : Set (Set V)), C from ?_)).trans_lt hsmall
  intro x hx
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
  · exact Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩

theorem lower_power_lt (n k : ℕ) (hk : k < n) :
    (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal) <
      (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  apply (Ordinal.opow_lt_opow_iff_right
    (Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1))).mpr
  exact_mod_cast Nat.succ_lt_succ hk

theorem omegaOne_le_power (n : ℕ) :
    (ω_ 1 : Ordinal.{0}) ≤ (ω_ 1) ^ ((n + 1 : ℕ) : Ordinal) := by
  have h := Ordinal.opow_le_opow_right (Ordinal.omega_pos 1)
    (show (1 : Ordinal.{0}) ≤ ((n + 1 : ℕ) : Ordinal) by exact_mod_cast Nat.succ_pos n)
  simpa only [Ordinal.opow_one] using h

theorem line_closed_prefix_countable (data : LineCoverData V) (f : W1 → W1) (x : V) :
    (data.cover f ∩ Set.Iic x).Countable := by
  apply ((data.cover_prefix_countable f x).union (Set.countable_singleton x)).mono
  intro y hy
  rcases lt_or_eq_of_le hy.2 with hlt | rfl
  · exact Or.inl ⟨hy.1, hlt⟩
  · exact Or.inr (by simp)

omit [LinearOrder V] [WellFoundedLT V] in
theorem exists_pointwise_bound {I : Type} (S : Set I) (hS : S.Countable) (F : I → W1 → W1) :
    ∃ g : W1 → W1, ∀ a ∈ S, F a ≤ g := by
  have hbound (i : W1) : ∃ b : W1, ∀ a ∈ S, F a i < b := by
    obtain ⟨b, hb⟩ := exists_bound_of_countable ((fun a => F a i) '' S) (hS.image _)
    exact ⟨b, fun a ha => hb (F a i) ⟨a, ha, rfl⟩⟩
  choose g hg using hbound
  exact ⟨g, fun a ha i => (hg i a ha).le⟩

def endpointSupport (D : W1 → Set (Set V)) (endpoint : (i : W1) → D i → V) : Set V :=
  ⋃ i : W1, Set.range (endpoint i)

omit [WellFoundedLT V] in
theorem endpointSupport_prefix_countable (data : LineCoverData V)
    (D : W1 → Set (Set V)) (hD : ∀ i, (D i).Countable)
    (endpoint : (i : W1) → D i → V)
    (hwitness : ∀ i (B : D i), ∃ x : V, data.row x = i ∧ x ≤ endpoint i B) (x : V) :
    (endpointSupport D endpoint ∩ Set.Iio x).Countable := by
  have hrow (i : W1) : (Set.range (endpoint i)).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp
      (Cardinal.mk_range_le.trans (Cardinal.le_aleph0_iff_set_countable.mpr (hD i)))
  have hiCount : (Set.Iic (data.row x)).Countable := Cardinal.le_aleph0_iff_set_countable.mp
    (Cardinal.lt_aleph_one_iff.mp (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt (data.row x)))
  apply (hiCount.biUnion (fun i _ => hrow i)).mono
  rintro y ⟨hy, hyx⟩
  obtain ⟨i, B, rfl⟩ := Set.mem_iUnion.mp hy
  obtain ⟨z, hzi, hzy⟩ := hwitness i B
  have hi : i ≤ data.row x := hzi ▸ data.row_mono (hzy.trans hyx.le)
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, Set.mem_range_self B⟩⟩

abbrev ProfileIndex := W1 ⊕ (W1 × W1)
abbrev Profile := ProfileIndex → W1

def head (f : Profile) (i : W1) : W1 := f (Sum.inl i)
def row (f : Profile) (i j : W1) : W1 := f (Sum.inr (i, j))

def profile (f : W1 → W1) (F : W1 → W1 → W1) : Profile
  | .inl i => f i
  | .inr ij => F ij.1 ij.2

noncomputable def profileRank : ProfileIndex ↪ W1 := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).mp
  simp only [ProfileIndex, Cardinal.mk_sum, Cardinal.mk_prod, Cardinal.lift_id,
    W1, Cardinal.mk_toType, Ordinal.card_omega,
    Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1),
    Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1), le_refl]

noncomputable def decode (f : W1 → W1) : Profile := f ∘ profileRank

theorem decode_mono : Monotone decode := fun _ _ h i => h (profileRank i)

theorem decode_surjective : Function.Surjective decode :=
  profileRank.injective.surjective_comp_right'
    (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩)

end Erdos1172Part3CoverProfileTools
