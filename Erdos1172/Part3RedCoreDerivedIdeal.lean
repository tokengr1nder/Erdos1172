/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RedCoreIdeal

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RedCoreDerivedIdeal

open Erdos1172Part3NeighborhoodCode Erdos1172Part3NeighborhoodIdeal
  Erdos1172Part3NeighborhoodIdealCore Erdos1172Part3FiniteIdealEndpoint
  Erdos1172Part3RedCoreIdeal

def blueSection (H : SimpleGraph W2) (a b : W2) (s : Set W2) : Set W2 :=
  (s ∩ {x | H.Adj x a}) ∩ Set.Iio b

def BlueSmall (r : Code ↪ W2) (G H : SimpleGraph W2) (δ : Ordinal)
    (a : W2) (s : Set W2) : Prop := Small r G H a
  {b | b < a ∧ GoodCut r G H b ∧ ¬RedSmall r G H δ b (blueSection H a b s)}

variable {r : Code ↪ W2} {G H : SimpleGraph W2} {δ : Ordinal} {a : W2}

theorem blueSmall_mono {s t : Set W2} (hst : s ⊆ t)
    (ht : BlueSmall r G H δ a t) : BlueSmall r G H δ a s := by
  apply small_mono (t := {b | b < a ∧ GoodCut r G H b ∧
    ¬RedSmall r G H δ b (blueSection H a b t)}) _ ht
  intro b hb
  exact ⟨hb.1, hb.2.1, fun h => hb.2.2 (redSmall_mono
    (show blueSection H a b s ⊆ blueSection H a b t from
      fun _ hx => ⟨⟨hst hx.1.1, hx.1.2⟩, hx.2⟩) h)⟩

theorem blueSmall_union (ha : GoodCut r G H a) (e : Ordinal) {s t : Set W2}
    (hs : BlueSmall r G H (ω ^ e) a s) (ht : BlueSmall r G H (ω ^ e) a t) :
    BlueSmall r G H (ω ^ e) a (s ∪ t) := by
  let left := {b | b < a ∧ GoodCut r G H b ∧
    ¬RedSmall r G H (ω ^ e) b (blueSection H a b s)}
  let right := {b | b < a ∧ GoodCut r G H b ∧
    ¬RedSmall r G H (ω ^ e) b (blueSection H a b t)}
  apply small_mono (t := left ∪ right) _ (union_small ha hs ht)
  intro b hb
  by_contra hnot
  have hleft : RedSmall r G H (ω ^ e) b (blueSection H a b s) := by
    by_contra h
    exact hnot (Or.inl ⟨hb.1, hb.2.1, h⟩)
  have hright : RedSmall r G H (ω ^ e) b (blueSection H a b t) := by
    by_contra h
    exact hnot (Or.inr ⟨hb.1, hb.2.1, h⟩)
  apply hb.2.2
  have heq : blueSection H a b (s ∪ t) =
      blueSection H a b s ∪ blueSection H a b t := by
    simp only [blueSection, Set.union_inter_distrib_right]
  rw [heq]
  exact redSmall_union hb.2.1 e hleft hright

theorem base_le_blue (ha : GoodCut r G H a) (hδ : 0 < δ)
    {s : Set W2} (hs : Small r G H a s) : BlueSmall r G H δ a s := by
  obtain ⟨c, hc, hac, hsub⟩ := hs
  have hnamed : Small r G H a (eval G H c) := ⟨c, hc, hac, Set.Subset.rfl⟩
  apply small_mono (t := eval G H c ∪ Set.Iic (r c)) _
    (union_small ha hnamed (bounded_interval_small ha hc))
  intro b hb
  by_cases hmem : b ∈ eval G H c
  · exact Or.inl hmem
  by_cases hle : b ≤ r c
  · exact Or.inr hle
  exact (hb.2.2 (base_le_red hδ
    ⟨c, lt_of_not_ge hle, hmem, fun _ hx => hsub hx.1.1⟩)).elim

def blueSmallness (ha : GoodCut r G H a) (e : Ordinal) : FiniteSmallness W2 where
  small := BlueSmall r G H (ω ^ e) a
  empty_small := base_le_blue ha (Ordinal.opow_pos e Ordinal.omega0_pos) (empty_small ha)
  mono := blueSmall_mono
  union_small := blueSmall_union ha e

theorem blueSmall_inter (s : Set W2) :
    BlueSmall r G H δ a (s ∩ {x | H.Adj x a}) ↔ BlueSmall r G H δ a s := by
  simp only [BlueSmall, blueSection, Set.inter_assoc, Set.inter_self]

theorem blue_core_of_blue_positive (ha : GoodCut r G H a) (hδ : 0 < δ)
    {s : Set W2} (hsub : s ⊆ Set.Iio a) (hs : ¬BlueSmall r G H δ a s) :
    HasCore H (ω_ 1) s := by
  let fiber := s ∩ {x | H.Adj x a}
  have hf : ¬BlueSmall r G H δ a fiber := by rwa [blueSmall_inter]
  have hbase : ¬Small r G H a fiber := fun h => hf (base_le_blue ha hδ h)
  obtain ⟨c, hc, hcl, hct⟩ := exists_core ha false fiber hbase
    (fun _ hx => hsub hx.1) (fun _ hx => hx.2)
  exact ⟨c, hc.trans Set.inter_subset_left, hcl, hct⟩

theorem red_core_of_blue_positive (ha : GoodCut r G H a)
    {s : Set W2} (hs : ¬BlueSmall r G H δ a s) : HasCore G δ s := by
  let support := {b | b < a ∧ GoodCut r G H b ∧
    ¬RedSmall r G H δ b (blueSection H a b s)}
  have hn : support.Nonempty := by
    by_contra h
    apply hs
    change Small r G H a support
    rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact empty_small ha
  obtain ⟨b, hb⟩ := hn
  exact (core_of_red_positive hb.2.1 hb.2.2).mono (fun _ hx => hx.1.1)

abbrev Targets (G H : SimpleGraph W2) (δ : Ordinal) : Prop :=
  OrdinalRamsey.HasCliqueOfType G (δ + 2) ∨
    OrdinalRamsey.HasCliqueOfType H (ω_ 1 + 2)

theorem blue_target_le_omegaTwo : (ω_ 1 : Ordinal) + 2 ≤ ω_ 2 := by
  apply le_of_lt
  apply Ordinal.isPrincipal_add_omega
  · exact Ordinal.omega_lt_omega.mpr one_lt_two
  · exact (Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2)

/-- A counterexample to the exact targets cannot have a proper derived
blue ideal over the red-core ideal at even one good cut. -/
theorem blueSmall_prior_of_no_targets (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (e : Ordinal) (hδ : ω ^ e + 2 ≤ ω_ 2) (hno : ¬Targets G H (ω ^ e))
    {a : W2} (ha : GoodCut r G H a) : BlueSmall r G H (ω ^ e) a (Set.Iio a) := by
  by_contra hpos
  apply hno
  apply targets_of_mixed_positive_ideal G H hcompl (ω ^ e) (ω_ 1) hδ
    blue_target_le_omegaTwo (blueSmallness ha e) (Set.Iio a) a hpos Set.Subset.rfl
  · intro s _ hs
    exact red_core_of_blue_positive ha hs
  · intro s hsub hs
    exact blue_core_of_blue_positive ha (Ordinal.opow_pos e Ordinal.omega0_pos) hsub hs

end Erdos1172Part3RedCoreDerivedIdeal
