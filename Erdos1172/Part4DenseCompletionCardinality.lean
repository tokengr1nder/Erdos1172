/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetBooleanCompletion
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

/-!
# Cardinal bounds from an actual dense set of forcing conditions

A completed Boolean value is determined by the dense conditions below it,
giving an injection into the powerset of the dense set. A positive pairwise
disjoint family has distinct dense witnesses, so its size is at most the
size of that dense set.

The density is an actual strengthening property. No chain condition or
bound of the completion by the dense-set cardinal itself is assumed. The
proofs also cover empty preorders and empty dense sets.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172PosetCompletion

variable {P : Type u} [Preorder P]

/-- Positive completion values contain actual conditions from any dense set. -/
theorem exists_dense_condition_le (D : Set P)
    (Hdense : ∀ p : P, ∃ d ∈ D, d ≤ p)
    {b : Completion P} (Hb : b ≠ ⊥) :
    ∃ d : D, condition d.val ≤ b := by
  obtain ⟨p, Hp⟩ := exists_condition_le Hb
  obtain ⟨d, Hd, Hdp⟩ := Hdense p
  exact ⟨⟨d, Hd⟩, (condition_mono Hdp).trans Hp⟩

/-- Testing against the actual dense cones detects the complete Boolean order. -/
theorem le_of_dense_conditions_le (D : Set P)
    (Hdense : ∀ p : P, ∃ d ∈ D, d ≤ p)
    {b c : Completion P}
    (H : ∀ d : D, condition d.val ≤ b → condition d.val ≤ c) : b ≤ c := by
  classical
  by_contra Hnot
  have Hresidual : b ⊓ cᶜ ≠ ⊥ := by
    intro Heq
    exact Hnot (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr Heq.le))
  obtain ⟨d, Hd⟩ := exists_dense_condition_le D Hdense Hresidual
  have Hdc : condition d.val ≤ c := H d (Hd.trans inf_le_left)
  exact condition_ne_bot d.val
    (bot_unique ((le_inf (Hd.trans inf_le_right) Hdc).trans compl_inf_eq_bot.le))

/-- The set of dense conditions lying below a completed value. -/
def denseCode (D : Set P) (b : Completion P) : Set D :=
  {d | condition d.val ≤ b}

theorem denseCode_injective (D : Set P)
    (Hdense : ∀ p : P, ∃ d ∈ D, d ≤ p) :
    Function.Injective (denseCode D) := by
  intro b c Hcode
  apply le_antisymm
  · apply le_of_dense_conditions_le D Hdense
    intro d Hd
    have Hmem : d ∈ denseCode D b := Hd
    rw [Hcode] at Hmem
    exact Hmem
  · apply le_of_dense_conditions_le D Hdense
    intro d Hd
    have Hmem : d ∈ denseCode D c := Hd
    rw [← Hcode] at Hmem
    exact Hmem

/-- Dense-set coding gives the powerset bound, not the generally false
claim that the completion is no larger than the dense set itself. -/
theorem completion_cardinal_le_two_pow_dense (D : Set P)
    (Hdense : ∀ p : P, ∃ d ∈ D, d ≤ p) :
    Cardinal.mk (Completion P) ≤ 2 ^ Cardinal.mk D := by
  calc
    Cardinal.mk (Completion P) ≤ Cardinal.mk (Set D) :=
      Cardinal.mk_le_of_injective (denseCode_injective D Hdense)
    _ = 2 ^ Cardinal.mk D := Cardinal.mk_set

/-- A nonzero pairwise-disjoint family has distinct actual dense witnesses.
No chain-condition hypothesis is used to obtain this cardinal bound. -/
theorem disjoint_family_cardinal_le_dense (D : Set P)
    (Hdense : ∀ p : P, ∃ d ∈ D, d ≤ p)
    {ι : Type u} (a : ι → Completion P)
    (Hpositive : ∀ i : ι, a i ≠ ⊥)
    (Hdisjoint : ∀ i j : ι, i ≠ j → a i ⊓ a j = ⊥) :
    Cardinal.mk ι ≤ Cardinal.mk D := by
  classical
  have Hex (i : ι) : ∃ d : D, condition d.val ≤ a i :=
    exists_dense_condition_le D Hdense (Hpositive i)
  choose pick Hpick using Hex
  apply Cardinal.mk_le_of_injective (f := pick)
  intro i j Heq
  by_contra Hne
  have Hj : condition (pick i).val ≤ a j := by
    rw [Heq]
    exact Hpick j
  exact condition_ne_bot (pick i).val
    (bot_unique ((le_inf (Hpick i) Hj).trans (Hdisjoint i j Hne).le))

end Erdos1172PosetCompletion
