/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCardinalDichotomy
public import Erdos1172.Part4InternalCHHartogs

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCantor

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The diagonal excludes the output of every edge with the indicated input. -/
def diagonal (X f : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun x => ⨅ y, _root_.imp (pair x y ∈ᴮ f) (x ∈ᴮ y)ᶜ) X

private theorem diagonal_predicate_ext (f : bSet 𝔹) :
    B_ext (fun x => ⨅ y, _root_.imp (pair x y ∈ᴮ f) (x ∈ᴮ y)ᶜ) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_pair_mem_left)
    (h₂ := B_ext_neg (h := B_ext_mem_left)))

theorem mem_diagonal (X f x : bSet 𝔹) :
    x ∈ᴮ diagonal X f = (x ∈ᴮ X) ⊓ ⨅ y, _root_.imp (pair x y ∈ᴮ f) (x ∈ᴮ y)ᶜ := by
  unfold diagonal
  apply le_antisymm
  · apply ((mem_comprehend_iff₂ _ X (diagonal_predicate_ext f)).mp le_rfl).trans
    apply iSup_le
    intro z
    have Heq : z ∈ᴮ X ⊓ (x =ᴮ z ⊓
        (⨅ y, _root_.imp (pair z y ∈ᴮ f) (z ∈ᴮ y)ᶜ)) ≤ x =ᴮ z :=
      inf_le_right.trans inf_le_left
    exact le_inf
      (bv_rw' (ϕ := fun w => w ∈ᴮ X) Heq
        (h_congr := B_ext_mem_left) (H_new := inf_le_left))
      (bv_rw' Heq (h_congr := diagonal_predicate_ext f) (H_new := inf_le_right.trans inf_le_right))
  · apply (mem_comprehend_iff₂ _ X (diagonal_predicate_ext f)).mpr
    exact le_iSup_of_le x (le_inf inf_le_left (le_inf bv_refl inf_le_right))

theorem diagonal_subset {X f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ diagonal X f ⊆ᴮ X :=
  comprehend_subset (ϕ := fun x => ⨅ y,
    _root_.imp (pair x y ∈ᴮ f) (x ∈ᴮ y)ᶜ) X

/-- No functional relation on a subset of X can cover the full internal powerset.
Totality or product support is not needed for this obstruction. -/
theorem bot_of_partial_surjection_powerset {X S f : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ S ⊆ᴮ X) (Hf : Γ ≤ is_func f)
    (Hsurj : Γ ≤ is_surj S (bv_powerset X) f) : Γ ≤ ⊥ := by
  let D := diagonal X f
  have HD : Γ ≤ D ∈ᴮ bv_powerset X := bv_powerset_spec.mp diagonal_subset
  have Hpre : Γ ≤ ⨆ a, (a ∈ᴮ S) ⊓ pair a D ∈ᴮ f :=
    (le_inf (Hsurj.trans (iInf_le _ D)) HD).trans bv_imp_elim
  obtain ⟨a, Ha⟩ := exists_convert Hpre (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hnot : Γ ≤ (a ∈ᴮ D)ᶜ := by
    rw [← imp_bot, ← deduction]
    have Hdiag : Γ ⊓ a ∈ᴮ D ≤ ⨅ y, _root_.imp (pair a y ∈ᴮ f) (a ∈ᴮ y)ᶜ := by
      have Hmem : Γ ⊓ a ∈ᴮ D ≤ a ∈ᴮ diagonal X f := inf_le_right
      exact Hmem.trans ((mem_diagonal X f a).le.trans inf_le_right)
    exact bv_absurd _ inf_le_right
      ((le_inf (Hdiag.trans (iInf_le _ D))
        (inf_le_left.trans (Ha.trans inf_le_right))).trans bv_imp_elim)
  have Hyes : Γ ≤ a ∈ᴮ D := by
    change Γ ≤ a ∈ᴮ diagonal X f
    rw [mem_diagonal]
    refine le_inf (mem_of_mem_subset HS (Ha.trans inf_le_left)) ?_
    apply le_iInf
    intro y
    rw [← deduction]
    have Heq : Γ ⊓ pair a y ∈ᴮ f ≤ y =ᴮ D :=
      eq_of_is_func_of_eq (inf_le_left.trans Hf) bv_refl inf_le_right
        (inf_le_left.trans (Ha.trans inf_le_right))
    exact bv_rw' (ϕ := fun z => (a ∈ᴮ z)ᶜ) Heq
      (h_congr := B_ext_neg (h := B_ext_mem_right))
      (H_new := inf_le_left.trans Hnot)
  exact bv_absurd _ Hyes Hnot

/-- Cantor's theorem, with the partial-surjection orientation made explicit. -/
theorem not_larger_than_powerset {X : bSet 𝔹} {Γ : 𝔹} : Γ ≤ (larger_than X (bv_powerset X))ᶜ := by
  rw [← imp_bot, ← deduction]
  unfold larger_than
  rw [inf_iSup_eq]
  apply iSup_le
  intro S
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  exact bot_of_partial_surjection_powerset
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (is_func_of_is_func' (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (inf_le_right.trans inf_le_right)

theorem powerset_not_injects {X : bSet 𝔹} {Γ : 𝔹} : Γ ≤ (injects_into (bv_powerset X) X)ᶜ := by
  rw [← imp_bot, ← deduction]
  exact bv_absurd _ (ErdosCHHartogs.larger_than_of_injects_into inf_le_right)
    not_larger_than_powerset

/-- The continuum contains the actual internal Hartogs omega-one, without CH. -/
theorem omegaOne_injects_powerset_omega {Γ : 𝔹} :
    Γ ≤ injects_into ErdosOmegaTwo.omegaOne (bv_powerset (bSet.omega : bSet 𝔹)) := by
  apply (le_inf
    (ErdosPartialInjection.omegaOne_cardinal_dichotomy (S := bv_powerset bSet.omega) (Γ := Γ))
    (powerset_not_injects (X := bSet.omega) (Γ := Γ))).trans
  rw [inf_sup_right]
  apply sup_le
  · exact (bv_absurd _ inf_le_left inf_le_right).trans bot_le
  · exact inf_le_left

end bSet.ErdosCantor
