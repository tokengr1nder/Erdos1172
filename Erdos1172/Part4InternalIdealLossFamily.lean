/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIdealCentering
public import Erdos1172.Part4InternalCHHartogs

@[expose] public section

/-!
# The actual internally countable family of base losses

For arbitrary names `A` and `T`, the name `lossFamily A T` is the image of
`T` under internal difference from `A`. A concrete functional graph
surjects onto this image. Internal countability of `T` therefore implies
internal countability of the loss family, using least preimages in omega.
Consequently the common positive subset theorem needs only the original
countable family and smallness of each individual loss, not a separately
supplied countable family covering those losses.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIdeal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem difference_congr_right {A B C : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ B =ᴮ C) : Γ ≤ difference A B =ᴮ difference A C := by
  have Hext (x : bSet 𝔹) : B_ext (fun Y : bSet 𝔹 => (x ∈ᴮ Y)ᶜ) :=
    B_ext_neg (h := B_ext_mem_right)
  apply mem_ext
  · apply le_iInf
    intro x
    rw [← deduction, mem_difference, mem_difference]
    exact le_inf (inf_le_right.trans inf_le_left)
      (bv_rw'' (inf_le_left.trans H) (inf_le_right.trans inf_le_right) (Hext x))
  · apply le_iInf
    intro x
    rw [← deduction, mem_difference, mem_difference]
    exact le_inf (inf_le_right.trans inf_le_left)
      (bv_rw'' (inf_le_left.trans (bv_symm H))
        (inf_le_right.trans inf_le_right) (Hext x))

theorem B_congr_difference_right (A : bSet 𝔹) : B_congr (difference A) := by
  intro B C Γ H
  exact difference_congr_right H

/-- The concrete image name, retaining the Boolean coefficients of `T`. -/
def lossFamily (A T : bSet 𝔹) : bSet 𝔹 :=
  ⟨T.type, fun i => difference A (T.func i), T.bval⟩

/-- Membership is the internal image predicate, over arbitrary names. -/
theorem mem_lossFamily (A T X : bSet 𝔹) :
    X ∈ᴮ lossFamily A T =
      ⨆ B : bSet 𝔹, (B ∈ᴮ T) ⊓ (X =ᴮ difference A B) := by
  rw [mem_unfold]
  change (⨆ i : T.type, T.bval i ⊓ X =ᴮ difference A (T.func i)) = _
  exact bounded_exists (h_congr :=
    B_ext_term (fun Y => X =ᴮ Y) (difference A)
      B_ext_bv_eq_right (B_congr_difference_right A))

theorem difference_mem_lossFamily {A T B : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ∈ᴮ T) : Γ ≤ difference A B ∈ᴮ lossFamily A T := by
  rw [mem_lossFamily]
  exact le_iSup_of_le B (le_inf HB bv_refl)

theorem lossFamily_subset_ideal {A T I : bSet 𝔹} {Γ : 𝔹}
    (Hsmall : Γ ≤ ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ T) (difference A B ∈ᴮ I)) :
    Γ ≤ lossFamily A T ⊆ᴮ I := by
  rw [subset_unfold']
  apply le_iInf
  intro X
  rw [← deduction, mem_lossFamily, inf_iSup_eq]
  apply iSup_le
  intro B
  have Hdiff : Γ ⊓ (B ∈ᴮ T ⊓ X =ᴮ difference A B) ≤ difference A B ∈ᴮ I :=
    (le_inf (inf_le_left.trans (Hsmall.trans (iInf_le _ B)))
      (inf_le_right.trans inf_le_left)).trans bv_imp_elim
  exact bv_rw' (x := X) (y := difference A B) (ϕ := fun z => z ∈ᴮ I)
    (inf_le_right.trans inf_le_right)
    (h_congr := B_ext_mem_left) (H_new := Hdiff)

/-- The actual graph of the difference map on the arbitrary name `T`. -/
def lossGraph (A T : bSet 𝔹) : bSet 𝔹 :=
  functionMk (u := T) (fun i => difference A (T.func i))
    (fun _ _ => difference_congr_right le_rfl)

theorem lossGraph_apply {A T B : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ∈ᴮ T) : Γ ≤ pair B (difference A B) ∈ᴮ lossGraph A T := by
  rw [mem_unfold] at HB
  apply HB.trans
  apply iSup_le
  intro i
  have Hpair : T.bval i ⊓ B =ᴮ T.func i ≤
      pair B (difference A B) =ᴮ pair (T.func i) (difference A (T.func i)) :=
    pair_eq_pair_iff.mpr ⟨inf_le_right, difference_congr_right inf_le_right⟩
  rw [mem_unfold]
  change T.bval i ⊓ B =ᴮ T.func i ≤
    ⨆ j : T.type, T.bval j ⊓
      pair B (difference A B) =ᴮ pair (T.func j) (difference A (T.func j))
  exact le_iSup_of_le i (le_inf inf_le_left Hpair)

theorem lossGraph_is_func {A T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_func (lossGraph A T) :=
  le_top.trans (functionMk_is_func (u := T) (fun i => difference A (T.func i))
    (fun _ _ => difference_congr_right le_rfl))

theorem lossGraph_is_total {A T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_total T (lossFamily A T) (lossGraph A T) := by
  apply le_iInf
  intro B
  rw [← deduction]
  apply le_iSup_of_le (difference A B)
  exact le_inf (difference_mem_lossFamily inf_le_right) (lossGraph_apply inf_le_right)

theorem lossGraph_is_func' {A T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_func' T (lossFamily A T) (lossGraph A T) :=
  le_inf lossGraph_is_func lossGraph_is_total

theorem lossGraph_is_surj {A T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_surj T (lossFamily A T) (lossGraph A T) := by
  apply le_iInf
  intro X
  rw [← deduction, mem_lossFamily, inf_iSup_eq]
  apply iSup_le
  intro B
  apply le_iSup_of_le B
  refine le_inf (inf_le_right.trans inf_le_left) ?_
  have Hpair : Γ ⊓ (B ∈ᴮ T ⊓ X =ᴮ difference A B) ≤
      pair B (difference A B) =ᴮ pair B X :=
    pair_eq_pair_iff.mpr ⟨bv_refl, bv_symm (inf_le_right.trans inf_le_right)⟩
  exact mem_congr Hpair bv_refl (lossGraph_apply (inf_le_right.trans inf_le_left))

theorem larger_than_lossFamily {A T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ larger_than T (lossFamily A T) := by
  apply le_iSup_of_le T
  apply le_iSup_of_le (lossGraph A T)
  exact le_inf (le_inf subset_self lossGraph_is_func') lossGraph_is_surj

/-- Images of internally countable families are internally countable.
The source representation `T.type` need not be countable externally. -/
theorem lossFamily_countable {A T : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ injects_into T bSet.omega) :
    Γ ≤ injects_into (lossFamily A T) bSet.omega := by
  have Hlarge : Γ ≤ larger_than bSet.omega (lossFamily A T) := by
    have Hbad : (larger_than bSet.omega (lossFamily A T))ᶜ ⊓ Γ ≤ ⊥ := by
      have Hnot : (larger_than bSet.omega (lossFamily A T))ᶜ ⊓ Γ ≤
          (larger_than T (lossFamily A T))ᶜ :=
        bSet_lt_of_le_of_lt (inf_le_right.trans HT) inf_le_left
      exact bv_absurd _ larger_than_lossFamily Hnot
    have Hresult : Γ ≤ ((larger_than bSet.omega (lossFamily A T))ᶜ)ᶜ :=
      le_neg_of_inf_eq_bot (bot_unique Hbad)
    simpa only [compl_compl] using Hresult
  exact ErdosCHHartogs.injects_into_of_larger_than_ordinal Ord_omega Hlarge

theorem lossFamily_contains_losses {A T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ T) (difference A B ∈ᴮ lossFamily A T) := by
  apply le_iInf
  intro B
  rw [← deduction]
  exact difference_mem_lossFamily inf_le_right

/-- The common positive subset is now constructed from the original
internally countable family, with no separately supplied loss-family data. -/
theorem positive_commonRemainder_of_countable {κ I A T : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I)
    (Hclosure : Γ ≤ countableClosure I)
    (HA : Γ ≤ positive κ I A)
    (HT : Γ ≤ injects_into T bSet.omega)
    (Hsmall : Γ ≤ ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ T) (difference A B ∈ᴮ I)) :
    Γ ≤ positive κ I (commonRemainder A (lossFamily A T)) ⊓
      ((commonRemainder A (lossFamily A T) ⊆ᴮ A) ⊓
        ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ T) (commonRemainder A (lossFamily A T) ⊆ᴮ B)) :=
  commonRemainder_positive_common HI Hclosure HA (lossFamily_countable HT)
    (lossFamily_subset_ideal Hsmall) lossFamily_contains_losses

end bSet.ErdosIdeal
