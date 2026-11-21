/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedImageRecursion

@[expose] public section

/-!
# One-step extension of bounded image recursion

The new coordinate is the actual domain of the current prefix. A
functional extension preserves every earlier prefix image, including the
image at that new coordinate itself. Congruence of the stage and image
arguments therefore preserves all old equations and establishes the new
one. No freshness of the output, injectivity, total run, or maximality is
assumed. The proof does not require the ambient bound to be an ordinal.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBoundedImageRecursion

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPrefixFunction ErdosPartialInjection ErdosInjectionExtension
open ErdosRowCandidates

private theorem mem_insert1_value {x y P : bSet 𝔹} :
    x ∈ᴮ bSet.insert1 y P = x =ᴮ y ⊔ x ∈ᴮ P :=
  mem_insert1

/-- The recurrence equation at the actual next coordinate extends the
whole prefix, retaining every previously established recurrence equation. -/
theorem imageRecPartial_insert_next
    {θ V P y : bSet 𝔹} {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hstage : ∀ T, B_congr (fun i => Φ i T))
    (Hpast : ∀ i, B_congr (Φ i))
    (HP : Γ ≤ imageRecPartial θ V Φ P)
    (HD : Γ ≤ graphDomain θ V P ∈ᴮ θ) (Hy : Γ ≤ y ∈ᴮ V)
    (Hvalue : Γ ≤ y =ᴮ Φ (graphDomain θ V P) (image (graphDomain θ V P) V P)) :
    Γ ≤ imageRecPartial θ V Φ (bSet.insert1 (pair (graphDomain θ V P) y) P) := by
  let D := graphDomain θ V P
  let Q := bSet.insert1 (pair D y) P
  have Hprefix : Γ ≤ prefixGraph θ V Q := prefixGraph_insert_next (HP.trans inf_le_left) HD Hy
  have Hfunc : Γ ≤ is_func Q := Hprefix.trans (inf_le_right.trans inf_le_left)
  have Hweak : Γ ≤ is_func' D V P := is_func'_of_is_function (imageRecPartial_function HP)
  have Himage : Γ ≤ image D V P =ᴮ image D V Q :=
    prefix_image_eq_of_extension subset_insertPair Hfunc Hweak
  have Hnew : Γ ≤ y =ᴮ Φ D (image D V Q) := bv_trans Hvalue (Hpast D Himage)
  refine le_inf Hprefix ?_
  apply le_iInf
  intro i
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ pair i x ∈ᴮ Q
  have Hsplit : Δ ≤ pair i x =ᴮ pair D y ⊔ pair i x ∈ᴮ P :=
    (show Δ ≤ pair i x ∈ᴮ Q from inf_le_right).trans
      (mem_insert1_value (x := pair i x) (y := pair D y) (P := P)).le
  apply (le_inf (le_refl Δ) Hsplit).trans
  rw [inf_sup_left]
  apply sup_le
  · let Λ := Δ ⊓ pair i x =ᴮ pair D y
    have HΛ : Λ ≤ Γ := inf_le_left.trans inf_le_left
    have HiD : Λ ≤ i =ᴮ D := eq_of_eq_pair_left' inf_le_right
    have Hxy : Λ ≤ x =ᴮ y := eq_of_eq_pair_right' inf_le_right
    have Himages : Λ ≤ image i V Q =ᴮ image D V Q := B_congr_image_left HiD
    have Harguments : Λ ≤ Φ i (image i V Q) =ᴮ Φ D (image D V Q) :=
      bv_trans (Hpast i Himages) (Hstage (image D V Q) HiD)
    exact bv_trans (bv_trans Hxy (HΛ.trans Hnew)) (bv_symm Harguments)
  · exact imageRecLaw_entry_of_extension Hpast subset_insertPair
      (inf_le_left.trans (inf_le_left.trans Hfunc))
      (inf_le_left.trans (inf_le_left.trans HP)) inf_le_right

end bSet.ErdosBoundedImageRecursion
