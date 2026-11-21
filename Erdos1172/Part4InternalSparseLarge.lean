/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSparseReservoir
public import Erdos1172.Part4InternalIndependentCoverage
public import Erdos1172.Part4InternalSmallCodomainPigeonhole

@[expose] public section

/-!
The large independent-set branch is obtained from actual internal maximality
and the small-codomain pigeonhole theorem. No externally enumerated vertices
or unproved internal transfinite-recursion principle is assumed.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSparseLarge

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosGraphNeighborhood
open ErdosSparseReservoir ErdosIndependentMaximal ErdosFiberInjection

/-- A small set cannot supply neighbors covering its large complement when
all relevant neighborhoods are small. The neighbor selector is constructed. -/
theorem sparse_small_cover_absurd {color : Bool} {R X A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HX : Γ ≤ injects_into omegaTwo X)
    (HAX : Γ ≤ A ⊆ᴮ X) (HA : Γ ≤ injects_into A omegaOne)
    (Hsparse : Γ ≤ sparseNeighborhoods color R X)
    (Hcover : Γ ≤ ⨅ y, _root_.imp (y ∈ᴮ difference X A)
      (⨆ a, a ∈ᴮ A ⊓ graphColor color R a y)) : Γ ≤ ⊥ := by
  let D := difference X A
  obtain ⟨f, Hf⟩ := ErdosSmallFiberBound.exists_selector_of_pointwise
    (P := fun y a => graphColor color R a y)
    (fun a => graphColor_ext_right color R a)
    (fun y => graphColor_ext_left color R y) Hcover
  have HD : Γ ≤ injects_into omegaTwo D :=
    ErdosLargeDifference.omegaTwo_injects_difference HCH HX HA
  have Hfound := ErdosSmallCodomainPigeonhole.omegaTwo_pigeonhole_of_small_codomain
    HCH (Hf.trans inf_le_left) HA HD
  apply (le_inf (le_refl Γ) Hfound).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro a
  let Δ := Γ ⊓ (a ∈ᴮ A ⊓ injects_into omegaTwo (fiber D f a))
  have Ha : Δ ≤ a ∈ᴮ A := inf_le_right.trans inf_le_left
  have HNsmall : Δ ≤ injects_into (neighborhood color R X a) omegaOne :=
    sparseNeighborhoods_apply (inf_le_left.trans Hsparse)
      (mem_of_mem_subset (inf_le_left.trans HAX) Ha)
  have Hsub : Δ ≤ fiber D f a ⊆ᴮ neighborhood color R X a := by
    rw [subset_unfold']
    apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_fiber_iff.mp (show Δ ⊓ y ∈ᴮ fiber D f a ≤ y ∈ᴮ fiber D f a from inf_le_right)
    have Hcolor : Δ ⊓ y ∈ᴮ fiber D f a ≤ graphColor color R a y :=
      (le_inf
        (inf_le_left.trans (inf_le_left.trans
          ((Hf.trans inf_le_right).trans ((iInf_le _ y).trans (iInf_le _ a)))))
        (le_inf Hy.1 Hy.2)).trans bv_imp_elim
    exact mem_neighborhood_iff.mpr ⟨mem_of_mem_subset difference_subset Hy.1, Hcolor⟩
  have Hbad : Δ ≤ injects_into omegaTwo omegaOne :=
    injects_into_trans (inf_le_right.trans inf_le_right)
      (injects_into_trans (injects_into_of_subset Hsub) HNsmall)
  exact bv_absurd _ Hbad omegaTwo_not_injects

/-- Internal cardinal comparison forces every maximal independent subset
of a large sparse reservoir to have full omega-two cardinality. -/
theorem maximal_independent_large {color : Bool} {R X A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HX : Γ ≤ injects_into omegaTwo X)
    (Hsparse : Γ ≤ sparseNeighborhoods color R X)
    (HAX : Γ ≤ A ⊆ᴮ X) (HA : Γ ≤ independent color R A)
    (Hmax : Γ ≤ ⨅ B, _root_.imp (B ⊆ᴮ X ⊓ independent color R B) (_root_.imp (A ⊆ᴮ B) (A =ᴮ B))) :
    Γ ≤ injects_into omegaTwo A := by
  have Hcover := ErdosIndependentCoverage.maximal_independent_covers HAX HA Hmax
  apply (le_inf (le_refl Γ)
    (ErdosPartialInjection.omegaTwo_cardinal_dichotomy (S := A) (Γ := Γ))).trans
  rw [inf_sup_left]
  apply sup_le
  · exact (sparse_small_cover_absurd (inf_le_left.trans HCH)
      (inf_le_left.trans HX) (inf_le_left.trans HAX) inf_le_right
      (inf_le_left.trans Hsparse) (inf_le_left.trans Hcover)).trans bot_le
  · exact inf_le_right

/-- A genuinely constructed large independent internal subset. This is
cardinal-sized homogeneity, not yet an increasing omega-two enumeration. -/
theorem large_independent_value {color : Bool} {R X : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HX : Γ ≤ injects_into omegaTwo X)
    (Hsparse : Γ ≤ sparseNeighborhoods color R X) :
    Γ ≤ ⨆ A, (A ⊆ᴮ X ⊓ independent color R A) ⊓ injects_into omegaTwo A := by
  apply (le_inf (le_refl Γ)
    (exists_maximal_independent (color := color) (R := R) (X := X) (Γ := Γ))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro A
  let Δ := Γ ⊓ ((A ⊆ᴮ X ⊓ independent color R A) ⊓
    ⨅ B, _root_.imp (B ⊆ᴮ X ⊓ independent color R B) (_root_.imp (A ⊆ᴮ B) (A =ᴮ B)))
  have HAX : Δ ≤ A ⊆ᴮ X := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have HA : Δ ≤ independent color R A := inf_le_right.trans (inf_le_left.trans inf_le_right)
  exact le_iSup_of_le A (le_inf (le_inf HAX HA)
    (maximal_independent_large (inf_le_left.trans HCH) (inf_le_left.trans HX)
      (inf_le_left.trans Hsparse) HAX HA (inf_le_right.trans inf_le_right)))

end bSet.ErdosSparseLarge
