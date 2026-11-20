/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSmallCodomainPigeonhole
public import Erdos1172.Part4InternalOmegaReservoir

@[expose] public section

/-!
Every internally omega-one-small subset of omega-two has a strict ordinal
bound inside omega-two, under internal CH. A genuine internal selector of
members covering the union, followed by the checked small-codomain
pigeonhole theorem, rules out a cofinal union. No regularity or boundedness
assumption and no enumeration by ground-model indices is supplied.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaTwoBounded

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFiberInjection ErdosIdeal

/-- Each value chosen at a point of the union is a member containing it. -/
def selectsUnionMember (A f : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ a, _root_.imp (x ∈ᴮ bv_union A ⊓ pair x a ∈ᴮ f) (x ∈ᴮ a)

/-- Bounded internal choice builds the actual union-membership selector,
including for the empty family. -/
theorem exists_union_selector (A : bSet 𝔹) {Γ : 𝔹} :
    ∃ f : bSet 𝔹, Γ ≤ is_function (bv_union A) A f ⊓ selectsUnionMember A f := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (P := fun x a => x ∈ᴮ a)
    (fun _ => B_ext_mem_left) (fun _ => B_ext_mem_right)
  apply le_iInf
  intro x
  rw [← deduction]
  exact mem_bv_union_iff.mp inf_le_right

/-- A fiber of the selector lies inside the selected member itself. -/
theorem union_selector_fiber_subset {A f a : bSet 𝔹} {Γ : 𝔹}
    (Hselect : Γ ≤ selectsUnionMember A f) :
    Γ ≤ fiber (bv_union A) f a ⊆ᴮ a := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hx := mem_fiber_iff.mp
    (show Γ ⊓ x ∈ᴮ fiber (bv_union A) f a ≤ x ∈ᴮ fiber (bv_union A) f a
      from inf_le_right)
  exact (le_inf
    (inf_le_left.trans (Hselect.trans ((iInf_le _ x).trans (iInf_le _ a))))
    (le_inf Hx.1 Hx.2)).trans bv_imp_elim

/-- A small family of strict predecessors cannot have an omega-two-sized
union: a large selector fiber would inject into a strict predecessor. -/
theorem union_not_omegaTwo_large {A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ A ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into A omegaOne) :
    Γ ≤ (injects_into omegaTwo (bv_union A))ᶜ := by
  rw [← imp_bot, ← deduction]
  let Δ := Γ ⊓ injects_into omegaTwo (bv_union A)
  obtain ⟨f, Hf⟩ := exists_union_selector A (Γ := Δ)
  have Hfound := ErdosSmallCodomainPigeonhole.omegaTwo_pigeonhole_of_small_codomain
    (inf_le_left.trans HCH) (Hf.trans inf_le_left)
    (inf_le_left.trans Hsmall)
    (show Δ ≤ injects_into omegaTwo (bv_union A) from inf_le_right)
  change Δ ≤ ⊥
  apply (le_inf (le_refl Δ) Hfound).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro a
  let Θ := Δ ⊓ (a ∈ᴮ A ⊓ injects_into omegaTwo (fiber (bv_union A) f a))
  have Ha : Θ ≤ a ∈ᴮ omegaTwo :=
    mem_of_mem_subset (inf_le_left.trans (inf_le_left.trans HA))
      (inf_le_right.trans inf_le_left)
  have Hsub : Θ ≤ fiber (bv_union A) f a ⊆ᴮ a :=
    union_selector_fiber_subset (inf_le_left.trans (Hf.trans inf_le_right))
  have Hbad : Θ ≤ injects_into omegaTwo omegaOne :=
    injects_into_trans (inf_le_right.trans inf_le_right)
      (injects_into_trans (injects_into_of_subset Hsub) (omegaTwo_member_injects Ha))
  exact bv_absurd _ Hbad omegaTwo_not_injects

/-- The actual union is itself a strict predecessor of omega-two. This is
an internal ordinal conclusion, not merely a cardinality bound. -/
theorem union_mem_omegaTwo {A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ A ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into A omegaOne) :
    Γ ≤ bv_union A ∈ᴮ omegaTwo := by
  have Hmembers : Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (Ord a ⊓ a ⊆ᴮ omegaTwo) := by
    apply le_iInf
    intro a
    rw [← deduction]
    have Ha : Γ ⊓ a ∈ᴮ A ≤ a ∈ᴮ omegaTwo :=
      mem_of_mem_subset (inf_le_left.trans HA) inf_le_right
    exact le_inf (Ord_of_mem_Ord Ha omegaTwo_Ord) (subset_of_mem_Ord Ha omegaTwo_Ord)
  have Hcases := (ErdosInitialSegments.union_initialSegment omegaTwo_Ord Hmembers).trans
    (inf_le_right.trans inf_le_right)
  have Hnot := union_not_omegaTwo_large HCH HA Hsmall
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · have Hlarge : Γ ⊓ (bv_union A =ᴮ omegaTwo) ≤ injects_into omegaTwo (bv_union A) :=
      bv_rw' (x := bv_union A) (y := omegaTwo)
        (ϕ := fun X => injects_into omegaTwo X) inf_le_right
        (h_congr := B_ext_injects_into_right) (H_new := injects_into_refl)
    exact (bv_absurd _ Hlarge (inf_le_left.trans Hnot)).trans bot_le
  · exact inf_le_right

/-- Any member of omega-two has a strictly later internal ordinal. The
checked large-tail theorem supplies a witness without a limit-ordinal axiom. -/
theorem exists_above_omegaTwo_member {a : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Ha : Γ ≤ a ∈ᴮ omegaTwo) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ omegaTwo ⊓ a ∈ᴮ b := by
  have Htail : Γ ≤ injects_into omegaTwo (difference omegaTwo (succ a)) :=
    ErdosLargeDifference.omegaTwo_injects_difference_succ HCH injects_into_refl Ha
  obtain ⟨b, Hb⟩ := ErdosSmallCodomainPigeonhole.exists_mem_of_injects_into
    Htail omegaOne_mem_omegaTwo
  rw [mem_difference] at Hb
  exact ⟨b, le_inf (Hb.trans inf_le_left)
    (ErdosOmegaReservoir.above_of_not_mem_succ Ha (Hb.trans inf_le_left)
      (Hb.trans inf_le_right))⟩

/-- Every omega-one-small internal subset has a single strict upper bound
still inside omega-two. The empty subset is included. -/
theorem exists_strict_upper_bound {A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ A ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into A omegaOne) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ omegaTwo ⊓ A ⊆ᴮ b := by
  have HU : Γ ≤ bv_union A ∈ᴮ omegaTwo := union_mem_omegaTwo HCH HA Hsmall
  obtain ⟨b, Hb⟩ := exists_above_omegaTwo_member HCH HU
  have HUord : Γ ≤ Ord (bv_union A) := Ord_of_mem_Ord HU omegaTwo_Ord
  have Hbord : Γ ≤ Ord b := Ord_of_mem_Ord (Hb.trans inf_le_left) omegaTwo_Ord
  refine ⟨b, le_inf (Hb.trans inf_le_left) ?_⟩
  rw [subset_unfold']
  apply le_iInf
  intro a
  rw [← deduction]
  let Δ := Γ ⊓ a ∈ᴮ A
  have Ha : Δ ≤ a ∈ᴮ omegaTwo := mem_of_mem_subset (inf_le_left.trans HA) inf_le_right
  have Hsub : Δ ≤ a ⊆ᴮ bv_union A :=
    (le_inf (le_top.trans ((bv_union_spec'' A).trans (iInf_le _ a)))
      (show Δ ≤ a ∈ᴮ A from inf_le_right)).trans bv_imp_elim
  have Hcases := (Ord.le_iff_lt_or_eq (Ord_of_mem_Ord Ha omegaTwo_Ord)
    (inf_le_left.trans HUord)).mp Hsub
  change Δ ≤ a ∈ᴮ b
  apply (le_inf (le_refl Δ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact mem_of_mem_Ord inf_le_right
      (inf_le_left.trans (inf_le_left.trans (Hb.trans inf_le_right)))
      (inf_le_left.trans (inf_le_left.trans Hbord))
  · exact mem_congr (bv_symm inf_le_right) bv_refl
      (inf_le_left.trans (inf_le_left.trans (Hb.trans inf_le_right)))

end bSet.ErdosOmegaTwoBounded
