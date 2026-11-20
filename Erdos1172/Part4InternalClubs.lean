/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIndexedIntersection
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
# Internal closed and unbounded predicates

All bounds, subsets, and indexed families are arbitrary Boolean-valued
names. Unboundedness uses strictly later members inside the bound. Closure
includes every nonzero internal limit point. Fullness gives an actual
unboundedness witness at the original Boolean condition. Intersections of
closed values are closed, with no nonempty-index or external-family premise.
No stationary-set existence or club-intersection unboundedness is asserted.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosIndexedIntersection

def unboundedIn (κ C : bSet 𝔹) : 𝔹 :=
  ⨅ a, _root_.imp (a ∈ᴮ κ) (⨆ b, (b ∈ᴮ C ⊓ b ∈ᴮ κ) ⊓ a ∈ᴮ b)

def closedIn (κ C : bSet 𝔹) : 𝔹 :=
  ⨅ a, _root_.imp ((a ∈ᴮ κ ⊓ (a =ᴮ (∅ : bSet 𝔹))ᶜ) ⊓ unboundedIn a C)
    (a ∈ᴮ C)

def club (κ C : bSet 𝔹) : 𝔹 :=
  C ⊆ᴮ κ ⊓ (unboundedIn κ C ⊓ closedIn κ C)

theorem unboundedIn_ext_set (κ : bSet 𝔹) : B_ext (unboundedIn κ) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ =>
      B_ext_inf (B_ext_inf B_ext_mem_right B_ext_const) B_ext_const)))

theorem unboundedIn_ext_bound (C : bSet 𝔹) :
    B_ext (fun κ => unboundedIn κ C) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right)
    (h₂ := B_ext_iSup (h := fun _ =>
      B_ext_inf (B_ext_inf B_ext_const B_ext_mem_right) B_ext_const)))

theorem closedIn_ext_set (κ : bSet 𝔹) : B_ext (closedIn κ) :=
  B_ext_iInf (h := fun a => B_ext_imp
    (h₁ := B_ext_inf B_ext_const (unboundedIn_ext_set a)) (h₂ := B_ext_mem_right))

theorem closedIn_ext_bound (C : bSet 𝔹) :
    B_ext (fun κ => closedIn κ C) :=
  B_ext_iInf (h := fun _ => B_ext_imp
    (h₁ := B_ext_inf (B_ext_inf B_ext_mem_right B_ext_const) B_ext_const)
    (h₂ := B_ext_const))

theorem club_ext_set (κ : bSet 𝔹) : B_ext (club κ) :=
  B_ext_inf B_ext_subset_left (B_ext_inf (unboundedIn_ext_set κ) (closedIn_ext_set κ))

theorem club_ext_bound (C : bSet 𝔹) : B_ext (fun κ => club κ C) :=
  B_ext_inf B_ext_subset_right (B_ext_inf (unboundedIn_ext_bound C) (closedIn_ext_bound C))

theorem unboundedIn_apply {κ C a : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ unboundedIn κ C) (Ha : Γ ≤ a ∈ᴮ κ) :
    Γ ≤ ⨆ b, (b ∈ᴮ C ⊓ b ∈ᴮ κ) ⊓ a ∈ᴮ b :=
  (le_inf (HU.trans (iInf_le _ a)) Ha).trans bv_imp_elim

/-- The witness is one actual name at the same condition, not an external
ordinal obtained by splitting the Boolean truth into ground cases. -/
theorem exists_unbounded_above {κ C a : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ unboundedIn κ C) (Ha : Γ ≤ a ∈ᴮ κ) :
    ∃ b : bSet 𝔹, Γ ≤ (b ∈ᴮ C ⊓ b ∈ᴮ κ) ⊓ a ∈ᴮ b :=
  exists_convert (unboundedIn_apply HU Ha)
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_left) B_ext_mem_right)

theorem closedIn_apply {κ C a : bSet 𝔹} {Γ : 𝔹}
    (HC : Γ ≤ closedIn κ C) (Ha : Γ ≤ a ∈ᴮ κ)
    (Hne : Γ ≤ (a =ᴮ (∅ : bSet 𝔹))ᶜ) (HU : Γ ≤ unboundedIn a C) :
    Γ ≤ a ∈ᴮ C :=
  (le_inf (HC.trans (iInf_le _ a)) (le_inf (le_inf Ha Hne) HU)).trans bv_imp_elim

/-- Enlarging the set preserves unboundedness; the bound is unchanged. -/
theorem unboundedIn_mono {κ C D : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ C ⊆ᴮ D) (HU : Γ ≤ unboundedIn κ C) :
    Γ ≤ unboundedIn κ D := by
  apply le_iInf
  intro a
  rw [← deduction]
  obtain ⟨b, Hb⟩ := exists_unbounded_above (inf_le_left.trans HU) inf_le_right
  exact le_iSup_of_le b (le_inf
    (le_inf (mem_of_mem_subset (inf_le_left.trans Hsub)
      (Hb.trans (inf_le_left.trans inf_le_left)))
      (Hb.trans (inf_le_left.trans inf_le_right))) (Hb.trans inf_le_right))

theorem club_subset {κ C : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ club κ C) : Γ ≤ C ⊆ᴮ κ := H.trans inf_le_left

theorem club_unbounded {κ C : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ club κ C) : Γ ≤ unboundedIn κ C :=
  H.trans (inf_le_right.trans inf_le_left)

theorem club_closed {κ C : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ club κ C) : Γ ≤ closedIn κ C :=
  H.trans (inf_le_right.trans inf_le_right)

theorem exists_club_above {κ C a : bSet 𝔹} {Γ : 𝔹}
    (HC : Γ ≤ club κ C) (Ha : Γ ≤ a ∈ᴮ κ) :
    ∃ b : bSet 𝔹, Γ ≤ (b ∈ᴮ C ⊓ b ∈ᴮ κ) ⊓ a ∈ᴮ b :=
  exists_unbounded_above (club_unbounded HC) Ha

theorem indexedIntersection_subset_value {κ T F i A : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ∈ᴮ T) (Hpair : Γ ≤ pair i A ∈ᴮ F) :
    Γ ≤ indexedIntersection κ F T ⊆ᴮ A := by
  rw [subset_unfold']
  apply le_iInf
  intro a
  rw [← deduction]
  have Ha := mem_indexedIntersection_iff.mp
    (show Γ ⊓ a ∈ᴮ indexedIntersection κ F T ≤
      a ∈ᴮ indexedIntersection κ F T from inf_le_right)
  exact (le_inf (Ha.2.trans ((iInf_le _ i).trans (iInf_le _ A)))
    (le_inf (inf_le_left.trans Hi) (inf_le_left.trans Hpair))).trans bv_imp_elim

/-- The actual bounded intersection of all guarded closed values is
closed. The family may be empty, and functionality is not needed for this
closure direction: each value occurring in the graph is constrained. -/
theorem closedIn_indexedIntersection {κ T F : bSet 𝔹} {Γ : 𝔹}
    (Hclosed : Γ ≤ ⨅ i, ⨅ A, _root_.imp
      (i ∈ᴮ T ⊓ pair i A ∈ᴮ F) (closedIn κ A)) :
    Γ ≤ closedIn κ (indexedIntersection κ F T) := by
  apply le_iInf
  intro a
  rw [← deduction]
  let Δ := Γ ⊓ ((a ∈ᴮ κ ⊓ (a =ᴮ (∅ : bSet 𝔹))ᶜ) ⊓
    unboundedIn a (indexedIntersection κ F T))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Ha : Δ ≤ a ∈ᴮ κ := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hne : Δ ≤ (a =ᴮ (∅ : bSet 𝔹))ᶜ :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have HU : Δ ≤ unboundedIn a (indexedIntersection κ F T) :=
    inf_le_right.trans inf_le_right
  apply mem_indexedIntersection_iff.mpr
  refine ⟨Ha, ?_⟩
  apply le_iInf
  intro i
  apply le_iInf
  intro A
  rw [← deduction]
  have HA : Δ ⊓ (i ∈ᴮ T ⊓ pair i A ∈ᴮ F) ≤ closedIn κ A :=
    (le_inf (inf_le_left.trans (HΔ.trans
      (Hclosed.trans ((iInf_le _ i).trans (iInf_le _ A))))) inf_le_right).trans bv_imp_elim
  exact closedIn_apply HA (inf_le_left.trans Ha) (inf_le_left.trans Hne)
    (unboundedIn_mono
      (indexedIntersection_subset_value (inf_le_right.trans inf_le_left)
        (inf_le_right.trans inf_le_right)) (inf_le_left.trans HU))

end bSet.ErdosClubs
