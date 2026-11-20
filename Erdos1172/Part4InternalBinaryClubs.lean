/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClubIntersection

@[expose] public section

/-!
# Binary intersections of internal omega-two clubs

An actual omega-indexed function lists the first club at zero and the
second club at every other numeral. Its checked internal graph includes
mixed natural names. The small-family club theorem supplies unboundedness
of a subset of the binary intersection; closure is proved directly.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOmegaSequence ErdosIndexedIntersection

/-- Binary intersections preserve internal closure, without any cardinal
or unboundedness premise on the ambient name. -/
theorem closedIn_binary_inter {κ C D : bSet 𝔹} {Γ : 𝔹}
    (HC : Γ ≤ closedIn κ C) (HD : Γ ≤ closedIn κ D) :
    Γ ≤ closedIn κ (C ∩ᴮ D) := by
  apply le_iInf
  intro a
  rw [← deduction]
  let Δ := Γ ⊓ ((a ∈ᴮ κ ⊓ (a =ᴮ (∅ : bSet 𝔹))ᶜ) ⊓
    unboundedIn a (C ∩ᴮ D))
  have Ha : Δ ≤ a ∈ᴮ κ := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hne : Δ ≤ (a =ᴮ (∅ : bSet 𝔹))ᶜ :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have HU : Δ ≤ unboundedIn a (C ∩ᴮ D) := inf_le_right.trans inf_le_right
  exact mem_binary_inter_iff.mpr
    ⟨closedIn_apply (inf_le_left.trans HC) Ha Hne
      (unboundedIn_mono binary_inter_subset_left HU),
     closedIn_apply (inf_le_left.trans HD) Ha Hne
      (unboundedIn_mono binary_inter_subset_right HU)⟩

/-- Two internal omega-two clubs have unbounded binary intersection.
The indexed family used in the proof is an actual internal function. -/
theorem unboundedIn_binary_inter {C D : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HC : Γ ≤ club omegaTwo C) (HD : Γ ≤ club omegaTwo D) :
    Γ ≤ unboundedIn omegaTwo (C ∩ᴮ D) := by
  classical
  let v (n : ℕ) : bSet 𝔹 := if n = 0 then C else D
  have Hv (n : ℕ) : Γ ≤ club omegaTwo (v n) := by
    by_cases h : n = 0
    · simpa only [v, if_pos h] using HC
    · simpa only [v, if_neg h] using HD
  have HF : Γ ≤ is_func' bSet.omega (bv_powerset omegaTwo) (sequenceGraph v) :=
    is_func'_of_is_function (sequenceGraph_is_function
      (fun n => mem_powerset_iff.mpr (club_subset (Hv n))))
  have HQ : Γ ≤ injects_into bSet.omega omegaOne :=
    injects_into_of_subset (subset_of_mem_Ord omega_mem_omegaOne omegaOne_Ord)
  have Hclubs : Γ ≤ ⨅ q, ⨅ E,
      _root_.imp (q ∈ᴮ bSet.omega ⊓ pair q E ∈ᴮ sequenceGraph v)
        (club omegaTwo E) := by
    apply le_iInf
    intro q
    apply le_iInf
    intro E
    rw [← deduction]
    let Δ := Γ ⊓ (q ∈ᴮ bSet.omega ⊓ pair q E ∈ᴮ sequenceGraph v)
    have Hgraph : Δ ≤ pair q E ∈ᴮ sequenceGraph v := inf_le_right.trans inf_le_right
    rw [mem_sequenceGraph] at Hgraph
    apply (le_inf (le_refl Δ) Hgraph).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    have HE : Δ ⊓ (pair q E =ᴮ pair (of_nat n.down) (v n.down)) ≤ E =ᴮ v n.down :=
      eq_of_eq_pair_right' inf_le_right
    exact bv_rw' (x := E) (y := v n.down) (ϕ := club omegaTwo) HE
      (h_congr := club_ext_set omegaTwo)
      (H_new := inf_le_left.trans (inf_le_left.trans (Hv n.down)))
  have Hcommon := unboundedIn_indexedIntersection HCH HF HQ Hclubs
  have Hzero : Γ ≤ pair (of_nat 0) C ∈ᴮ sequenceGraph v := by
    change Γ ≤ pair (of_nat 0) (v 0) ∈ᴮ sequenceGraph v
    exact sequenceGraph_pair
  have Hone : Γ ≤ pair (of_nat 1) D ∈ᴮ sequenceGraph v := by
    change Γ ≤ pair (of_nat 1) (v 1) ∈ᴮ sequenceGraph v
    exact sequenceGraph_pair
  have Hsub : Γ ≤ indexedIntersection omegaTwo (sequenceGraph v) bSet.omega ⊆ᴮ
      C ∩ᴮ D :=
    subset_binary_inter_iff.mpr
      ⟨indexedIntersection_subset_value of_nat_mem_omega Hzero,
       indexedIntersection_subset_value of_nat_mem_omega Hone⟩
  exact unboundedIn_mono Hsub Hcommon

/-- The actual binary intersection of two omega-two clubs is a club,
under the same internal CH condition used for small-family intersection. -/
theorem club_binary_inter {C D : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HC : Γ ≤ club omegaTwo C) (HD : Γ ≤ club omegaTwo D) :
    Γ ≤ club omegaTwo (C ∩ᴮ D) :=
  le_inf (subset_trans' binary_inter_subset_left (club_subset HC))
    (le_inf (unboundedIn_binary_inter HCH HC HD)
      (closedIn_binary_inter (club_closed HC) (club_closed HD)))

end bSet.ErdosClubs
