/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaSequence
public import Erdos1172.Part4InternalGraphNeighborhood
public import Erdos1172.Part4InternalPartitionGraph

@[expose] public section

/-!
# Homogeneity of a concrete internal omega sequence

Color information on numeral-indexed values transfers to the entire internal
range of the actual sequence graph. Both range joins are distributed under
the original Boolean context, so mixed internal names are included. Neither
increasingness nor a global disjointness hypothesis on the values is needed.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaSequence

open ErdosPartition

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Exact internal range membership, including arbitrary mixed values. -/
theorem rangeMem_sequenceGraph (v : ℕ → bSet 𝔹) (x : bSet 𝔹) :
    rangeMem bSet.omega (sequenceGraph v) x =
      ⨆ n : (bSet.omega : bSet 𝔹).type, x =ᴮ v n.down := by
  apply le_antisymm
  · unfold rangeMem
    apply iSup_le
    intro i
    apply (inf_le_right : i ∈ᴮ bSet.omega ⊓ pair i x ∈ᴮ sequenceGraph v ≤
      pair i x ∈ᴮ sequenceGraph v).trans
    rw [mem_sequenceGraph]
    apply iSup_le
    intro n
    exact le_iSup_of_le n eq_of_eq_pair_right
  · apply iSup_le
    intro n
    apply le_iSup_of_le (of_nat n.down)
    exact le_inf of_nat_mem_omega (pair_of_nat_mem_iff.mpr le_rfl)

/-- Ordered range points inherit the common symmetric color. Equal numeral
branches are impossible because the two range points are membership-ordered. -/
theorem graphColor_of_sequenceGraph_range {color : Bool}
    {R : bSet 𝔹} {v : ℕ → bSet 𝔹} {x y : bSet 𝔹} {Γ : 𝔹}
    (Hcolor : ∀ m n, m < n → Γ ≤ graphColor color R (v m) (v n))
    (Hx : Γ ≤ rangeMem bSet.omega (sequenceGraph v) x)
    (Hy : Γ ≤ rangeMem bSet.omega (sequenceGraph v) y)
    (Hxy : Γ ≤ x ∈ᴮ y) : Γ ≤ graphColor color R x y := by
  apply (le_inf (le_refl Γ) (Hx.trans (rangeMem_sequenceGraph v x).le)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro m
  apply (le_inf (le_refl (Γ ⊓ x =ᴮ v m.down))
    (inf_le_left.trans (Hy.trans (rangeMem_sequenceGraph v y).le))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  let Δ := (Γ ⊓ x =ᴮ v m.down) ⊓ y =ᴮ v n.down
  have Hxv : Δ ≤ x =ᴮ v m.down := inf_le_left.trans inf_le_right
  have Hyv : Δ ≤ y =ᴮ v n.down := inf_le_right
  have Hvalues : Δ ≤ graphColor color R (v m.down) (v n.down) := by
    rcases lt_trichotomy m.down n.down with hlt | heq | hgt
    · exact inf_le_left.trans (inf_le_left.trans (Hcolor _ _ hlt))
    · have Hself : Δ ≤ v m.down ∈ᴮ v n.down :=
        mem_congr Hxv Hyv (inf_le_left.trans (inf_le_left.trans Hxy))
      rw [heq] at Hself
      exact (bot_of_mem_self' Hself).trans bot_le
    · rw [graphColor_symm color R (v m.down) (v n.down)]
      exact inf_le_left.trans (inf_le_left.trans (Hcolor _ _ hgt))
  exact bv_rw' (ϕ := fun z => graphColor color R z y) Hxv
    (h_congr := graphColor_ext_left color R y)
    (H_new := bv_rw' (ϕ := graphColor color R (v m.down)) Hyv
      (h_congr := graphColor_ext_right color R (v m.down)) (H_new := Hvalues))

/-- Local same-color information on all increasing numeral pairs makes the
whole internal sequence range homogeneous in the exact partition semantics. -/
theorem sequenceGraph_homogeneousUnion {color : Bool}
    {R : bSet 𝔹} {v : ℕ → bSet 𝔹} {Γ : 𝔹}
    (Hcolor : ∀ m n, m < n → Γ ≤ graphColor color R (v m) (v n)) :
    Γ ≤ homogeneousUnion color R bSet.omega bSet.omega
      (sequenceGraph v) (sequenceGraph v) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  simp only [sup_self]
  let Δ := Γ ⊓ ((rangeMem bSet.omega (sequenceGraph v) x ⊓
    rangeMem bSet.omega (sequenceGraph v) y) ⊓ x ∈ᴮ y)
  have Hxy : Δ ≤ x ∈ᴮ y := inf_le_right.trans inf_le_right
  apply (le_graphColor_iff_oriented color R Hxy).mp
  exact graphColor_of_sequenceGraph_range
    (fun m n h => inf_le_left.trans (Hcolor m n h))
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right)) Hxy

end bSet.ErdosOmegaSequence
