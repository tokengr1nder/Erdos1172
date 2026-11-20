/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaGenericString
public import Erdos1172.Part4InternalCHHartogs

@[expose] public section

/-! # Passing from dense local collapse witnesses to the global bound

A graph witnessing a surjection may vary with the condition. Density makes
the existential truth value top, and the ordinal domain supplies an injection
in the reverse direction. Ground inclusion handles smaller ordinals.
-/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion
open scoped Flypitch
universe u
namespace Erdos1172Shioya

variable (κ θ : Cardinal.{u}) [Fact (Cardinal.aleph0 < κ)] [Nonempty (Condition κ θ)]

def DenseCheckedSurjections : Prop :=
  ∀ α : Ordinal.{u}, κ.ord < α → α < θ.ord → ∀ p : Condition κ θ, ∃ q ≤ p,
    condition q ≤ surjects_onto (check (PSet.ordinalMk κ.ord)) (check (PSet.ordinalMk α))

theorem surjects_onto_of_dense_surjections (hdense : DenseCheckedSurjections κ θ)
    (α : Ordinal.{u}) (hl : κ.ord < α) (hu : α < θ.ord) :
    (⊤ : Algebra κ θ) ≤ surjects_onto (check (PSet.ordinalMk κ.ord)) (check (PSet.ordinalMk α)) := by
  let D := {q : Condition κ θ | condition q ≤ surjects_onto (check (PSet.ordinalMk κ.ord)) (check (PSet.ordinalMk α))}
  have hD : ∀ p : Condition κ θ, ∃ q ∈ D, q ≤ p := by
    intro p
    obtain ⟨q, hqp, hq⟩ := hdense α hl hu p
    exact ⟨q, hq, hqp⟩
  rw [← iSup_condition_eq_top_of_dense D hD]
  exact iSup_le (fun t : D => t.property)

theorem checked_lt_injects_of_dense_surjections (hdense : DenseCheckedSurjections κ θ)
    (α : Ordinal.{u}) (hα : α < θ.ord) :
    (⊤ : Algebra κ θ) ≤ injects_into (check (PSet.ordinalMk α)) (check (PSet.ordinalMk κ.ord)) := by
  rcases le_or_gt α κ.ord with h | h
  · exact injects_into_of_subset (check_subset (ZFSet.subset_iff.mp (Ordinal.toZFSet_monotone h)))
  · exact ErdosCHHartogs.injects_into_of_larger_than_ordinal (check_Ord (PSet.Ord_mk κ.ord))
      (larger_than_of_surjects_onto (surjects_onto_of_dense_surjections κ θ hdense α h hα))

theorem mixed_below_injects_of_dense_surjections (hdense : DenseCheckedSurjections κ θ) :
    (⊤ : Algebra κ θ) ≤ ⨅ x, _root_.imp (x ∈ᴮ check (PSet.ordinalMk θ.ord))
      (injects_into x (check (PSet.ordinalMk κ.ord))) := by
  rw [PSet.ordinalMk_eq_def θ.ord, check_unfold, ← bounded_forall (h_congr := B_ext_injects_into_left)]
  change (⊤ : Algebra κ θ) ≤ ⨅ i : θ.ord.ToType,
    _root_.imp ⊤ (injects_into (check (PSet.ordinalMk i.toOrd.val)) (check (PSet.ordinalMk κ.ord)))
  apply le_iInf
  intro i
  rw [top_imp]
  exact checked_lt_injects_of_dense_surjections κ θ hdense i.toOrd.val i.toOrd.property

end Erdos1172Shioya
