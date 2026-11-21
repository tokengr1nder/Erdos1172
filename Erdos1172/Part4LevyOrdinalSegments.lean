/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCollapseNames
public import Erdos1172.Part4InternalCHHartogs

@[expose] public section

/-!
# Checked ordinal segments in the actual below-cardinal collapse

The pre-set for a coordinate has exactly that coordinate's alphabet as its
index type. Hence its collapse-name Boolean algebra is definitionally the
completion of `BelowCondition κ`; no equivalence of forcing products or
transport of Boolean coefficients is required.

Every checked predecessor of κ is internally countable, including the empty
predecessor. Boolean bounded universal quantification then proves the same
for arbitrary mixed members of checked κ. No regularity, GCH, noncollapse,
or identification of the new internal omega-one is assumed here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch Erdos1172LevyCollapse

universe u

namespace Erdos1172LevyCollapse

open bSet Erdos1172PosetCompletion Lattice

/-- A ground ordinal segment with exactly the alphabet of its collapse
coordinate as index type. Its children use the existing ordinal pre-sets. -/
def segmentPSet {κ : Cardinal.{u}} (i : κ.ord.ToType) : PSet.{u} :=
  PSet.mk (Set.Iio i) (fun j => PSet.ordinalMk j.val.toOrd.val)

/-- The new representation has precisely the members of the existing
canonical ordinal pre-set; only its indexing presentation changes. -/
theorem segmentPSet_equiv_ordinalMk {κ : Cardinal.{u}} (i : κ.ord.ToType) :
    PSet.Equiv (segmentPSet i) (PSet.ordinalMk i.toOrd.val) := by
  apply PSet.Mem.ext
  intro x
  change (∃ j : Set.Iio i, PSet.Equiv x (PSet.ordinalMk j.val.toOrd.val)) ↔
    x ∈ PSet.ordinalMk i.toOrd.val
  rw [PSet.mem_ordinalMk_iff]
  constructor
  · rintro ⟨j, hx⟩
    refine ⟨j.val.toOrd.val, ?_, hx⟩
    exact (Ordinal.ToType.mk.symm.lt_iff_lt).mpr j.property
  · rintro ⟨a, ha, hx⟩
    let a' : Set.Iio κ.ord := ⟨a, ha.trans i.toOrd.property⟩
    let j : κ.ord.ToType := Ordinal.ToType.mk a'
    have hjord : j.toOrd.val = a := by
      change (Ordinal.ToType.mk.symm (Ordinal.ToType.mk a')).val = a
      rw [OrderIso.symm_apply_apply]
    have hji : j < i := by
      apply (Ordinal.ToType.mk.symm.lt_iff_lt).mp
      change j.toOrd.val < i.toOrd.val
      rw [hjord]
      exact ha
    refine ⟨⟨j, hji⟩, ?_⟩
    change PSet.Equiv x (PSet.ordinalMk j.toOrd.val)
    rw [hjord]
    exact hx

/-- The actual coordinate collapse gives countability in the unchanged
below-κ algebra. Empty coordinate alphabets are handled separately, without
asserting a total function from omega onto the empty set. -/
theorem segmentPSet_countable (κ : Cardinal.{u}) (i : κ.ord.ToType) :
    (⊤ : Completion (BelowCondition κ)) ≤ injects_into (check (segmentPSet i)) bSet.omega := by
  classical
  by_cases h : Nonempty (Set.Iio i)
  · let : Nonempty (segmentPSet i).Type := h
    have Hsurj : (⊤ : Completion (BelowCondition κ)) ≤
        surjects_onto bSet.omega (check (segmentPSet i)) :=
      forces_coordinate_countable_surjection (segmentPSet (κ := κ)) i
    exact bSet.ErdosCHHartogs.injects_into_of_larger_than_ordinal Ord_omega
      (larger_than_of_surjects_onto Hsurj)
  · have Hequiv : PSet.Equiv (segmentPSet i) (∅ : PSet.{u}) := by
      apply PSet.equiv_iff.mpr
      constructor
      · intro j
        exact (h ⟨j⟩).elim
      · intro j
        cases j
    have Heq : (⊤ : Completion (BelowCondition κ)) ≤
        check (segmentPSet i) =ᴮ (∅ : bSet (Completion (BelowCondition κ))) := by
      simpa only [check_empty_eq_empty] using
        (check_bv_eq Hequiv : (⊤ : Completion (BelowCondition κ)) ≤
          check (segmentPSet i) =ᴮ check (∅ : PSet.{u}))
    exact bv_rw' Heq (ϕ := fun z => injects_into z bSet.omega)
      (h_congr := B_ext_injects_into_left)
      (H_new := injects_into_of_subset empty_subset)

/-- Countability of each checked predecessor in its canonical ordinal
representation, using Boolean equality rather than a forcing-type cast. -/
theorem checked_predecessor_countable (κ : Cardinal.{u}) (i : κ.ord.ToType) :
    (⊤ : Completion (BelowCondition κ)) ≤
      injects_into (check (PSet.ordinalMk i.toOrd.val)) bSet.omega :=
  bv_rw'' (ϕ := fun z => injects_into z bSet.omega)
    (check_bv_eq (segmentPSet_equiv_ordinalMk i))
    (segmentPSet_countable κ i) B_ext_injects_into_left

/-- All internal members of checked κ are countable. The quantifier covers
arbitrary mixed names, not only one globally chosen ground representative. -/
theorem below_checked_members_countable (κ : Cardinal.{u}) :
    (⊤ : Completion (BelowCondition κ)) ≤
      ⨅ x, _root_.imp (x ∈ᴮ check (PSet.ordinalMk κ.ord)) (injects_into x bSet.omega) := by
  rw [PSet.ordinalMk_eq_def, check_unfold]
  rw [← bounded_forall (h_congr := B_ext_injects_into_left)]
  change (⊤ : Completion (BelowCondition κ)) ≤
    ⨅ i : κ.ord.ToType, _root_.imp ⊤ (injects_into (check (PSet.ordinalMk i.toOrd.val)) bSet.omega)
  apply le_iInf
  intro i
  rw [top_imp]
  exact checked_predecessor_countable κ i

/-- Same-condition specialization for an arbitrary mixed predecessor. -/
theorem below_checked_member_countable (κ : Cardinal.{u})
    {Γ : Completion (BelowCondition κ)}
    {x : bSet (Completion (BelowCondition κ))}
    (Hx : Γ ≤ x ∈ᴮ check (PSet.ordinalMk κ.ord)) :
    Γ ≤ injects_into x bSet.omega :=
  (le_inf (le_top.trans ((below_checked_members_countable κ).trans (iInf_le _ x)))
    Hx).trans bv_imp_elim

end Erdos1172LevyCollapse
