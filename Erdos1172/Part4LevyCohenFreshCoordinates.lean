/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenIteration
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Fresh ground coordinates beyond any checked initial segment

The complement of an initial segment of the initial ordinal of kappa has
cardinality kappa. It therefore contains an actual externally injective
natural-number sequence. The bound need not be externally countable.

For the first-stage regular uncountable collapse, the same coordinates
are top-members of internal omega-one, pairwise top-distinct, and outside
the checked bound at top. No final-stage chain condition, ideal, or
generic-subset encoding is assumed or concluded.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCohen

open bSet ErdosOmegaTwo

/-- The sequence lies at or above the bound, which suffices to be outside
the corresponding strict ordinal initial segment. Regularity is not needed. -/
theorem exists_countable_indices_above (κ : Cardinal.{u})
    (Hunc : Cardinal.aleph0 < κ) (i : κ.ord.ToType) :
    ∃ j : ℕ → κ.ord.ToType, Function.Injective j ∧ ∀ n, i ≤ j n := by
  classical
  let : Infinite κ.ord.ToType := Cardinal.infinite_iff.mpr (by simpa using Hunc.le)
  have Hsmall : Cardinal.mk (Set.Iio i) < Cardinal.mk κ.ord.ToType :=
    Cardinal.mk_Iio_lt i (by simp)
  have Hcard : Cardinal.mk ((Set.Iio i)ᶜ : Set κ.ord.ToType) = κ := by
    simpa using Cardinal.mk_compl_of_infinite (Set.Iio i) Hsmall
  have Hcount : Cardinal.mk (ULift.{u} ℕ) ≤
      Cardinal.mk ((Set.Iio i)ᶜ : Set κ.ord.ToType) := by
    simpa only [Hcard, Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
      using Hunc.le
  obtain ⟨e⟩ := (Cardinal.le_def (ULift.{u} ℕ)
    ((Set.Iio i)ᶜ : Set κ.ord.ToType)).mp Hcount
  let j : ℕ → κ.ord.ToType := fun n => (e ⟨n⟩).val
  refine ⟨j, ?_, ?_⟩
  · intro m n h
    have Heq : (⟨m⟩ : ULift.{u} ℕ) = ⟨n⟩ := e.injective (Subtype.ext h)
    exact congrArg ULift.down Heq
  · intro n
    exact le_of_not_gt (e ⟨n⟩).property

/-- The sequence uses the exact child-index type of the checked ordinal,
not a forcing-alphabet transport or a supplied fresh-coordinate family. -/
theorem exists_fresh_ground_indices (κ : Cardinal.{u})
    (Hunc : Cardinal.aleph0 < κ) (i : κ.ord.ToType) :
    ∃ j : ℕ → (PSet.ordinalMk κ.ord).Type, Function.Injective j ∧
      ∀ n, (PSet.ordinalMk κ.ord).Func (j n) ∉
        PSet.ordinalMk i.toOrd.val := by
  obtain ⟨j, Hj, Habove⟩ := exists_countable_indices_above κ Hunc i
  rw [PSet.ordinalMk_eq_def κ.ord]
  refine ⟨j, Hj, ?_⟩
  intro n Hmem
  change PSet.ordinalMk (j n).toOrd.val ∈ PSet.ordinalMk i.toOrd.val at Hmem
  have Hlt : (j n).toOrd.val < i.toOrd.val := PSet.ordinalMk_lt_of_mem Hmem
  exact (not_lt_of_ge (Habove n)) ((Ordinal.ToType.mk.symm.lt_iff_lt).mp Hlt)

/-- Checked freshness and separation for the same actual ground sequence.
The omega-one membership is specifically in the first-stage algebra. -/
theorem exists_fresh_checked_coordinates (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) (i : κ.ord.ToType) :
    ∃ j : ℕ → (PSet.ordinalMk κ.ord).Type, Function.Injective j ∧
      (∀ n, (⊤ : FirstAlgebra κ) ≤
        check ((PSet.ordinalMk κ.ord).Func (j n)) ∈ᴮ omegaOne) ∧
      (∀ m n, m ≠ n → (⊤ : FirstAlgebra κ) ≤
        (check ((PSet.ordinalMk κ.ord).Func (j m)) =ᴮ
          check ((PSet.ordinalMk κ.ord).Func (j n)))ᶜ) ∧
      ∀ n, (⊤ : FirstAlgebra κ) ≤
        (check ((PSet.ordinalMk κ.ord).Func (j n)) ∈ᴮ
          check (PSet.ordinalMk i.toOrd.val))ᶜ := by
  obtain ⟨j, Hj, Hfresh⟩ := exists_fresh_ground_indices κ Hunc i
  refine ⟨j, Hj, ?_, ?_, ?_⟩
  · intro n
    exact firstStage_coordinate_mem κ Hκ Hunc (j n)
  · intro m n Hmn
    have Hneq : (check ((PSet.ordinalMk κ.ord).Func (j m)) : bSet (FirstAlgebra κ)) =ᴮ
        check ((PSet.ordinalMk κ.ord).Func (j n)) = ⊥ :=
      check_bv_eq_bot_of_not_equiv
        (PSet.ordinalMk_inj κ.ord (j m) (j n) (fun h => Hmn (Hj h)))
    rw [Hneq, compl_bot]
  · intro n
    have Hnot : (check ((PSet.ordinalMk κ.ord).Func (j n)) : bSet (FirstAlgebra κ)) ∈ᴮ
        check (PSet.ordinalMk i.toOrd.val) = ⊥ :=
      not_check_mem_iff.mp (Hfresh n)
    rw [Hnot, compl_bot]

end Erdos1172LevyCohen
