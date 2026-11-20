/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenFreshCoordinates
public import Erdos1172.Part4GroundIndexNameBound
public import Erdos1172.Part4LevyOrdinalSegments

@[expose] public section

/-!
# Arbitrary small fresh ground coordinate families

The complement of any proper initial segment of the ground initial ordinal
of kappa has cardinality kappa. Every ground index type of cardinal at most
kappa therefore embeds there, without a nonemptiness or external countability
assumption. The resulting pre-set has exactly that original index type.

When its index cardinal is strictly below kappa, its checked name is
internally countable in the FIRST Levy algebra: it injects into the checked
ordinal of its ground index cardinal, which the actual collapse makes
countable. For regular uncountable kappa the same fresh coordinate set is
a subset of the first-stage internal omega-one. These are actual fresh
coordinates and an actual internal countability conclusion, not a supplied
enumeration, final-stage strict chain condition, or anonymous recovery.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCohen

open bSet ErdosOmegaTwo

/-- Every ground family of size at most kappa embeds beyond the given
initial segment. No external countability or nonemptiness is required. -/
theorem exists_indices_above_of_cardinal_le (κ : Cardinal.{u})
    (Hunc : Cardinal.aleph0 < κ) (I : Type u) (HI : Cardinal.mk I ≤ κ)
    (i : κ.ord.ToType) :
    ∃ j : I → κ.ord.ToType, Function.Injective j ∧ ∀ x, i ≤ j x := by
  classical
  let : Infinite κ.ord.ToType := Cardinal.infinite_iff.mpr (by simpa using Hunc.le)
  have Hsmall : Cardinal.mk (Set.Iio i) < Cardinal.mk κ.ord.ToType :=
    Cardinal.mk_Iio_lt i (by simp)
  have Hcard : Cardinal.mk ((Set.Iio i)ᶜ : Set κ.ord.ToType) = κ := by
    simpa using Cardinal.mk_compl_of_infinite (Set.Iio i) Hsmall
  have Hbound : Cardinal.mk I ≤ Cardinal.mk ((Set.Iio i)ᶜ : Set κ.ord.ToType) :=
    HI.trans_eq Hcard.symm
  obtain ⟨e⟩ := (Cardinal.le_def I ((Set.Iio i)ᶜ : Set κ.ord.ToType)).mp Hbound
  refine ⟨fun x => (e x).val, ?_, ?_⟩
  · intro x y Hxy
    exact e.injective (Subtype.ext Hxy)
  · intro x
    exact le_of_not_gt (e x).property

/-- The fresh labels use the exact child type of the ground ordinal. -/
theorem exists_fresh_ground_indices_of_cardinal_le (κ : Cardinal.{u})
    (Hunc : Cardinal.aleph0 < κ) (I : Type u) (HI : Cardinal.mk I ≤ κ)
    (i : κ.ord.ToType) :
    ∃ j : I → (PSet.ordinalMk κ.ord).Type, Function.Injective j ∧
      ∀ x, (PSet.ordinalMk κ.ord).Func (j x) ∉ PSet.ordinalMk i.toOrd.val := by
  obtain ⟨j, Hj, Habove⟩ := exists_indices_above_of_cardinal_le κ Hunc I HI i
  rw [PSet.ordinalMk_eq_def κ.ord]
  refine ⟨j, Hj, ?_⟩
  intro x Hmem
  change PSet.ordinalMk (j x).toOrd.val ∈ PSet.ordinalMk i.toOrd.val at Hmem
  have Hlt : (j x).toOrd.val < i.toOrd.val := PSet.ordinalMk_lt_of_mem Hmem
  exact (not_lt_of_ge (Habove x)) ((Ordinal.ToType.mk.symm.lt_iff_lt).mp Hlt)

/-- The coordinate pre-set retains the original index type, not a quotient
or a externally countable reindexing. -/
def freshCoordinateSet {κ : Cardinal.{u}} {I : Type u}
    (j : I → (PSet.ordinalMk κ.ord).Type) : PSet.{u} :=
  PSet.mk I (fun x => (PSet.ordinalMk κ.ord).Func (j x))

theorem freshCoordinateSet_type {κ : Cardinal.{u}} {I : Type u}
    (j : I → (PSet.ordinalMk κ.ord).Type) :
    (freshCoordinateSet j).Type = I := rfl

theorem freshCoordinateSet_func {κ : Cardinal.{u}} {I : Type u}
    (j : I → (PSet.ordinalMk κ.ord).Type) (x : I) :
    (freshCoordinateSet j).Func x = (PSet.ordinalMk κ.ord).Func (j x) := rfl

theorem freshCoordinateSet_subset {κ : Cardinal.{u}} {I : Type u}
    (j : I → (PSet.ordinalMk κ.ord).Type) :
    freshCoordinateSet j ⊆ PSet.ordinalMk κ.ord := by
  intro x
  exact ⟨j x, PSet.Equiv.refl _⟩

theorem freshCoordinateSet_separated {κ : Cardinal.{u}} {I : Type u}
    {j : I → (PSet.ordinalMk κ.ord).Type} (Hj : Function.Injective j) :
    ∀ x y : I, x ≠ y →
      ¬ PSet.Equiv ((freshCoordinateSet j).Func x) ((freshCoordinateSet j).Func y) := by
  intro x y Hxy
  exact PSet.ordinalMk_inj κ.ord (j x) (j y) (fun h => Hxy (Hj h))

/-- Separation remains valid at top for arbitrary checked-coordinate
arguments in the first-stage Boolean algebra. -/
theorem freshCoordinateSet_checked_separated {κ : Cardinal.{u}} {I : Type u}
    {j : I → (PSet.ordinalMk κ.ord).Type} (Hj : Function.Injective j) :
    ∀ x y : I, x ≠ y → (⊤ : FirstAlgebra κ) ≤
      (check ((freshCoordinateSet j).Func x) =ᴮ
        check ((freshCoordinateSet j).Func y))ᶜ := by
  intro x y Hxy
  have Hneq : (check ((freshCoordinateSet j).Func x) : bSet (FirstAlgebra κ)) =ᴮ
      check ((freshCoordinateSet j).Func y) = ⊥ :=
    check_bv_eq_bot_of_not_equiv (freshCoordinateSet_separated Hj x y Hxy)
  rw [Hneq, compl_bot]

/-- Every checked ground pre-set with a small index type is internally
countable in the first-stage collapse. Separation, regularity, and external
countability are unnecessary for this cardinal-comparison direction. -/
theorem firstStage_checked_countable_of_cardinal_lt (κ : Cardinal.{u})
    (C : PSet.{u}) (HC : Cardinal.mk C.Type < κ) :
    (⊤ : FirstAlgebra κ) ≤ injects_into (check C) omega := by
  have Hindex : Cardinal.mk (check C : bSet (FirstAlgebra κ)).type ≤
      Cardinal.mk C.Type := by
    simpa only [check_type'] using (le_rfl : Cardinal.mk C.Type ≤ Cardinal.mk C.Type)
  have Hinj : (⊤ : FirstAlgebra κ) ≤ injects_into (check C)
      (check (PSet.ordinalMk (Cardinal.mk C.Type).ord)) :=
    ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
      (Cardinal.mk C.Type) (check C) Hindex
  have Hmember : (⊤ : FirstAlgebra κ) ≤
      check (PSet.ordinalMk (Cardinal.mk C.Type).ord) ∈ᴮ
        check (PSet.ordinalMk κ.ord) :=
    check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr HC))
  exact injects_into_trans Hinj
    (Erdos1172LevyCollapse.below_checked_member_countable κ Hmember)

theorem freshCoordinateSet_checked_countable (κ : Cardinal.{u}) {I : Type u}
    (j : I → (PSet.ordinalMk κ.ord).Type) (HI : Cardinal.mk I < κ) :
    (⊤ : FirstAlgebra κ) ≤ injects_into (check (freshCoordinateSet j)) omega :=
  firstStage_checked_countable_of_cardinal_lt κ (freshCoordinateSet j) HI

theorem freshCoordinateSet_checked_subset_omegaOne (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) {I : Type u}
    (j : I → (PSet.ordinalMk κ.ord).Type) :
    (⊤ : FirstAlgebra κ) ≤ check (freshCoordinateSet j) ⊆ᴮ omegaOne :=
  subset_trans' (check_subset (freshCoordinateSet_subset j))
    (subset_of_eq (firstStage_checked_upper_eq_omegaOne κ Hκ Hunc))

/-- Ground freshness yields actual top-valued checked freshness for every
label of the same coordinate pre-set. -/
theorem freshCoordinateSet_checked_fresh {κ : Cardinal.{u}} {I : Type u}
    {j : I → (PSet.ordinalMk κ.ord).Type} {i : κ.ord.ToType}
    (Hfresh : ∀ x, (PSet.ordinalMk κ.ord).Func (j x) ∉ PSet.ordinalMk i.toOrd.val) :
    ∀ x : I, (⊤ : FirstAlgebra κ) ≤
      (check ((freshCoordinateSet j).Func x) ∈ᴮ check (PSet.ordinalMk i.toOrd.val))ᶜ := by
  intro x
  have Hnot : (check ((freshCoordinateSet j).Func x) : bSet (FirstAlgebra κ)) ∈ᴮ
      check (PSet.ordinalMk i.toOrd.val) = ⊥ :=
    not_check_mem_iff.mp (Hfresh x)
  rw [Hnot, compl_bot]

/-- Actual small fresh checked coordinates, with internal countability
proved from the collapse, not supplied as an external enumeration. Ground
and Boolean separation follow from `Hj` by the preceding public lemmas. -/
theorem exists_small_fresh_checked_coordinates (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (I : Type u) (HI : Cardinal.mk I < κ) (i : κ.ord.ToType) :
    ∃ j : I → (PSet.ordinalMk κ.ord).Type, Function.Injective j ∧
      ((⊤ : FirstAlgebra κ) ≤ check (freshCoordinateSet j) ⊆ᴮ omegaOne) ∧
      ((⊤ : FirstAlgebra κ) ≤ injects_into (check (freshCoordinateSet j)) omega) ∧
      ∀ x : I, (⊤ : FirstAlgebra κ) ≤
        (check ((freshCoordinateSet j).Func x) ∈ᴮ check (PSet.ordinalMk i.toOrd.val))ᶜ := by
  obtain ⟨j, Hj, Hfresh⟩ := exists_fresh_ground_indices_of_cardinal_le κ Hunc I HI.le i
  exact ⟨j, Hj, freshCoordinateSet_checked_subset_omegaOne κ Hκ Hunc j,
    freshCoordinateSet_checked_countable κ j HI, freshCoordinateSet_checked_fresh Hfresh⟩

/-- In particular, a small ground label set times the full natural index
type is still small, even when the label set is not externally countable. -/
theorem small_times_nat_cardinal_lt (κ : Cardinal.{u})
    (Hunc : Cardinal.aleph0 < κ) (I : Type u) (HI : Cardinal.mk I < κ) :
    Cardinal.mk (I × ULift.{u} ℕ) < κ := by
  simpa only [Cardinal.mk_prod, Cardinal.mk_uLift, Cardinal.mk_nat,
    Cardinal.lift_aleph0, Cardinal.lift_id] using Cardinal.mul_lt_of_lt Hunc.le HI Hunc

end Erdos1172LevyCohen
