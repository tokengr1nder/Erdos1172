/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenIndexedBinaryAssignment
public import Erdos1172.Part4LevyCohenSmallFreshCoordinates
public import Erdos1172.Part4LevyCohenDomainBound
public import Erdos1172.Part4CohenBitAssignmentBridge

@[expose] public section

/-!
# Coding small ground-indexed Boolean families into fresh Cohen bits

Every ground index type of cardinality strictly below kappa admits a
separated family of fresh fixed ground coordinates after a ground-bound
refinement. Its whole checked coordinate set is internally countable in
the first Levy algebra, even if the index type is not externally countable.

The actual whole-index binary assignment graph can therefore be adjoined
at the same first-stage Boolean condition. One canonical refinement then
gives an actual stronger iteration condition coding every supplied Boolean
coefficient, with the original index type and its injective ground labels.

Only regular uncountable kappa is required. There is no GCH, inaccessible,
ideal, nonemptiness, supplied enumeration, or global branch assumption.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet bSet.ErdosOmegaTwo bSet.ErdosPartialInjection

/-- Any small ground-indexed family of first-stage coefficients is coded
by distinct fresh checked coordinates below one actual stronger condition. -/
theorem exists_small_binary_coding_extension (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (I : Type u) (HI : Cardinal.mk I < κ)
    (p : Erdos1172CohenIteration.Conditions (omegaOne : bSet (FirstAlgebra κ)))
    (b : I → FirstAlgebra κ) :
    ∃ r : Erdos1172CohenIteration.Conditions (omegaOne : bSet (FirstAlgebra κ)),
      r ≤ p ∧ ∃ j : I → (PSet.ordinalMk κ.ord).Type,
        Function.Injective j ∧
        ∀ x, Erdos1172PosetCompletion.condition r ≤
          (Erdos1172CohenIteration.bitValue omegaOne
              (check ((PSet.ordinalMk κ.ord).Func (j x))) (1 : bSet (FirstAlgebra κ)) ⊓
            firstStageHom κ (b x)) ⊔
          ((Erdos1172CohenIteration.bitValue omegaOne
              (check ((PSet.ordinalMk κ.ord).Func (j x))) (1 : bSet (FirstAlgebra κ)))ᶜ ⊓
            (firstStageHom κ (b x))ᶜ) := by
  obtain ⟨i, s, Hsp, Hbound⟩ := exists_ground_bound_refinement κ Hκ Hunc p
  obtain ⟨j, Hj, HC, Hcount, Hjfresh⟩ := exists_small_fresh_checked_coordinates κ Hκ Hunc I HI i
  have Hfresh (x : I) : s.value ≤
      (check ((freshCoordinateSet j).Func x) ∈ᴮ
        graphDomain omegaOne two (Erdos1172BooleanNameIteration.name s))ᶜ := by
    rw [← imp_bot, ← deduction]
    have Hmem : s.value ⊓ check ((freshCoordinateSet j).Func x) ∈ᴮ
        graphDomain omegaOne two (Erdos1172BooleanNameIteration.name s) ≤
        check ((freshCoordinateSet j).Func x) ∈ᴮ check (PSet.ordinalMk i.toOrd.val) :=
      mem_of_mem_subset (inf_le_left.trans Hbound) inf_le_right
    exact bv_absurd _ Hmem (le_top.trans (Hjfresh x))
  have Hs : s.value ≤ ErdosCohen.condition omegaOne
      (Erdos1172BooleanNameIteration.name s) :=
    ErdosCohen.mem_conditions_iff.mp (Erdos1172BooleanNameIteration.name_mem s)
  obtain ⟨q, Hq, Hsub, Hbits⟩ :=
    ErdosCohen.exists_indexed_binary_assignment (freshCoordinateSet j) b
      (freshCoordinateSet_separated Hj) omegaOne_property Hs
      (le_top.trans HC) (le_top.trans Hcount) Hfresh
  obtain ⟨r, Hrs, Hrvalue, Heq⟩ :=
    Erdos1172BooleanNameIteration.exists_extension_refinement s s.nonzero le_rfl
      (ErdosCohen.mem_conditions_iff.mpr Hq) Hsub
  refine ⟨r, Hrs.trans Hsp, j, Hj, ?_⟩
  intro x
  have H1 : r.value ⊓ b x ≤
      pair (check ((freshCoordinateSet j).Func x)) (1 : bSet (FirstAlgebra κ)) ∈ᴮ
        Erdos1172BooleanNameIteration.name r :=
    mem_congr bv_refl (inf_le_left.trans Heq)
      ((le_inf (inf_le_left.trans Hrvalue) inf_le_right).trans (Hbits x).1)
  have H0 : r.value ⊓ (b x)ᶜ ≤
      pair (check ((freshCoordinateSet j).Func x)) (0 : bSet (FirstAlgebra κ)) ∈ᴮ
        Erdos1172BooleanNameIteration.name r :=
    mem_congr bv_refl (inf_le_left.trans Heq)
      ((le_inf (inf_le_left.trans Hrvalue) inf_le_right).trans (Hbits x).2)
  exact Erdos1172CohenIteration.condition_binary_agreement H1 H0

end Erdos1172LevyCohen
