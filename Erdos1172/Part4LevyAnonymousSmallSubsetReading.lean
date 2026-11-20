/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenSmallBinaryCoding
public import Erdos1172.Part4BooleanCheckedIndicatorAgreement
public import Erdos1172.Part4LevyAnonymousCollapse

@[expose] public section

/-!
# Actual anonymous recovery of small checked-ground subsets

Every source subset of a ground set with fewer than kappa labels is
locally coded by fresh Cohen coordinates. Their actual one-bit values
belong to the anonymous complete algebra, so they define an actual name
over that algebra with the original checked children.

Local binary agreement of membership coefficients identifies the whole
transported mixed subset with that anonymous name. The final cover retains
the original transported source-validity guard. No separated-label,
external countability, global validity, one global representative, GCH,
anonymous distributivity, or ideal hypothesis is supplied.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport ErdosCheckedIndicator
open Erdos1172CohenIteration Erdos1172CompleteSubalgebra Erdos1172PosetCompletion

/-- The original checked ground children with actual anonymous bit
coefficients. Labels of `A` need not be extensionally separated. -/
def anonymousSmallSubset (κ : Cardinal.{u}) (A : PSet.{u})
    (j : A.Type → (PSet.ordinalMk κ.ord).Type) : bSet (anonymousAlgebra κ) :=
  checkedIndicator A (fun i =>
    ⟨bitValue (ErdosOmegaTwo.omegaOne : bSet (FirstAlgebra κ))
      (check ((PSet.ordinalMk κ.ord).Func (j i))) (1 : bSet (FirstAlgebra κ)),
      bitValue_mem_anonymousAlgebra κ (j i)⟩)

theorem anonymousSmallSubset_subset (κ : Cardinal.{u}) (A : PSet.{u})
    (j : A.Type → (PSet.ordinalMk κ.ord).Type) :
    (⊤ : anonymousAlgebra κ) ≤ anonymousSmallSubset κ A j ⊆ᴮ check A :=
  checkedIndicator_subset A _

/-- Literal hereditary name transport, not merely local forcing equality. -/
theorem map_anonymousSmallSubset (κ : Cardinal.{u}) (A : PSet.{u})
    (j : A.Type → (PSet.ordinalMk κ.ord).Type) :
    mapNames (inclusion (anonymousAlgebra κ)) (anonymousSmallSubset κ A j) =
      checkedIndicator A (fun i =>
        bitValue (ErdosOmegaTwo.omegaOne : bSet (FirstAlgebra κ))
          (check ((PSet.ordinalMk κ.ord).Func (j i))) (1 : bSet (FirstAlgebra κ))) :=
  map_checkedIndicator (inclusion (anonymousAlgebra κ)) A _

/-- Below a cone where the transported subset is valid, actual fresh-bit
coding produces one stronger cone and an actual anonymous subset name. -/
theorem exists_anonymous_small_subset_extension (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (A : PSet.{u}) (HA : Cardinal.mk A.Type < κ)
    (p : Conditions (ErdosOmegaTwo.omegaOne : bSet (FirstAlgebra κ)))
    (x : bSet (FirstAlgebra κ))
    (Hx : condition p ≤ firstStageHom κ (x ⊆ᴮ check A)) :
    ∃ r : Conditions (ErdosOmegaTwo.omegaOne : bSet (FirstAlgebra κ)),
      r ≤ p ∧ ∃ j : A.Type → (PSet.ordinalMk κ.ord).Type,
        Function.Injective j ∧
        condition r ≤ mapNames (firstStageHom κ) x =ᴮ
          mapNames (inclusion (anonymousAlgebra κ)) (anonymousSmallSubset κ A j) := by
  obtain ⟨r, Hrp, j, Hj, Hcode⟩ := exists_small_binary_coding_extension
    κ Hκ Hunc A.Type HA p (fun i => check (A.Func i) ∈ᴮ x)
  refine ⟨r, Hrp, j, Hj, ?_⟩
  have Hsubset : condition r ≤ mapNames (firstStageHom κ) x ⊆ᴮ check A := by
    have H := (condition_mono Hrp).trans Hx
    rwa [map_subset, map_check] at H
  rw [map_anonymousSmallSubset]
  apply eq_checkedIndicator_of_binary_agreement A Hsubset
  intro i
  have Hmember : firstStageHom κ ((check (A.Func i) : bSet (FirstAlgebra κ)) ∈ᴮ x) =
      (check (A.Func i) : bSet (Algebra κ)) ∈ᴮ mapNames (firstStageHom κ) x := by
    rw [map_mem, map_check]
  rw [← Hmember]
  erw [inf_comm (firstStageHom κ (check (A.Func i) ∈ᴮ x)),
    inf_comm ((firstStageHom κ (check (A.Func i) ∈ᴮ x))ᶜ)]
  exact Hcode i

/-- Every arbitrary source mixed subset of a small checked ground family
is covered by actual anonymous names at its original validity guard. The
ground labels may repeat, and no single global representative is selected. -/
theorem firstStage_small_subset_anonymous_cover (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (A : PSet.{u}) (HA : Cardinal.mk A.Type < κ)
    (x : bSet (FirstAlgebra κ)) :
    firstStageHom κ (x ⊆ᴮ check A) ≤ ⨆ y : bSet (anonymousAlgebra κ),
      inclusion (anonymousAlgebra κ) (y ⊆ᴮ check A) ⊓
        (mapNames (firstStageHom κ) x =ᴮ mapNames (inclusion (anonymousAlgebra κ)) y) := by
  classical
  let V : Algebra κ := ⨆ y : bSet (anonymousAlgebra κ),
    inclusion (anonymousAlgebra κ) (y ⊆ᴮ check A) ⊓
      (mapNames (firstStageHom κ) x =ᴮ mapNames (inclusion (anonymousAlgebra κ)) y)
  change firstStageHom κ (x ⊆ᴮ check A) ≤ V
  by_contra Hnot
  have Hpositive : firstStageHom κ (x ⊆ᴮ check A) ⊓ Vᶜ ≠ ⊥ := by
    intro Hzero
    apply Hnot
    have H : firstStageHom κ (x ⊆ᴮ check A) ≤ (Vᶜ)ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr Hzero.le)
    simpa only [compl_compl] using H
  obtain ⟨p, Hp⟩ := exists_condition_le Hpositive
  obtain ⟨r, Hrp, j, _Hj, Heq⟩ :=
    exists_anonymous_small_subset_extension κ Hκ Hunc A HA p x (Hp.trans inf_le_left)
  have HrV : condition r ≤ V := by
    apply le_iSup_of_le (anonymousSmallSubset κ A j)
    refine le_inf ?_ Heq
    rw [top_unique (anonymousSmallSubset_subset κ A j), map_top]
    exact le_top
  have HrnotV : condition r ≤ Vᶜ := (condition_mono Hrp).trans (Hp.trans inf_le_right)
  exact condition_ne_bot r (bot_unique ((le_inf HrV HrnotV).trans inf_compl_eq_bot.le))

end Erdos1172LevyCohen
