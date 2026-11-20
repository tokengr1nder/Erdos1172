/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenRealReading

@[expose] public section

/-!
# The full powerset of omega in the actual internal Cohen extension

The forward inclusion of a transported powerset holds for every complete
Boolean homomorphism, by the actual coefficients of its displayed children.
The reverse inclusion here uses the proved reading cover for arbitrary
mixed real names. The equality is not inferred from general elementarity,
and no global source witness is selected.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNameTransport

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B]
variable [NontrivialCompleteBooleanAlgebra C]

/-- Every transported subset remains a subset; the converse is not
asserted for an arbitrary homomorphism. -/
theorem map_powerset_subset (e : CompleteLatticeHom B C) (X : bSet B) :
    (⊤ : C) ≤ mapNames e (bv_powerset X) ⊆ᴮ bv_powerset (mapNames e X) := by
  rw [subset_unfold]
  change (⊤ : C) ≤ ⨅ f : X.type → B,
    _root_.imp (e (set_of_indicator (u := X) f ⊆ᴮ X))
      (mapNames e (set_of_indicator (u := X) f) ∈ᴮ bv_powerset (mapNames e X))
  apply le_iInf
  intro f
  rw [← deduction]
  apply mem_powerset_iff.mpr
  exact inf_le_right.trans (map_subset e (set_of_indicator (u := X) f) X).le

end bSet.ErdosNameTransport

namespace Erdos1172CohenIteration

open bSet bSet.ErdosNameTransport

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Every arbitrary second-stage subset of omega enters the transported
first-stage powerset through the actual Boolean cover of source names. -/
theorem powerset_omega_subset_map :
    (⊤ : omegaOneAlgebra B) ≤ bv_powerset omega ⊆ᴮ
      mapNames omegaOneFirstStageHom (bv_powerset (omega : bSet B)) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hx : (⊤ : omegaOneAlgebra B) ⊓ x ∈ᴮ bv_powerset omega ≤ x ⊆ᴮ omega :=
    mem_powerset_iff.mp inf_le_right
  apply (real_reading_cover Hx).trans
  apply iSup_le
  intro y
  have Hmem : (y ⊆ᴮ (omega : bSet B)) ≤ y ∈ᴮ bv_powerset omega :=
    mem_powerset_iff.mpr le_rfl
  have Hmap : omegaOneFirstStageHom (y ⊆ᴮ (omega : bSet B)) ≤
      mapNames omegaOneFirstStageHom y ∈ᴮ
        mapNames omegaOneFirstStageHom (bv_powerset omega) := by
    rw [← map_mem]
    exact OrderHomClass.mono omegaOneFirstStageHom Hmem
  exact bv_rw' (ϕ := fun z => z ∈ᴮ
      mapNames omegaOneFirstStageHom (bv_powerset (omega : bSet B)))
    inf_le_right (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans Hmap)

/-- Equality of the actual full internal powersets, including all mixed
target subsets, proved from real-name reading rather than assumed. -/
theorem map_powerset_omega_eq :
    (⊤ : omegaOneAlgebra B) ≤
      mapNames omegaOneFirstStageHom (bv_powerset (omega : bSet B)) =ᴮ
        bv_powerset omega := by
  apply (le_inf ?_ powerset_omega_subset_map).trans (eq_of_subset_subset _ _)
  simpa only [omega, map_check] using
    (map_powerset_subset omegaOneFirstStageHom (omega : bSet B))

end Erdos1172CohenIteration
