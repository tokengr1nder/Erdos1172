/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenIterationReading

@[expose] public section

/-!
# From local readings to actual completed Boolean bounds

A locally forced graph extension gives inclusion of completed cones after
restriction to the corresponding first-stage Boolean value. The proof
uses the regular-cone membership criterion: every strengthening has a
further actual common strengthening. Distributing the complete first-stage
map over the reading cover then gives its ambient Boolean bound.

No elementarity, new-real exclusion, or cardinal preservation is assumed
or concluded here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Restricting the cone of `p` to a Boolean context where its graph
extends `s` gives a completed cone below `s`. -/
theorem condition_inf_firstStageHom_le_condition {K : bSet B}
    (p s : Conditions K) {b : B}
    (Hb : b ≤ s.value)
    (Hsub : b ≤ Erdos1172BooleanNameIteration.name s ⊆ᴮ
      Erdos1172BooleanNameIteration.name p) :
    condition p ⊓ firstStageHom K b ≤ condition s := by
  change (condition p ⊓ firstStageHom K b).val ≤ (condition s).val
  intro r Hr
  change r ∈ (condition p).val ∧ r ∈ (firstStageHom K b).val at Hr
  have Hrb : r.value ≤ b :=
    (condition_le_firstStageHom_iff K r b).mp (condition_le_iff.mpr Hr.2)
  apply (mem_condition_iff s r).mpr
  intro t Htr
  obtain ⟨v, Hvt, Hvp⟩ := (mem_condition_iff p r).mp Hr.1 t Htr
  have Hvb : v.value ≤ b := Hvt.1.trans (Htr.1.trans Hrb)
  refine ⟨v, Hvt, ?_⟩
  exact ⟨Hvb.trans Hb, subset_trans' (Hvb.trans Hsub) Hvp.2⟩

/-- A reading of a condition's actual name implies the read value in the
completed iteration, after intersection with that condition's cone. -/
theorem condition_inf_firstStageHom_reads_le {K : bSet B}
    (p : Conditions K) (c : Algebra K) :
    condition p ⊓ firstStageHom K
      (reads c (Erdos1172BooleanNameIteration.name p)) ≤ c := by
  unfold reads
  rw [map_iSup]
  erw [inf_iSup_eq]
  apply iSup_le
  intro s
  exact (condition_inf_firstStageHom_le_condition p s.val inf_le_left
    (subset_of_eq (bv_symm inf_le_right))).trans s.property

end Erdos1172CohenIteration
