/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyStageCover
public import Erdos1172.Part4ShioyaReindexing
public import Erdos1172.Part4ShioyaLevyBoundedReading

@[expose] public section

/-! # Boolean transport from the ordinal-coded stages to the full Lévy completion -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}} {P Q : Type u} [PartialOrder P] [PartialOrder Q]

private theorem iso_symm_pullback (κ : Cardinal.{u}) (e : P ≃o Q) (b : Completion P) :
    (PartialProjection.isoProjection (κ := κ) e).booleanHom
      ((PartialProjection.isoProjection (κ := κ) e.symm).booleanHom b) = b := by
  apply eq_of_condition_tests
  intro p
  rw [PartialProjection.iso_condition,PartialProjection.iso_condition,e.symm_apply_apply]

private theorem iso_pullback_cone (κ : Cardinal.{u}) (e : P ≃o Q) (q : Q) :
    (PartialProjection.isoProjection (κ := κ) e).booleanHom (condition q) = condition (e.symm q) := by
  let φ := (PartialProjection.isoProjection (κ := κ) e).booleanHom
  have h : condition q ≤ (PartialProjection.isoProjection (κ := κ) e.symm).booleanHom (condition (e.symm q)) :=
    (PartialProjection.iso_condition (κ := κ) e.symm q _).mpr le_rfl
  apply le_antisymm ((OrderHomClass.mono φ h).trans_eq (iso_symm_pullback κ e _))
  apply (PartialProjection.iso_condition (κ := κ) e (e.symm q) _).mpr
  rw [e.apply_symm_apply]

variable (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)

def stageToFull (i : Index θ) : CompleteLatticeHom (stageBase hκ hκθ hθ i).Algebra (Completion (Full κ θ)) :=
  (fullProjection hκ.aleph0_le i).booleanHom.comp
    (PartialProjection.isoProjection (κ := κ) (stageIso hκ hκθ hθ i).symm).booleanHom

theorem stageToFull_injective (i : Index θ) : Function.Injective (stageToFull hκ hκθ hθ i) :=
  (fullProjection hκ.aleph0_le i).booleanHom_injective.comp
    (PartialProjection.isoProjection (κ := κ) (stageIso hκ hκθ hθ i).symm).booleanHom_injective

theorem stageToFull_test (i : Index θ) (p : Full κ θ) (b : (stageBase hκ hκθ hθ i).Algebra) :
    condition p ≤ stageToFull hκ hκθ hθ i b ↔
      condition ((stageIso hκ hκθ hθ i).symm (cut hκ.pos (Set.Iio i) p)) ≤ b :=
  ((fullProjection hκ.aleph0_le i).dom_condition ⟨p,Set.mem_univ _⟩ _).trans
    (PartialProjection.iso_condition (κ := κ) (stageIso hκ hκθ hθ i).symm _ b)

theorem stageToFull_condition (i : Index θ) (q : (stageBase hκ hκθ hθ i).Poset) :
    stageToFull hκ hκθ hθ i (condition q) = condition (extendStage (stageIso hκ hκθ hθ i q)) := by
  change (fullProjection hκ.aleph0_le i).booleanHom
    ((PartialProjection.isoProjection (κ := κ) (stageIso hκ hκθ hθ i).symm).booleanHom (condition q)) = _
  rw [iso_pullback_cone, fullProjection_condition]
  rfl

theorem stageToFull_restrict {i j : Index θ} (hij : i ≤ j) (b : (stageBase hκ hκθ hθ i).Algebra) :
    stageToFull hκ hκθ hθ j ((codedRestriction hκ hκθ hθ hij).booleanHom b) = stageToFull hκ hκθ hθ i b := by
  apply eq_of_condition_tests
  intro p
  rw [stageToFull_test,codedRestriction_condition,stageToFull_test,OrderIso.apply_symm_apply,
    cut_cut hκ.pos (Set.Iio_subset_Iio hij)]

theorem coded_bounded_reading_with_point {I : Type u} (hI : Cardinal.mk I < θ)
    (f : I → Completion (Full κ θ)) (old : Index θ) (p : Full κ θ) :
    ∃ j : Index θ, old ≤ j ∧ ∃ q : (stageBase hκ hκθ hθ j).Poset,
      stageToFull hκ hκθ hθ j (condition q) = condition p ∧
      ∃ g : I → (stageBase hκ hκθ hθ j).Algebra, ∀ a, stageToFull hκ hκθ hθ j (g a) = f a := by
  obtain ⟨j,hj,q,hq,g,hg⟩ := bounded_reading_with_point hθ hκθ hκ.aleph0_le hI f old p
  let e := stageIso hκ hκθ hθ j
  refine ⟨j,hj,e.symm q,?_,fun a => (PartialProjection.isoProjection (κ := κ) e).booleanHom (g a),?_⟩
  · rw [stageToFull_condition]
    change condition (extendStage (e (e.symm q))) = condition p
    rw [e.apply_symm_apply,hq]
  · intro a
    change (fullProjection hκ.aleph0_le j).booleanHom
      ((PartialProjection.isoProjection (κ := κ) e.symm).booleanHom
        ((PartialProjection.isoProjection (κ := κ) e).booleanHom (g a))) = _
    exact (congrArg (fullProjection hκ.aleph0_le j).booleanHom (iso_symm_pullback κ e.symm (g a))).trans (hg a)

end Erdos1172Shioya.LevyProduct
