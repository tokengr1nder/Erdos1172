/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaStageCover
public import Erdos1172.Part4ShioyaLevyRestrictions
public import Erdos1172.Part4ShioyaCoverPreservation

@[expose] public section

/-! # The dual Shioya forcing as an image of the Lévy stage forcing -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}}
variable (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)

include hκ hκθ hθ in
theorem presentationWitness (i : Index θ) :
    ∃ A : Presentation θ, Nonempty (A.Carrier ≃o Stage κ i) :=
  exists_small_presentation (Stage κ i) (stage_cardinal_lt hθ hκθ hκ.pos i)

def stageBase (i : Index θ) : Condition κ θ := by
  let A := (presentationWitness hκ hκθ hθ i).choose
  let e := (presentationWitness hκ hκθ hθ i).choose_spec.some
  exact ⟨A, separative_of_iso e (stage_separative hκ.aleph0_le i), shortInfima_of_iso e (shortInfima hκ),
    e.symm (empty hκ.pos), i, fun _ => ⊥⟩

def stageIso (i : Index θ) : (stageBase hκ hκθ hθ i).Poset ≃o Stage κ i :=
  (presentationWitness hκ hκθ hθ i).choose_spec.some

def productIso {A B C D : Type u} [PartialOrder A] [PartialOrder B] [PartialOrder C]
    [PartialOrder D] (e : A ≃o B) (f : C ≃o D) : A × C ≃o B × D where
  toEquiv := e.toEquiv.prodCongr f.toEquiv
  map_rel_iff' := and_congr e.le_iff_le f.le_iff_le

def codedRestriction {i j : Index θ} (h : i ≤ j) :
    PartialProjection κ (stageBase hκ hκθ hθ j).Poset (stageBase hκ hκθ hθ i).Poset :=
  productProjection (((stageIso hκ hκθ hθ j).trans (split hκ.aleph0_le (Set.Iio_subset_Iio h))).trans
    (productIso (stageIso hκ hκθ hθ i).symm (OrderIso.refl _))) (empty hκ.pos)

theorem codedRestriction_condition {i j : Index θ} (h : i ≤ j) (p : (stageBase hκ hκθ hθ j).Poset)
    (b : (stageBase hκ hκθ hθ i).Algebra) :
    condition p ≤ (codedRestriction hκ hκθ hθ h).booleanHom b ↔
      condition ((stageIso hκ hκθ hθ i).symm (cut hκ.pos (Set.Iio i) (stageIso hκ hκθ hθ j p))) ≤ b :=
  (codedRestriction hκ hκθ hθ h).dom_condition ⟨p, Set.mem_univ _⟩ b

theorem eq_of_condition_tests {P : Type u} [Preorder P] {b c : Completion P}
    (h : ∀ p : P, condition p ≤ b ↔ condition p ≤ c) : b = c := by
  have hd (p : P) : ∃ q ∈ (Set.univ : Set P), q ≤ p := ⟨p, Set.mem_univ _, le_rfl⟩
  exact le_antisymm (le_of_dense_conditions_le Set.univ hd (fun p => (h p.val).mp))
    (le_of_dense_conditions_le Set.univ hd (fun p => (h p.val).mpr))

theorem cut_self_stage (i : Index θ) (p : Stage κ i) :
    cut hκ.pos (Set.Iio i) p = p := by
  apply value_injective
  funext t
  by_cases ht : t ∈ Set.Iio i
  · exact cut_at hκ.pos p ht
  · exact (cut_not_at hκ.pos p ht).trans (value_outside p ht hκ.pos).symm

def stageSystem : StageSystem κ θ (Index θ) where
  base := stageBase hκ hκθ hθ
  restrict := codedRestriction hκ hκθ hθ
  restrict_id i := by
    ext b
    apply eq_of_condition_tests
    intro p
    rw [codedRestriction_condition, cut_self_stage hκ, OrderIso.symm_apply_apply]
    rfl
  restrict_comp {i j k} h g := by
    ext b
    apply eq_of_condition_tests
    intro p
    simp only [CompleteLatticeHom.comp_apply, codedRestriction_condition, OrderIso.apply_symm_apply,
      cut_cut hκ.pos (Set.Iio_subset_Iio h)]

private theorem large_coordinate (hθ : θ.IsInaccessible) (i : Index θ) (μ : Cardinal.{u}) (hμ : μ < θ) :
    ∃ t j : Index θ, i ≤ t ∧ t < j ∧ μ ≤ Cardinal.mk (Alphabet t) := by
  let ν := max Cardinal.aleph0 μ
  let Y := ν.ord.ToType
  have he : Cardinal.mk Y = ν := Cardinal.mk_ord_toType _
  let _ : Nontrivial Y := Cardinal.one_lt_iff_nontrivial.mp (he.symm ▸
    Cardinal.one_lt_aleph0.trans_le (le_max_left _ μ))
  obtain ⟨t,j,hit,htj,f,hf⟩ := exists_coordinate_surjection hθ i Y
    (he.trans_lt (max_lt hθ.aleph0_lt hμ))
  exact ⟨t,j,hit,htj,(le_max_right Cardinal.aleph0 μ).trans
    (he.symm.le.trans (Cardinal.mk_le_of_surjective hf))⟩

theorem stageSystem_hasCollapseFactors : (stageSystem hκ hκθ hθ).HasCollapseFactors := by
  intro i μ hμ
  obtain ⟨t, j, hi, hj, ht⟩ := large_coordinate hθ i μ hμ
  let E := ((stageIso hκ hκθ hθ j).trans (stageSplit hκ.aleph0_le hi hj)).trans
    (productIso (productIso (stageIso hκ hκθ hθ i).symm (OrderIso.refl _)) (OrderIso.refl _))
  let F := productProjection (κ := κ) E (empty hκ.pos)
  let c := Collapse.empty (α := Alphabet t) hκ.pos
  let G := productProjection (κ := κ) (OrderIso.refl ((stageBase hκ hκθ hθ i).Poset ×
    Collapse.Condition κ (Alphabet t))) c
  refine ⟨j, hi.trans hj.le, Alphabet t, ht, c, F, ?_⟩
  ext b
  apply eq_of_condition_tests
  intro p
  have hf := F.dom_condition ⟨p, Set.mem_univ _⟩ (G.booleanHom b)
  have hg := G.dom_condition ⟨(E p).1, Set.mem_univ _⟩ b
  exact (codedRestriction_condition hκ hκθ hθ (hi.trans hj.le) p b).trans (hf.trans hg).symm

variable [Fact (Cardinal.aleph0 < κ)]

theorem stage_forget_lifts : ForcingCover.Lifts (stageSystem hκ hκθ hθ).forgetMap :=
  (stageSystem hκ hκθ hθ).forget_lifts (stageSystem_hasCollapseFactors hκ hκθ hθ) hκ

theorem stage_forget_reaches (q : Condition κ θ) :
    ∃ a, (stageSystem hκ hκθ hθ).forgetMap a ≤ q := by
  let _ : Nonempty (Index θ) := ⟨q.length⟩
  exact (stageSystem hκ hκθ hθ).forget_reaches (stageSystem_hasCollapseFactors hκ hκθ hθ) hκ q

def stageCoverHom := ForcingCover.booleanHom (stageSystem hκ hκθ hθ).forgetMap
  (stage_forget_lifts hκ hκθ hθ)

theorem stageCoverHom_injective : Function.Injective (stageCoverHom hκ hκθ hθ) :=
  ForcingCover.booleanHom_injective _ (stage_forget_lifts hκ hκθ hθ) (stage_forget_reaches hκ hκθ hθ)

end Erdos1172Shioya.LevyProduct
