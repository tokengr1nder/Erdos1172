/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyChainCondition
public import Erdos1172.Part4ShioyaLevyRestrictions
public import Erdos1172.Part4CompletionAntichainRepresentation

@[expose] public section

/-! # Simultaneous bounded-stage reading of Boolean values in the Lévy product -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}}

private theorem cone_le_cone {P : Type u} [PartialOrder P] (h : Separative P) (p q : P) :
    condition p ≤ condition q ↔ p ≤ q := by
  refine ⟨fun hcone => ?_, fun hp => condition_mono hp⟩
  by_contra hn
  obtain ⟨r,hr,hin⟩ := h p q hn
  exact hin ((mem_condition_iff q p).mp (condition_le_iff.mp hcone) r hr)

theorem cut_le_iff_le_extendStage (hκ : 0 < κ) (i : Index θ) (q : Full κ θ) (p : Stage κ i) :
    cut hκ (Set.Iio i) q ≤ p ↔ q ≤ extendStage p := by
  constructor
  · intro h j
    change q.value j ≤ p.value j
    by_cases hj : j < i
    · simpa only [cut_at hκ _ (show j ∈ Set.Iio i from hj)] using h j
    · rw [value_outside p (i := j) hj hκ]
      exact Collapse.le_empty _ _
  · intro h j
    by_cases hj : j < i
    · rw [cut_at hκ _ (show j ∈ Set.Iio i from hj)]
      exact h j
    · rw [cut_not_at hκ _ (show j ∉ Set.Iio i from hj),value_outside p (i := j) hj hκ]

theorem fullProjection_condition (hκ : Cardinal.aleph0 ≤ κ) (i : Index θ) (p : Stage κ i) :
    (fullProjection hκ i).booleanHom (condition p) = condition (extendStage p) := by
  have h (q : Full κ θ) : condition q ≤ (fullProjection hκ i).booleanHom (condition p) ↔
      condition q ≤ condition (extendStage p) := by
    rw [(fullProjection hκ i).dom_condition ⟨q,Set.mem_univ _⟩, fullProjection_apply,
      cone_le_cone (stage_separative hκ i),cut_le_iff_le_extendStage,cone_le_cone (full_separative hκ)]
  have hd (p : Full κ θ) : ∃ q ∈ (Set.univ : Set (Full κ θ)), q ≤ p := ⟨p, Set.mem_univ _,le_rfl⟩
  exact le_antisymm (le_of_dense_conditions_le Set.univ hd (fun q => (h q.val).mp))
    (le_of_dense_conditions_le Set.univ hd (fun q => (h q.val).mpr))

theorem family_full_support_bounded (hθ : θ.IsRegular) (hκθ : κ ≤ θ) {I : Type u}
    (hI : Cardinal.mk I < θ) (f : I → Full κ θ) :
    ∃ j : Index θ, ∀ a, support (f a).value ⊆ Set.Iio j := by
  choose k hk using fun a => full_support_bounded hθ hκθ (f a)
  have hn : ¬IsCofinal (Set.range k) := by
    intro h
    have hc := Order.cof_le h
    rw [show Order.cof (Index θ) = θ from (Ordinal.cof_toType θ.ord).trans hθ.cof_ord] at hc
    exact (Cardinal.mk_range_le.trans_lt hI).not_ge hc
  obtain ⟨j,hj⟩ : ∃ j, ∀ a, k a < j := by
    by_contra! hc
    apply hn
    intro j
    obtain ⟨a, h⟩ := hc j
    exact ⟨k a,Set.mem_range_self a,h⟩
  exact ⟨j, fun a => (hk a).trans (Set.Iio_subset_Iio (hj a).le)⟩

theorem bounded_reading (hθ : θ.IsInaccessible) (hκθ : κ < θ) (hκ : Cardinal.aleph0 ≤ κ)
    {I : Type u} (hI : Cardinal.mk I < θ) (f : I → Completion (Full κ θ)) :
    ∃ i : Index θ, ∃ g : I → Completion (Stage κ i), ∀ a,
      (fullProjection hκ i).booleanHom (g a) = f a := by
  choose A hA _ he using fun a => exists_small_condition_antichain_sup θ
    (fun b hp hd => full_completion_disjoint_family_cardinal_lt hθ hκθ hκ b hp hd) (f a)
  let J := Σ a : I, A a
  have hJ : Cardinal.mk J < θ := by
    rw [show Cardinal.mk J = _ from Cardinal.mk_sigma (fun a => ↥(A a))]
    exact Cardinal.sum_lt_of_isRegular hθ.isRegular hI hA
  let point (z : J) := z.2.val
  obtain ⟨i,hi⟩ := family_full_support_bounded hθ.isRegular hκθ.le hJ point
  let r (z : J) : Stage κ i := ⟨(point z).value,(point z).small,hi z⟩
  have hr (z : J) : extendStage (r z) = point z := value_injective rfl
  refine ⟨i,fun a => ⨆ p : A a, condition (r ⟨a,p⟩),fun a => ?_⟩
  rw [map_iSup]
  exact (iSup_congr (fun p => (fullProjection_condition hκ i _).trans (congrArg condition (hr ⟨a,p⟩)))).trans (he a)

theorem bounded_reading_with_point (hθ : θ.IsInaccessible) (hκθ : κ < θ) (hκ : Cardinal.aleph0 ≤ κ)
    {I : Type u} (hI : Cardinal.mk I < θ) (f : I → Completion (Full κ θ))
    (old : Index θ) (p : Full κ θ) :
    ∃ j : Index θ, old ≤ j ∧ ∃ q : Stage κ j, extendStage q = p ∧
      ∃ g : I → Completion (Stage κ j), ∀ a, (fullProjection hκ j).booleanHom (g a) = f a := by
  obtain ⟨i,g,hg⟩ := bounded_reading hθ hκθ hκ hI f
  obtain ⟨m,hm⟩ := full_support_bounded hθ.isRegular hκθ.le p
  let j := max (max old m) i
  have hij : i ≤ j := le_max_right _ _
  have hmj : m ≤ j := (le_max_right old m).trans (le_max_left _ _)
  let q : Stage κ j := ⟨p.value,p.small,hm.trans (Set.Iio_subset_Iio hmj)⟩
  refine ⟨j,(le_max_left old m).trans (le_max_left _ _),q,value_injective rfl,
    fun a => (stageProjection hκ hij).booleanHom (g a),fun a => ?_⟩
  exact (DFunLike.congr_fun (fullProjection_booleanHom_comp hκ hij) (g a)).trans (hg a)

end Erdos1172Shioya.LevyProduct
