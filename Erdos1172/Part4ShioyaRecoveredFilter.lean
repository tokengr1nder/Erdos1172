/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaFreezing
public import Erdos1172.Part4ShioyaGenericString

@[expose] public section

/-! # The presentation filter recovered from a coded Shioya string

For a densely coded presentation, changing only its point embeds its
compatibility relation into the Shioya forcing. The associated name is
upward closed and directed and meets every ground set dense below the
original point. This gives the strong coding case of Lemma 32 of Eskew
and Hayut, *Dense ideals*, locally at an arbitrary starting point.
-/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion
open scoped Flypitch
universe u

namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)]

theorem cone_le_of_refinements {P : Type u} [Preorder P] (p : P) (b : Completion P)
    (h : ∀ r ≤ p, ∃ s ≤ r, condition s ≤ b) : condition p ≤ b := by
  apply condition_le_iff.mpr
  rw [← b.prop.eq]
  apply (mem_regularization_iff b.val p).mpr
  intro r hr
  obtain ⟨s, hsr, hs⟩ := h r hr
  exact ⟨s, hsr, condition_le_iff.mp hs⟩

namespace Condition

theorem withPoint_mono (v : Condition κ θ) {a b : v.Poset} (hab : a ≤ b) :
    v.withPoint a ≤ v.withPoint b := (v.withPoint b).withPoint_le hab

theorem withPoint_dense_below (v : Condition κ θ) (D : Set v.Poset)
    (hd : ∀ p ≤ v.point, ∃ d ∈ D, d ≤ p) {w : Condition κ θ} (hw : w ≤ v) :
    ∃ r : w.Poset, r ≤ w.point ∧ ∃ d ∈ D, w.withPoint r ≤ v.withPoint d := by
  obtain ⟨π, hp, he⟩ := hw
  obtain ⟨x, hx⟩ := π.dense w.point
  have hxv : π.proj x ≤ v.point :=
    (separative_condition_le_iff v.separative _ _).mp ((π.dom_condition x _).mp ((condition_mono hx).trans hp))
  obtain ⟨d, hdD, hdx⟩ := hd _ hxv
  obtain ⟨y, hyx, hyd⟩ := π.lifts x d hdx
  have hyr : y.val ≤ w.point := (show y.val ≤ x.val from hyx).trans hx
  refine ⟨y.val, hyr, d, hdD, π, ?_, ?_⟩
  · exact (π.dom_condition y _).mpr (condition_mono hyd)
  · exact (condition_mono hyr).trans he

theorem withPoint_predense (v : Condition κ θ) (D : Set v.Poset)
    (hd : ∀ p ≤ v.point, ∃ d ∈ D, d ≤ p) :
    condition v ≤ ⨆ d : D, condition (v.withPoint d.val) := by
  apply cone_le_of_refinements
  intro w hw
  obtain ⟨r, hr, d, hdD, hwd⟩ := v.withPoint_dense_below D hd hw
  exact ⟨w.withPoint r, w.withPoint_le hr, le_iSup_of_le ⟨d, hdD⟩ (condition_mono hwd)⟩

theorem CodesDense.common_point {v w : Condition κ θ} (hc : v.CodesDense) (a b : v.Poset)
    (ha : w ≤ v.withPoint a) (hb : w ≤ v.withPoint b) :
    ∃ r : w.Poset, r ≤ w.point ∧ ∃ c : v.Poset, c ≤ a ∧ c ≤ b ∧ w.withPoint r ≤ v.withPoint c := by
  change ∃ π : PartialProjection κ w.Poset v.Poset, condition w.point ≤ π.booleanHom (condition a) ∧
    condition w.point ≤ extensionValue π.booleanHom v.name w.name at ha
  change ∃ σ : PartialProjection κ w.Poset v.Poset, condition w.point ≤ σ.booleanHom (condition b) ∧
    condition w.point ≤ extensionValue σ.booleanHom v.name w.name at hb
  obtain ⟨π, hpa, hπ⟩ := ha
  obtain ⟨σ, hsb, hσ⟩ := hb
  have he := hc.freeze_booleanHom π σ hπ hσ (condition b)
  have hpb := (le_inf (le_refl (condition w.point)) hsb).trans (he.ge.trans inf_le_right)
  obtain ⟨x, hx⟩ := π.dense w.point
  have hp := condition_mono hx
  refine ⟨x.val, hx, π.proj x, ?_, ?_, π, (π.dom_condition x _).mpr le_rfl, hp.trans hπ⟩
  · exact (separative_condition_le_iff v.separative _ _).mp ((π.dom_condition x _).mp (hp.trans hpa))
  · exact (separative_condition_le_iff v.separative _ _).mp ((π.dom_condition x _).mp (hp.trans hpb))

theorem CodesDense.compatible_iff {v : Condition κ θ} (hc : v.CodesDense) (a b : v.Poset) :
    (∃ w : Condition κ θ, w ≤ v.withPoint a ∧ w ≤ v.withPoint b) ↔ ∃ c : v.Poset, c ≤ a ∧ c ≤ b := by
  constructor
  · rintro ⟨w, ha, hb⟩
    obtain ⟨_, _, c, hca, hcb, _⟩ := hc.common_point a b ha hb
    exact ⟨c, hca, hcb⟩
  · rintro ⟨c, hca, hcb⟩
    exact ⟨v.withPoint c, v.withPoint_mono hca, v.withPoint_mono hcb⟩

theorem CodesDense.cones_directed {v : Condition κ θ} (hc : v.CodesDense) (a b : v.Poset) :
    condition (v.withPoint a) ⊓ condition (v.withPoint b) =
      ⨆ c : {c : v.Poset // c ≤ a ∧ c ≤ b}, condition (v.withPoint c.val) := by
  apply le_antisymm _ (iSup_le fun c => le_inf (condition_mono (v.withPoint_mono c.property.1))
    (condition_mono (v.withPoint_mono c.property.2)))
  apply le_of_dense_conditions_le Set.univ (fun p => ⟨p, Set.mem_univ _, le_rfl⟩)
  intro p hp
  apply cone_le_of_refinements
  intro r hr
  obtain ⟨s, hsr, hsa⟩ := (mem_condition_iff (v.withPoint a) p.val).mp
    (condition_le_iff.mp (hp.trans inf_le_left)) r hr
  obtain ⟨w, hws, hwb⟩ := (mem_condition_iff (v.withPoint b) p.val).mp
    (condition_le_iff.mp (hp.trans inf_le_right)) s (hsr.trans hr)
  obtain ⟨z, hzw, c, hca, hcb, hzc⟩ := hc.common_point a b (hws.trans hsa) hwb
  exact ⟨w.withPoint z, (w.withPoint_le hzw).trans (hws.trans hsr),
    le_iSup_of_le ⟨c, hca, hcb⟩ (condition_mono hzc)⟩

end Condition

variable [Nonempty (Condition κ θ)] (v : Condition κ θ)

def recoveredFilter : bSet (Algebra κ θ) :=
  .mk v.Poset (fun p => StringName.label (γ := v.presentation.index.toOrd.val) p) (fun p => condition (v.withPoint p))

theorem recoveredFilter_mem (p : v.Poset) :
    (StringName.label (γ := v.presentation.index.toOrd.val) p ∈ᴮ recoveredFilter v) = condition (v.withPoint p) := by
  apply le_antisymm _ (mem_mk' (recoveredFilter v) p)
  rw [mem_unfold]
  apply iSup_le
  intro q
  change v.Poset at q
  change condition (v.withPoint q) ⊓ (StringName.label (γ := v.presentation.index.toOrd.val) p =ᴮ
    StringName.label (γ := v.presentation.index.toOrd.val) q) ≤ condition (v.withPoint p)
  by_cases h : p = q
  · subst q
    exact inf_le_left
  · have hne : ¬ PSet.Equiv (PSet.ordinalMk (Ordinal.ToType.toOrd (o := v.presentation.index.toOrd.val) p).val)
        (PSet.ordinalMk (Ordinal.ToType.toOrd (o := v.presentation.index.toOrd.val) q).val) :=
      fun he => h (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv he)))
    exact (inf_le_right.trans_eq (check_bv_eq_bot_of_not_equiv hne)).trans bot_le

theorem recoveredFilter_point :
    condition v ≤ StringName.label (γ := v.presentation.index.toOrd.val) v.point ∈ᴮ recoveredFilter v := by
  rw [recoveredFilter_mem]
  exact le_rfl

theorem recoveredFilter_subset :
    (⊤ : Algebra κ θ) ≤ recoveredFilter v ⊆ᴮ check (PSet.ordinalMk v.presentation.index.toOrd.val) := by
  rw [subset_unfold]
  apply le_iInf
  intro x
  change v.Poset at x
  rw [← deduction]
  exact le_top.trans (check_mem (PSet.mk_mem_mk_of_lt
    (Ordinal.ToType.toOrd (o := v.presentation.index.toOrd.val) x).property))

theorem recoveredFilter_upward (p q : v.Poset) (hpq : p ≤ q) :
    (StringName.label (γ := v.presentation.index.toOrd.val) p ∈ᴮ recoveredFilter v) ≤
      StringName.label (γ := v.presentation.index.toOrd.val) q ∈ᴮ recoveredFilter v := by
  rw [recoveredFilter_mem, recoveredFilter_mem]
  exact condition_mono (v.withPoint_mono hpq)

theorem recoveredFilter_directed (hc : v.CodesDense) (a b : v.Poset) :
    ((StringName.label (γ := v.presentation.index.toOrd.val) a ∈ᴮ recoveredFilter v) ⊓
      (StringName.label (γ := v.presentation.index.toOrd.val) b ∈ᴮ recoveredFilter v)) =
    ⨆ c : {c : v.Poset // c ≤ a ∧ c ≤ b},
      StringName.label (γ := v.presentation.index.toOrd.val) c.val ∈ᴮ recoveredFilter v := by
  simpa only [recoveredFilter_mem] using hc.cones_directed a b

theorem recoveredFilter_meets_dense (D : Set v.Poset) (hd : ∀ p ≤ v.point, ∃ d ∈ D, d ≤ p) :
    condition v ≤ ⨆ d : D, StringName.label (γ := v.presentation.index.toOrd.val) d.val ∈ᴮ recoveredFilter v := by
  simpa only [recoveredFilter_mem] using v.withPoint_predense D hd

theorem recoveredFilter_meets_dense_name (D : Set v.Poset) (hd : ∀ p ≤ v.point, ∃ d ∈ D, d ≤ p) :
    condition v ≤ ⨆ x : bSet (Algebra κ θ),
      (x ∈ᴮ check'' (fun d : D => StringName.label (γ := v.presentation.index.toOrd.val) d.val)) ⊓
      (x ∈ᴮ recoveredFilter v) := by
  apply (recoveredFilter_meets_dense v D hd).trans
  apply iSup_le
  intro d
  apply le_iSup_of_le (StringName.label (γ := v.presentation.index.toOrd.val) d.val)
  exact le_inf (le_top.trans (mem_mk' (check'' (fun q : D =>
    StringName.label (γ := v.presentation.index.toOrd.val) q.val)) d)) le_rfl

end Erdos1172Shioya
