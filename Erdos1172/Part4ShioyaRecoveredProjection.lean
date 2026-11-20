/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUniformization
public import Erdos1172.Part4ShioyaRecoveredFilter

@[expose] public section

/-! # Recovered presentation generics along a uniformization edge

Below the chosen source point, a condition belongs to the recovered
target filter exactly where some stronger domain point belongs to the
recovered source filter and projects below that target condition.
-/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion
open scoped Flypitch
universe u
namespace Erdos1172Shioya.Uniformization.Edge

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)] {p q : Condition κ θ}
variable (E : Edge p q)

abbrev liftsOf (r : p.Poset) :=
  {t : E.projection.dom // t.val ≤ E.source ∧ E.projection.proj t ≤ r}

theorem repoint_le {r : p.Poset} (t : E.projection.dom) (ht : t.val ≤ E.source)
    (hr : E.projection.proj t ≤ r) : q.withPoint t.val ≤ p.withPoint r :=
  ⟨E.projection,(E.projection.dom_condition t _).mpr (condition_mono hr),
    (condition_mono ht).trans E.string_le⟩

theorem recovered_projection (hp : p.CodesDense) (r : p.Poset) :
    condition (q.withPoint E.source) ⊓ condition (p.withPoint r) =
      ⨆ t : E.liftsOf r, condition (q.withPoint t.val.val) := by
  classical
  have lower (t : E.liftsOf r) : condition (q.withPoint t.val.val) ≤
      condition (q.withPoint E.source) ⊓ condition (p.withPoint r) := by
    apply le_inf
    · exact condition_mono (q.withPoint_mono t.property.1)
    · exact condition_mono (E.repoint_le t.val t.property.1 t.property.2)
  apply le_antisymm _ (iSup_le lower)
  let π := E.projection
  let D := {t : q.Poset | ∃ h : t ∈ π.dom, t ≤ E.source ∧
    (π.proj ⟨t,h⟩ ≤ r ∨ ¬ ∃ s, s ≤ π.proj ⟨t,h⟩ ∧ s ≤ r)}
  have hD (a : q.Poset) (ha : a ≤ E.source) : ∃ t ∈ D, t ≤ a := by
    obtain ⟨x,hx⟩ := π.dense a
    by_cases h : ∃ s, s ≤ π.proj x ∧ s ≤ r
    · obtain ⟨s,hs,hsr⟩ := h
      obtain ⟨t,ht,hts⟩ := π.lifts x s hs
      have hta : t.val ≤ a := (show t.val ≤ x.val from ht).trans hx
      exact ⟨t.val,⟨t.property,hta.trans ha,Or.inl (hts.trans hsr)⟩,hta⟩
    · exact ⟨x.val,⟨x.property,hx.trans ha,Or.inr h⟩,hx⟩
  have hcover := (q.withPoint E.source).withPoint_predense D hD
  apply (inf_le_inf_right _ hcover).trans
  rw [iSup_inf_eq]
  apply iSup_le
  rintro ⟨t,hd,ht,htr | hbad⟩
  · exact inf_le_left.trans (le_iSup (fun z : E.liftsOf r => condition (q.withPoint z.val.val))
      ⟨⟨t,hd⟩,ht,htr⟩)
  · let s := π.proj ⟨t,hd⟩
    have hts : condition (q.withPoint t) ≤ condition (p.withPoint s) :=
      condition_mono (E.repoint_le ⟨t,hd⟩ ht le_rfl)
    apply (inf_le_inf_right _ hts).trans
    exact (hp.cones_directed s r).le.trans (iSup_le fun b => (hbad ⟨b.val,b.property⟩).elim)

theorem recoveredFilter_projection [Nonempty (Condition κ θ)] (hp : p.CodesDense) (r : p.Poset) :
    ((StringName.label (γ := q.presentation.index.toOrd.val) E.source ∈ᴮ recoveredFilter q) ⊓
      (StringName.label (γ := p.presentation.index.toOrd.val) r ∈ᴮ recoveredFilter p)) =
      ⨆ t : E.liftsOf r, StringName.label (γ := q.presentation.index.toOrd.val) t.val.val ∈ᴮ
        recoveredFilter q := by
  simpa only [recoveredFilter_mem] using E.recovered_projection hp r

end Erdos1172Shioya.Uniformization.Edge
