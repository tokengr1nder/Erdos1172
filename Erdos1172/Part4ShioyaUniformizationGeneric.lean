/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUniformization
public import Erdos1172.Part4ShioyaGenericCodingStages

@[expose] public section

/-! # Ground uniformization diagrams in the Shioya generic

A ground diagram can occur only where all its stage and edge conditions
belong to the same generic. Their Boolean meet is exactly the truth value
of a single subset assertion. The name below collects the ground diagrams
with the prescribed coding and inverse-limit properties.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open bSet Erdos1172PosetCompletion Erdos1172PosetGeneric

universe u
namespace Erdos1172Shioya.Uniformization
namespace Presentation

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)] [Nonempty (Condition κ θ)]

/-- Ground set of Boolean condition labels required by a given diagram. -/
def requiredLabels (a : Presentation κ θ) : PSet.{u} :=
  .mk a.diagram.requirements (fun p => genericLabel (positiveCondition p.val))

def requirementsValue (a : Presentation κ θ) : Algebra κ θ :=
  ⨅ p : a.diagram.requirements, condition p.val

theorem requirementsValue_eq_subset (a : Presentation κ θ) :
    a.requirementsValue = (check a.requiredLabels ⊆ᴮ genericFilterName (Algebra κ θ)) := by
  rw [subset_unfold]
  change (⨅ p : a.diagram.requirements, condition p.val) =
    ⨅ p : a.diagram.requirements, _root_.imp ⊤
      (check (genericLabel (positiveCondition p.val)) ∈ᴮ genericFilterName (Algebra κ θ))
  simp only [genericFilterName_mem, top_imp]
  rfl

omit [Nonempty (Condition κ θ)] in
theorem le_requirementsValue_iff (a : Presentation κ θ) (Γ : Algebra κ θ) :
    Γ ≤ a.requirementsValue ↔ a.diagram.requirements ⊆ {p | Γ ≤ condition p} := by
  constructor
  · intro h p hp
    exact h.trans (iInf_le (fun q : a.diagram.requirements => condition q.val) ⟨p,hp⟩)
  · intro h
    exact le_iInf fun p : a.diagram.requirements => (show Γ ≤ condition p.val from h p.property)

omit [Nonempty (Condition κ θ)] in
theorem requirementsValue_mono {v u : Presentation κ θ} (h : v ≤ u) :
    v.requirementsValue ≤ u.requirementsValue := by
  apply le_iInf
  intro p
  exact iInf_le (fun q : v.diagram.requirements => condition q.val)
    ⟨p.val,requirements_mono h p.property⟩

def labelEmbedding :
    Presentation κ θ ↪ (PSet.ordinalMk (Cardinal.mk (Presentation κ θ)).ord).Type := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).mp
  simp only [PSet.ordinalMk_type, Cardinal.mk_ord_toType, le_refl]

def label (a : Presentation κ θ) : PSet.{u} :=
  (PSet.ordinalMk (Cardinal.mk (Presentation κ θ)).ord).Func (labelEmbedding a)

omit [Fact (Cardinal.aleph0 < κ)] [Nonempty (Condition κ θ)] in
private theorem label_separated {a b : Presentation κ θ} (h : a ≠ b) :
    ¬ PSet.Equiv a.label b.label :=
  PSet.ordinalMk_inj _ _ _ (fun he => h (labelEmbedding.injective he))

def groundFamily (Coding : Condition κ θ → Prop) : bSet (Algebra κ θ) :=
  .mk (GroundCondition κ θ Set.univ Coding) (fun a => check a.val.label)
    (fun a => a.val.requirementsValue)

theorem le_groundFamily_mem_iff (Coding : Condition κ θ → Prop) (a : Presentation κ θ)
    {Γ : Algebra κ θ} (hΓ : Γ ≠ ⊥) :
    Γ ≤ check a.label ∈ᴮ groundFamily Coding ↔ a.Valid {p | Γ ≤ condition p} Coding := by
  classical
  have hmem : (check a.label ∈ᴮ groundFamily Coding) ≤ a.requirementsValue := by
    rw [mem_unfold]
    apply iSup_le
    intro b
    change GroundCondition κ θ Set.univ Coding at b
    change b.val.requirementsValue ⊓ (check a.label =ᴮ check b.val.label) ≤ _
    by_cases he : a = b.val
    · exact inf_le_left.trans_eq (congrArg requirementsValue he.symm)
    · exact (inf_le_right.trans_eq (check_bv_eq_bot_of_not_equiv (label_separated he))).trans bot_le
  constructor
  · intro h
    have hstatic : a.Valid Set.univ Coding := by
      by_contra hn
      apply hΓ
      apply bot_unique
      apply h.trans
      rw [mem_unfold]
      apply iSup_le
      intro b
      change GroundCondition κ θ Set.univ Coding at b
      change b.val.requirementsValue ⊓ (check a.label =ᴮ check b.val.label) ≤ ⊥
      have he : a ≠ b.val := fun e => hn (e ▸ b.property)
      exact inf_le_right.trans_eq (check_bv_eq_bot_of_not_equiv (label_separated he))
    exact ⟨hstatic.1,(le_requirementsValue_iff a Γ).mp (h.trans hmem),hstatic.2.2⟩
  · intro h
    let b : GroundCondition κ θ Set.univ Coding := ⟨a,h.1,Set.subset_univ _,h.2.2⟩
    exact ((le_requirementsValue_iff a Γ).mpr h.2.1).trans (mem_mk' (groundFamily Coding) b)

open LevyProduct

/-- Below each condition the generic admits singleton uniformization diagrams
on arbitrarily late Lévy stages. The recovered point of the displayed stage
still refines the originally prescribed condition. -/
theorem singleton_stages_below (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)
    (z : Index θ) (hz : IsBot z) (late : Index θ) (p : Condition κ θ) :
    condition p ≤ ⨆ a : {a : (stageSystem hκ hκθ hθ).Entry // late ≤ a.stage ∧
      a.length = a.stage ∧ (topPresentation hκ hκθ hθ a).withPoint a.point ≤ p},
      (check (singleton z hz (topPresentation hκ hκθ hθ a.val)).label ∈ᴮ
        groundFamily (κ := κ) (θ := θ) Condition.CodesDense) ⊓
      (StringName.label (γ := ((stageSystem hκ hκθ hθ).base a.val.stage).presentation.index.toOrd.val)
        a.val.point ∈ᴮ recoveredFilter (topPresentation hκ hκθ hθ a.val)) := by
  apply cone_le_of_refinements
  intro r hr
  obtain ⟨a,hl,hs,hc,ha⟩ := exists_pointed_coding_stage hκ hκθ hθ r late
  let v := topPresentation hκ hκθ hθ a
  let t := v.withPoint a.point
  have htop : ∀ x : v.Poset, x ≤ v.point := topPresentation_greatest hκ hκθ hθ a
  have hv : condition t ≤ condition v := condition_mono (v.withPoint_le (htop a.point))
  refine ⟨t,ha,le_iSup_of_le ⟨a,hl,hs,ha.trans hr⟩ (le_inf ?_ ?_)⟩
  · apply (le_groundFamily_mem_iff _ _ (condition_ne_bot t)).mpr
    exact singleton_valid z hz _ _ v htop hc.dense hv
  · exact (recoveredFilter_mem v a.point).ge

/-- Every ground singleton in the generic has a two-stage end extension
whose final coding word is on a Lévy stage beyond any prescribed index. -/
theorem two_stage_extensions_below (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)
    (z : Index θ) (hz : IsBot z) (b : Index θ) (hzb : z < b)
    (hpair : ∀ i ≤ b, i = z ∨ i = b) (late : Index θ) (p : Condition κ θ)
    (hp : ∀ x : p.Poset, x ≤ p.point) (hc : p.CodesDense) :
    condition p ≤ ⨆ D : {D : Diagram κ θ (Set.Iic b) //
      (⟨b,D⟩ : Presentation κ θ) ≤ singleton z hz p ∧
      ∃ a : (stageSystem hκ hκθ hθ).Entry, late ≤ a.stage ∧ a.length = a.stage ∧
        D.stage ⟨b,show b ≤ b from le_rfl⟩ = topPresentation hκ hκθ hθ a},
      check (Presentation.label (⟨b,D.val⟩ : Presentation κ θ)) ∈ᴮ
        groundFamily (κ := κ) (θ := θ) Condition.CodesDense := by
  apply cone_le_of_refinements
  intro r hr
  obtain ⟨a,hl,hs,ha,har⟩ := exists_pointed_coding_stage hκ hκθ hθ r late
  let q := topPresentation hκ hκθ hθ a
  let t := q.withPoint a.point
  have htp : t ≤ p := har.trans hr
  obtain ⟨π,hw,he⟩ := htp
  let edge : Edge p q := ⟨a.point,π,hw,he⟩
  let G := {s : Condition κ θ | condition t ≤ condition s}
  have hq : ∀ x : q.Poset, x ≤ q.point := topPresentation_greatest hκ hκθ hθ a
  obtain ⟨D,hd,hdp,_,hdq⟩ := exists_two_stage_extension z hz b hzb hpair G
    Condition.CodesDense p q edge ⟨hp,hc,condition_mono (har.trans hr)⟩
      ⟨hq,ha.dense,condition_mono (q.withPoint_le (hq a.point))⟩
      (show condition t ≤ condition t from le_rfl)
  exact ⟨t,har,le_iSup_of_le ⟨D,hdp,a,hl,hs,hdq⟩
    ((le_groundFamily_mem_iff _ (⟨b,D⟩ : Presentation κ θ) (condition_ne_bot t)).mpr hd)⟩

end Presentation
end Erdos1172Shioya.Uniformization
