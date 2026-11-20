/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalProjectionComposition

@[expose] public section

/-! # Transitivity of pointed word refinement between internal Shioya presentations -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem pointTest_apply {Γ : B} {R S F p q x y : N} (h : Γ ≤ pointTest R S F p q)
    (hxy : Γ ≤ edge F x y) (hxp : Γ ≤ edge R x p) : Γ ≤ edge S y q :=
  projection_imp.mp (h.trans (iInf_le _ x) |>.trans (iInf_le _ y)) Γ le_rfl (le_inf hxy hxp)

theorem wordTest_apply {Γ : B} {R F p l b l' b' x y i : N} (h : Γ ≤ wordTest R F p l b l' b')
    (hxy : Γ ≤ edge F x y) (hxp : Γ ≤ edge R x p) (hi : Γ ≤ i ∈ᴮ l') :
    Γ ≤ (edge b x i ⟹ edge b' y i) ⊓ (edge b' y i ⟹ edge b x i) :=
  projection_imp.mp (h.trans inf_le_right |>.trans (iInf_le _ x) |>.trans (iInf_le _ y) |>.trans (iInf_le _ i))
    Γ le_rfl (le_inf (le_inf hxy hxp) hi)

theorem pointTest_comp {Γ : B} {Q T R S V p q r D F E G : N}
    (hf : Γ ≤ is_function D Q F) (hg : Γ ≤ is_function E T G)
    (hp : Γ ≤ pointTest R S F p q) (hq : Γ ≤ pointTest S V G q r) :
    Γ ≤ pointTest R V (projectionComposite D F E G T) p r := by
  refine le_iInf fun x => le_iInf fun z => projection_imp.mpr ?_
  intro Δ h hz
  obtain ⟨y,hxy,hyz⟩ := (projectionComposite_pair (h.trans hf) (h.trans hg)).mp (hz.trans inf_le_left)
  exact pointTest_apply (h.trans hq) hyz (pointTest_apply (h.trans hp) hxy (hz.trans inf_le_right))

theorem wordTest_comp {Γ : B} {Q T R S p q l₁ b₁ l₂ b₂ l₃ b₃ D F E G : N}
    (hf : Γ ≤ is_function D Q F) (hg : Γ ≤ is_function E T G)
    (hp : Γ ≤ pointTest R S F p q)
    (w₁ : Γ ≤ wordTest R F p l₁ b₁ l₂ b₂) (w₂ : Γ ≤ wordTest S G q l₂ b₂ l₃ b₃) :
    Γ ≤ wordTest R (projectionComposite D F E G T) p l₁ b₁ l₃ b₃ := by
  refine le_inf (subset_trans' (w₂.trans inf_le_left) (w₁.trans inf_le_left))
    (le_iInf fun x => le_iInf fun z => le_iInf fun i => projection_imp.mpr ?_)
  intro Δ h hs
  have hi := hs.trans inf_le_right
  have hxp := hs.trans (inf_le_left.trans inf_le_right)
  obtain ⟨y,hxy,hyz⟩ := (projectionComposite_pair (h.trans hf) (h.trans hg)).mp (hs.trans (inf_le_left.trans inf_le_left))
  have a := wordTest_apply (h.trans w₁) hxy hxp (mem_of_mem_subset (h.trans (w₂.trans inf_le_left)) hi)
  have b := wordTest_apply (h.trans w₂) hyz (pointTest_apply (h.trans hp) hxy hxp) hi
  refine le_inf (projection_imp.mpr fun e he hv => ?_) (projection_imp.mpr fun e he hv => ?_)
  · exact projection_imp.mp (b.trans inf_le_left) e he (projection_imp.mp (a.trans inf_le_left) e he hv)
  · exact projection_imp.mp (a.trans inf_le_right) e he (projection_imp.mp (b.trans inf_le_right) e he hv)

private theorem splitJoin {I : Type*} {Γ z : B} {v : I → B} (h : Γ ≤ ⨆ i, v i)
    (step : ∀ i, Γ ⊓ v i ≤ z) : Γ ≤ z :=
  ((inf_eq_left.mpr h).symm.trans (inf_iSup_eq Γ v)).le.trans (iSup_le step)

/-- Eliminate a refinement locally by genuine internal domain and graph names. -/
theorem refinementValue_cases {Γ z : B} {K P R p l b Q S q m c : N}
    (h : Γ ≤ refinementValue K P R p l b Q S q m c)
    (step : ∀ {d : B}, d ≤ Γ → ∀ D F : N, d ≤ partialProjectionValue K P R Q S D F →
      d ≤ pointTest R S F p q → d ≤ wordTest R F p l b m c → d ≤ z) : Γ ≤ z := by
  apply splitJoin h
  intro D
  apply splitJoin inf_le_right
  intro F
  exact step (inf_le_left.trans inf_le_left) D F (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)

theorem refinementValue_trans {Γ : B} {K P R p l₁ b₁ Q S q l₂ b₂ T V r l₃ b₃ : N}
    (hk : Γ ≤ omega ∈ᴮ K) (hP : Γ ≤ partialOrderValue P R) (hQ : Γ ≤ partialOrderValue Q S)
    (hT : Γ ≤ partialOrderValue T V) (hC : Γ ≤ shortInfimaValue K P R)
    (pq : Γ ≤ refinementValue K P R p l₁ b₁ Q S q l₂ b₂)
    (qr : Γ ≤ refinementValue K Q S q l₂ b₂ T V r l₃ b₃) :
    Γ ≤ refinementValue K P R p l₁ b₁ T V r l₃ b₃ := by
  apply refinementValue_cases pq
  intro Δ h D F pi hpt word
  apply refinementValue_cases (h.trans qr)
  intro d h' E G sig hqt word'
  have base := h'.trans h
  have hf := (projectionLaws_iff.mp (h'.trans pi)).func
  have hg := (projectionLaws_iff.mp sig).func
  exact le_iSup_of_le (projectionPullback D F E) (le_iSup_of_le (projectionComposite D F E G T)
    (le_inf (le_inf (partialProjectionValue_comp (base.trans hk) (base.trans hP) (base.trans hQ) (base.trans hT)
      (base.trans hC) (h'.trans pi) sig) (pointTest_comp hf hg (h'.trans hpt) hqt))
      (wordTest_comp hf hg (h'.trans hpt) (h'.trans word) word')))

end bSet.ErdosShioyaInternal
