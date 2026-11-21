/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenBoundedUltrapowerIso
public import Erdos1172.Part4LevyMatchingBoundedSourceMaster
public import Erdos1172.Part4SideForcingBaseChange

@[expose] public section

/-! # Stage-1 anonymous ultrapower lift into the localized source–Cohen algebra

Combining `anonymousUltrapowerHom` (Module 2) with `exists_matching_bounded_source_master` and
`BaseChange.hom`, we show that `anonymousAlgebra θ` embeds into `Erdos1172CohenIteration.omegaOneAlgebra R`
without any external `Col(ω, θ)` factor surviving (`anonymousSourceCohenHom`). Localizing
`Erdos1172CohenIteration.omegaOneAlgebra R` below the source master condition `sourceCohenMaster u`
yields `LocalizedSourceCohen R (sourceCohenMaster u) hm₀` and a complete Boolean homomorphism
`stageOneScalarHom : CompleteLatticeHom (Algebra U (anonymousAlgebra κ)) (LocalizedSourceCohen ...)`
that agrees on constant germs `value U (fun _ => b)` with `u (inclusion _ b)` (`stageOneBase`) and
sends `boundedAnonName U a (fun _ => anonymousSubset κ)` to the generic subset of `θ` (`stageOneSubsetEq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter Cardinal bSet Lattice ErdosNameTransport ErdosOmegaTwo ErdosCohen
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172CompleteSubalgebra
open Erdos1172GroundUltrapower Erdos1172LevyCohen Erdos1172BooleanUltrapower
open Erdos1172Shioya.ForcingCover Erdos1172BooleanNameIteration
open scoped Flypitch Erdos1172LevyCollapse

universe u

namespace Erdos1172LevyCollapse.Matching

private theorem completeHom_inf {X Y : Type u} [CompleteLattice X] [CompleteLattice Y]
    (e : CompleteLatticeHom X Y) (x y : X) : e (x ⊓ y) = e x ⊓ e y := by
  rw [← sInf_pair, sInfHomClass.map_sInf, Set.image_pair, sInf_pair]

private theorem completeHom_sup {X Y : Type u} [CompleteLattice X] [CompleteLattice Y]
    (e : CompleteLatticeHom X Y) (x y : X) : e (x ⊔ y) = e x ⊔ e y := by
  rw [← sSup_pair, sSupHomClass.map_sSup, Set.image_pair, sSup_pair]

private theorem inf_of_le {α : Type u} [SemilatticeInf α] {x y : α} (h : x ≤ y) :
    x ⊓ y = x := inf_eq_left.mpr h

private theorem inf_comm_eq {α : Type u} [SemilatticeInf α] (x y : α) :
    x ⊓ y = y ⊓ x := inf_comm x y

theorem jointSourceHom_injective {R J : Type u} [NontrivialCompleteBooleanAlgebra R] [Nonempty J] :
    Function.Injective (jointSourceHom (R := R) J) := by
  intro x y hxy
  apply joint_source_reflects (d := (⊤ : Erdos1172Collapse.Algebra J)) top_ne_bot
  rw [hxy]

section LocalizedBelow

/-- Principal-ideal localization `{w : W // w ≤ m₀.val}` of a complete Boolean algebra `W` below a
positive element `m₀ : Positive W`. -/
def LocalizedBelow (W : Type u) [CompleteBooleanAlgebra W] (m₀ : Positive W) : Type u :=
  {w : W // w ≤ m₀.val}

namespace LocalizedBelow
variable {W : Type u} [CompleteBooleanAlgebra W] (m₀ : Positive W)

@[ext]
theorem ext {x y : LocalizedBelow W m₀} (h : x.val = y.val) : x = y :=
  Subtype.ext h

instance : CompleteBooleanAlgebra (LocalizedBelow W m₀) where
  le x y := x.val ≤ y.val
  lt x y := x.val < y.val
  le_refl x := le_refl x.val
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
  le_antisymm _ _ h1 h2 := Subtype.ext (le_antisymm h1 h2)
  sup x y := ⟨x.val ⊔ y.val, sup_le x.property y.property⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ := sup_le
  inf x y := ⟨x.val ⊓ y.val, inf_le_left.trans x.property⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  sSup S := ⟨sSup (Subtype.val '' S), sSup_le (by rintro _ ⟨x, _, rfl⟩; exact x.property)⟩
  isLUB_sSup S :=
    ⟨fun x hx => le_sSup ⟨x, hx, rfl⟩,
     fun b hb => sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hb hx)⟩
  sInf S := ⟨m₀.val ⊓ sInf (Subtype.val '' S), inf_le_left⟩
  isGLB_sInf S :=
    ⟨fun x hx => inf_le_right.trans (sInf_le ⟨x, hx, rfl⟩),
     fun b hb => le_inf b.property (le_sInf (by rintro _ ⟨x, hx, rfl⟩; exact hb hx))⟩
  top := ⟨m₀.val, le_rfl⟩
  le_top x := x.property
  bot := ⟨⊥, bot_le⟩
  bot_le _ := bot_le
  compl x := ⟨m₀.val ⊓ x.valᶜ, inf_le_left⟩
  sdiff x y := ⟨x.val ⊓ (m₀.val ⊓ y.valᶜ), inf_le_left.trans x.property⟩
  himp x y := ⟨m₀.val ⊓ (x.valᶜ ⊔ y.val), inf_le_left⟩
  le_sup_inf x y z := show (x.val ⊔ y.val) ⊓ (x.val ⊔ z.val) ≤ x.val ⊔ (y.val ⊓ z.val) from le_sup_inf
  inf_compl_le_bot x := by
    change x.val ⊓ (m₀.val ⊓ x.valᶜ) ≤ ⊥
    calc
      x.val ⊓ (m₀.val ⊓ x.valᶜ) ≤ x.val ⊓ x.valᶜ := inf_le_inf_left _ inf_le_right
      _ = ⊥ := inf_compl_eq_bot
  top_le_sup_compl x := by
    change m₀.val ≤ x.val ⊔ (m₀.val ⊓ x.valᶜ)
    calc
      m₀.val = m₀.val ⊓ (x.val ⊔ x.valᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = (m₀.val ⊓ x.val) ⊔ (m₀.val ⊓ x.valᶜ) := inf_sup_left _ _ _
      _ ≤ x.val ⊔ (m₀.val ⊓ x.valᶜ) := sup_le_sup inf_le_right le_rfl
  sdiff_eq _ _ := rfl
  himp_eq x y := Subtype.ext (by
    change m₀.val ⊓ (x.valᶜ ⊔ y.val) = y.val ⊔ (m₀.val ⊓ x.valᶜ)
    calc
      m₀.val ⊓ (x.valᶜ ⊔ y.val) = (m₀.val ⊓ x.valᶜ) ⊔ (m₀.val ⊓ y.val) := inf_sup_left _ _ _
      _ = (m₀.val ⊓ x.valᶜ) ⊔ y.val := by rw [inf_eq_right.mpr y.property]
      _ = y.val ⊔ (m₀.val ⊓ x.valᶜ) := sup_comm _ _)

instance : NontrivialCompleteBooleanAlgebra (LocalizedBelow W m₀) where
  toCompleteBooleanAlgebra := inferInstance
  bot_lt_top := lt_of_le_of_ne bot_le fun h => m₀.property (congrArg Subtype.val h).symm

/-- Complete Boolean restriction homomorphism `w ↦ w ⊓ m₀.val` onto `LocalizedBelow W m₀`. -/
def restrict : CompleteLatticeHom W (LocalizedBelow W m₀) where
  toFun w := ⟨w ⊓ m₀.val, inf_le_right⟩
  map_sSup' S := Subtype.ext (by
    change sSup S ⊓ m₀.val = sSup (Subtype.val '' ((fun w => (⟨w ⊓ m₀.val, inf_le_right⟩ : LocalizedBelow W m₀)) '' S))
    rw [Set.image_image, sSup_inf_eq, sSup_image])
  map_sInf' S := Subtype.ext (by
    change sInf S ⊓ m₀.val = m₀.val ⊓ sInf (Subtype.val '' ((fun w => (⟨w ⊓ m₀.val, inf_le_right⟩ : LocalizedBelow W m₀)) '' S))
    rw [Set.image_image, inf_comm (sInf S) m₀.val]
    apply le_antisymm
    · refine le_inf inf_le_left (le_sInf ?_)
      rintro _ ⟨w, hw, rfl⟩
      exact le_inf ((inf_le_right.trans (sInf_le hw))) inf_le_left
    · refine le_inf inf_le_left (le_sInf fun w hw => ?_)
      have hmem : w ⊓ m₀.val ∈ (fun x => x ⊓ m₀.val) '' S := ⟨w, hw, rfl⟩
      exact (inf_le_right.trans (sInf_le hmem)).trans inf_le_left)

end LocalizedBelow
end LocalizedBelow

section ChangeEquivalentName
variable {E : Type u} [NontrivialCompleteBooleanAlgebra E]

def equivCone (U₁ U₂ : bSet E) (p : Condition U₁) :
    Erdos1172BooleanNameIteration.Algebra U₂ :=
  ⨆ q : {q : Condition U₂ // q.value ≤ p.value ∧ q.value ≤ name p ⊆ᴮ name q},
    Erdos1172PosetCompletion.condition q.val

theorem equivCone_ne_bot {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂) (p : Condition U₁) :
    equivCone U₁ U₂ p ≠ ⊥ := by
  have hmem : p.value ≤ name p ∈ᴮ U₂ :=
    mem_congr bv_refl (le_top.trans heq) (name_mem p)
  obtain ⟨q, hqv, hqeq⟩ := exists_canonical_refinement p.nonzero hmem
  intro h0
  have hle : Erdos1172PosetCompletion.condition q ≤ equivCone U₁ U₂ p :=
    le_iSup (fun r : {r : Condition U₂ // r.value ≤ p.value ∧ r.value ≤ name p ⊆ᴮ name r} =>
      Erdos1172PosetCompletion.condition r.val) ⟨q, hqv, subset_of_eq hqeq⟩
  exact Erdos1172PosetCompletion.condition_ne_bot q (le_bot_iff.mp (hle.trans_eq h0))

theorem equivCone_mono {U₁ U₂ : bSet E} {p₁ p₂ : Condition U₁} (hle : p₁ ≤ p₂) :
    equivCone U₁ U₂ p₁ ≤ equivCone U₁ U₂ p₂ := by
  refine iSup_le fun ⟨q, hqv, hqsub⟩ => ?_
  exact le_iSup (fun r : {r : Condition U₂ // r.value ≤ p₂.value ∧ r.value ≤ name p₂ ⊆ᴮ name r} =>
    Erdos1172PosetCompletion.condition r.val)
    ⟨q, hqv.trans hle.1, subset_trans' (hqv.trans hle.2) hqsub⟩

private theorem equivCone_le_condition {U₁ U₂ : bSet E} {p : Condition U₁} {q : Condition U₂}
    (hpv : p.value ≤ q.value) (hpeq : p.value ≤ name q ⊆ᴮ name p) :
    equivCone U₁ U₂ p ≤ Erdos1172PosetCompletion.condition q := by
  refine iSup_le fun ⟨r, hrv, hrsub⟩ => ?_
  have hrq : r ≤ q := ⟨hrv.trans hpv, subset_trans' (hrv.trans hpeq) hrsub⟩
  exact Erdos1172PosetCompletion.condition_mono hrq

private theorem exists_mem_iSup_inf_ne_bot {α : Type u} [CompleteBooleanAlgebra α]
    {ι : Sort*} {f : ι → α} {c : α} (h : c ⊓ (⨆ i, f i) ≠ ⊥) : ∃ i, c ⊓ f i ≠ ⊥ := by
  by_contra hnone
  apply h
  rw [inf_iSup_eq]
  exact iSup_eq_bot.mpr fun i => by_contra fun hi => hnone ⟨i, hi⟩

def equivConeOrderHom {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂) :
    Condition U₁ →o Positive (Erdos1172BooleanNameIteration.Algebra U₂) :=
  ⟨fun p => ⟨equivCone U₁ U₂ p, equivCone_ne_bot heq p⟩, fun _ _ h => equivCone_mono h⟩

theorem equivConeOrderHom_lifts {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂) :
    Lifts (equivConeOrderHom heq) := by
  intro p c hc
  have hc_val : c.val ≤ equivCone U₁ U₂ p := hc
  have hmeet : c.val ⊓ equivCone U₁ U₂ p ≠ ⊥ := by
    erw [inf_of_le hc_val]
    exact c.property
  obtain ⟨⟨q, hqv, hqsub⟩, hcq⟩ := exists_mem_iSup_inf_ne_bot hmeet
  obtain ⟨q₁, hq₁⟩ := Erdos1172PosetCompletion.exists_condition_le hcq
  obtain ⟨q₂, hq₂_q₁, hq₂_q⟩ :=
    (Erdos1172PosetCompletion.mem_condition_iff q q₁).mp
      (Erdos1172PosetCompletion.condition_le_iff.mp (hq₁.trans inf_le_right)) q₁ le_rfl
  have hq₂_c : Erdos1172PosetCompletion.condition q₂ ≤ c.val :=
    (Erdos1172PosetCompletion.condition_mono hq₂_q₁).trans (hq₁.trans inf_le_left)
  have hmem₁ : q₂.value ≤ name q₂ ∈ᴮ U₁ :=
    mem_congr bv_refl (le_top.trans (bv_symm heq)) (name_mem q₂)
  obtain ⟨p', hp'v, hp'eq⟩ := exists_canonical_refinement q₂.nonzero hmem₁
  have hp'_p : p' ≤ p :=
    ⟨hp'v.trans (hq₂_q.1.trans hqv),
     subset_trans' (hp'v.trans (subset_trans' (hq₂_q.1.trans hqsub) hq₂_q.2)) (subset_of_eq hp'eq)⟩
  exact ⟨p', hp'_p, (equivCone_le_condition hp'v (subset_of_eq hp'eq)).trans hq₂_c⟩

theorem equivConeOrderHom_compat {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂)
    (p₁ p₂ : Condition U₁) (hle : equivConeOrderHom heq p₁ ≤ equivConeOrderHom heq p₂) :
    ∃ z ≤ p₁, z ≤ p₂ := by
  have hmem : p₁.value ≤ name p₁ ∈ᴮ U₂ :=
    mem_congr bv_refl (le_top.trans heq) (name_mem p₁)
  obtain ⟨q, hqv, hqeq⟩ := exists_canonical_refinement p₁.nonzero hmem
  have hq_cone₂ : Erdos1172PosetCompletion.condition q ≤ equivCone U₁ U₂ p₂ :=
    (le_iSup (fun r : {r : Condition U₂ // r.value ≤ p₁.value ∧ r.value ≤ name p₁ ⊆ᴮ name r} =>
      Erdos1172PosetCompletion.condition r.val) ⟨q, hqv, subset_of_eq hqeq⟩).trans hle
  have hmeet : Erdos1172PosetCompletion.condition q ⊓ equivCone U₁ U₂ p₂ ≠ ⊥ := by
    erw [inf_of_le hq_cone₂]
    exact Erdos1172PosetCompletion.condition_ne_bot q
  obtain ⟨⟨r, hrv, hrsub⟩, hqr⟩ := exists_mem_iSup_inf_ne_bot hmeet
  obtain ⟨s, hs_q, hs_r⟩ := (Erdos1172PosetCompletion.condition_inf_ne_bot_iff q r).mp hqr
  have hmem₁ : s.value ≤ name s ∈ᴮ U₁ :=
    mem_congr bv_refl (le_top.trans (bv_symm heq)) (name_mem s)
  obtain ⟨z, hzv, hzeq⟩ := exists_canonical_refinement s.nonzero hmem₁
  have hz₁ : z ≤ p₁ :=
    ⟨hzv.trans (hs_q.1.trans hqv),
     subset_trans' (hzv.trans (subset_trans' (hs_q.1.trans (subset_of_eq hqeq)) hs_q.2))
       (subset_of_eq hzeq)⟩
  have hz₂ : z ≤ p₂ :=
    ⟨hzv.trans (hs_r.1.trans hrv),
     subset_trans' (hzv.trans (subset_trans' (hs_r.1.trans hrsub) hs_r.2))
       (subset_of_eq hzeq)⟩
  exact ⟨z, hz₁, hz₂⟩

theorem equivConeOrderHom_dense {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂)
    (c : Positive (Erdos1172BooleanNameIteration.Algebra U₂)) :
    ∃ p, equivConeOrderHom heq p ≤ c := by
  obtain ⟨q, hqc⟩ := Erdos1172PosetCompletion.exists_condition_le c.property
  have hmem₁ : q.value ≤ name q ∈ᴮ U₁ :=
    mem_congr bv_refl (le_top.trans (bv_symm heq)) (name_mem q)
  obtain ⟨p, hpv, hpeq⟩ := exists_canonical_refinement q.nonzero hmem₁
  exact ⟨p, (equivCone_le_condition hpv (subset_of_eq hpeq)).trans hqc⟩

/-- Boolean-equivalent forcing names `⊤ ≤ U₁ =ᴮ U₂` have canonically isomorphic completed
algebras `Algebra U₁ ≃o Algebra U₂`. -/
def changeEquivalentName {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂) :
    Erdos1172BooleanNameIteration.Algebra U₁ ≃o Erdos1172BooleanNameIteration.Algebra U₂ :=
  (completionIso (equivConeOrderHom heq) (equivConeOrderHom_lifts heq)
    (equivConeOrderHom_compat heq) (equivConeOrderHom_dense heq)).symm.trans
    (Erdos1172PositiveBoolean.completionOrderIso (B := Erdos1172BooleanNameIteration.Algebra U₂)).symm

theorem changeEquivalentName_condition {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂)
    (p : Condition U₁) :
    changeEquivalentName heq (Erdos1172PosetCompletion.condition p) = equivCone U₁ U₂ p := by
  let iso1 := completionIso (equivConeOrderHom heq) (equivConeOrderHom_lifts heq)
    (equivConeOrderHom_compat heq) (equivConeOrderHom_dense heq)
  have h1 : iso1 (Erdos1172PosetCompletion.condition (equivConeOrderHom heq p)) =
      Erdos1172PosetCompletion.condition p :=
    booleanHom_condition (equivConeOrderHom heq) (equivConeOrderHom_lifts heq)
      (equivConeOrderHom_compat heq) p
  have h2 : iso1.symm (Erdos1172PosetCompletion.condition p) =
      Erdos1172PosetCompletion.condition (equivConeOrderHom heq p) := by
    rw [← h1, OrderIso.symm_apply_apply]
  change (Erdos1172PositiveBoolean.completionOrderIso
    (B := Erdos1172BooleanNameIteration.Algebra U₂)).symm
      (iso1.symm (Erdos1172PosetCompletion.condition p)) = _
  rw [h2, ← element_condition (equivConeOrderHom heq p), completionOrderIso_symm_apply]
  exact joinMembers_element (equivConeOrderHom heq p).val

theorem changeEquivalentName_sourceHom {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂) (b : E) :
    changeEquivalentName heq (sourceHom U₁ b) = sourceHom U₂ b := by
  let ψ : CompleteLatticeHom (Erdos1172BooleanNameIteration.Algebra U₁)
      (Erdos1172BooleanNameIteration.Algebra U₂) :=
    CompleteLatticeHom.OrderIso.toCompleteLatticeHom (changeEquivalentName heq)
  change ψ (sourceHom U₁ b) = sourceHom U₂ b
  apply le_antisymm
  · have hcov : sourceHom U₁ b =
        ⨆ p : {p : Condition U₁ // Erdos1172PosetCompletion.condition p ≤ sourceHom U₁ b},
          Erdos1172PosetCompletion.condition p.val :=
      le_antisymm (fun q hq => Erdos1172PosetCompletion.condition_le_iff.mp
        (le_iSup (fun p : {p : Condition U₁ // Erdos1172PosetCompletion.condition p ≤ sourceHom U₁ b} =>
          Erdos1172PosetCompletion.condition p.val) ⟨q, Erdos1172PosetCompletion.condition_le_iff.mpr hq⟩))
        (iSup_le fun p => p.property)
    rw [hcov, _root_.map_iSup ψ]
    refine iSup_le fun ⟨p, hp⟩ => ?_
    have hp_b : p.value ≤ b := (condition_le_source U₁ p b).mp hp
    change changeEquivalentName heq (Erdos1172PosetCompletion.condition p) ≤ sourceHom U₂ b
    rw [changeEquivalentName_condition]
    exact iSup_le fun ⟨q, hqv, _⟩ => (condition_le_source U₂ q b).mpr (hqv.trans hp_b)
  · apply le_of_dense_conditions_le Set.univ (fun q => ⟨q, Set.mem_univ _, le_rfl⟩)
    rintro ⟨q, _⟩ hq
    have hq_b : q.value ≤ b := (condition_le_source U₂ q b).mp hq
    by_contra hnot
    have hpos : Erdos1172PosetCompletion.condition q ⊓ (ψ (sourceHom U₁ b))ᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨q', hq'⟩ := Erdos1172PosetCompletion.exists_condition_le hpos
    obtain ⟨q'', hq''_q', hq''_q⟩ :=
      (Erdos1172PosetCompletion.mem_condition_iff q q').mp
        (Erdos1172PosetCompletion.condition_le_iff.mp (hq'.trans inf_le_left)) q' le_rfl
    have hmem₁ : q''.value ≤ name q'' ∈ᴮ U₁ :=
      mem_congr bv_refl (le_top.trans (bv_symm heq)) (name_mem q'')
    obtain ⟨p, hpv, hpeq⟩ := exists_canonical_refinement q''.nonzero hmem₁
    have hp_b : Erdos1172PosetCompletion.condition p ≤ sourceHom U₁ b :=
      (condition_le_source U₁ p b).mpr (hpv.trans (hq''_q.1.trans hq_b))
    have hmem_cone : p.value ≤ name p ∈ᴮ U₂ :=
      mem_congr bv_refl (le_top.trans heq) (name_mem p)
    obtain ⟨r, hrv, hreq⟩ := exists_canonical_refinement p.nonzero hmem_cone
    have hr_cone : Erdos1172PosetCompletion.condition r ≤ ψ (sourceHom U₁ b) := by
      have h1 : Erdos1172PosetCompletion.condition r ≤ equivCone U₁ U₂ p :=
        le_iSup (fun s : {s : Condition U₂ // s.value ≤ p.value ∧ s.value ≤ name p ⊆ᴮ name s} =>
          Erdos1172PosetCompletion.condition s.val) ⟨r, hrv, subset_of_eq hreq⟩
      exact h1.trans ((changeEquivalentName_condition heq p).symm.le.trans (OrderHomClass.mono ψ hp_b))
    have hr_q'' : r ≤ q'' :=
      ⟨hrv.trans hpv,
       subset_trans' (subset_of_eq (hrv.trans hpeq)) (subset_of_eq hreq)⟩
    have hr_not : Erdos1172PosetCompletion.condition r ≤ (ψ (sourceHom U₁ b))ᶜ :=
      (Erdos1172PosetCompletion.condition_mono (hr_q''.trans hq''_q')).trans (hq'.trans inf_le_right)
    exact Erdos1172PosetCompletion.condition_ne_bot r
      (le_bot_iff.mp ((le_inf hr_cone hr_not).trans inf_compl_eq_bot.le))

/-- The assignment cone `⨆ p : {p // p.value ≤ z ∈ᴮ name p}, condition p` is preserved under
`changeEquivalentName`. -/
theorem changeEquivalentName_memCone {U₁ U₂ : bSet E} (heq : (⊤ : E) ≤ U₁ =ᴮ U₂) (z : bSet E) :
    changeEquivalentName heq
      (⨆ p : {p : Condition U₁ // p.value ≤ z ∈ᴮ name p}, Erdos1172PosetCompletion.condition p.val) =
    ⨆ q : {q : Condition U₂ // q.value ≤ z ∈ᴮ name q}, Erdos1172PosetCompletion.condition q.val := by
  let ψ : CompleteLatticeHom (Erdos1172BooleanNameIteration.Algebra U₁)
      (Erdos1172BooleanNameIteration.Algebra U₂) :=
    CompleteLatticeHom.OrderIso.toCompleteLatticeHom (changeEquivalentName heq)
  change ψ _ = _
  rw [_root_.map_iSup ψ]
  apply le_antisymm
  · refine iSup_le fun ⟨p, hp⟩ => ?_
    change changeEquivalentName heq (Erdos1172PosetCompletion.condition p) ≤ _
    rw [changeEquivalentName_condition]
    refine iSup_le fun ⟨q, hqv, hqsub⟩ => ?_
    have hqz : q.value ≤ z ∈ᴮ name q := mem_of_mem_subset hqsub (hqv.trans hp)
    exact le_iSup (fun r : {r : Condition U₂ // r.value ≤ z ∈ᴮ name r} =>
      Erdos1172PosetCompletion.condition r.val) ⟨q, hqz⟩
  · refine iSup_le fun ⟨q, hq⟩ => ?_
    by_contra hnot
    let rhs := ⨆ p : {p : Condition U₁ // p.value ≤ z ∈ᴮ name p}, ψ (Erdos1172PosetCompletion.condition p.val)
    have hpos : Erdos1172PosetCompletion.condition q ⊓ rhsᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨q₁, hq₁⟩ := Erdos1172PosetCompletion.exists_condition_le hpos
    obtain ⟨q₂, hq₂_q₁, hq₂_q⟩ :=
      (Erdos1172PosetCompletion.mem_condition_iff q q₁).mp
        (Erdos1172PosetCompletion.condition_le_iff.mp (hq₁.trans inf_le_left)) q₁ le_rfl
    have hmem₁ : q₂.value ≤ name q₂ ∈ᴮ U₁ :=
      mem_congr bv_refl (le_top.trans (bv_symm heq)) (name_mem q₂)
    obtain ⟨p, hpv, hpeq⟩ := exists_canonical_refinement q₂.nonzero hmem₁
    have hq₂z : q₂.value ≤ z ∈ᴮ name q₂ :=
      mem_of_mem_subset hq₂_q.2 (hq₂_q.1.trans hq)
    have hpz : p.value ≤ z ∈ᴮ name p :=
      mem_congr bv_refl hpeq (hpv.trans hq₂z)
    have hmem₂ : p.value ≤ name p ∈ᴮ U₂ :=
      mem_congr bv_refl (le_top.trans heq) (name_mem p)
    obtain ⟨r, hrv, hreq⟩ := exists_canonical_refinement p.nonzero hmem₂
    have hr_rhs : Erdos1172PosetCompletion.condition r ≤ rhs := by
      have h1 : Erdos1172PosetCompletion.condition r ≤ equivCone U₁ U₂ p :=
        le_iSup (fun s : {s : Condition U₂ // s.value ≤ p.value ∧ s.value ≤ name p ⊆ᴮ name s} =>
          Erdos1172PosetCompletion.condition s.val) ⟨r, hrv, subset_of_eq hreq⟩
      have h2 : ψ (Erdos1172PosetCompletion.condition p) ≤ rhs :=
        le_iSup (fun t : {t : Condition U₁ // t.value ≤ z ∈ᴮ name t} =>
          ψ (Erdos1172PosetCompletion.condition t.val)) ⟨p, hpz⟩
      exact h1.trans ((changeEquivalentName_condition heq p).symm.le.trans h2)
    have hr_q₂ : r ≤ q₂ :=
      ⟨hrv.trans hpv,
       subset_trans' (subset_of_eq (hrv.trans hpeq)) (subset_of_eq hreq)⟩
    have hr_not : Erdos1172PosetCompletion.condition r ≤ rhsᶜ :=
      (Erdos1172PosetCompletion.condition_mono (hr_q₂.trans hq₂_q₁)).trans (hq₁.trans inf_le_right)
    exact Erdos1172PosetCompletion.condition_ne_bot r
      (le_bot_iff.mp ((le_inf hr_rhs hr_not).trans inf_compl_eq_bot.le))

end ChangeEquivalentName

section BaseChangeMemCone

private theorem completeHom_compl {X Y : Type u} [CompleteBooleanAlgebra X] [CompleteBooleanAlgebra Y]
    (e : CompleteLatticeHom X Y) (x : X) : e xᶜ = (e x)ᶜ := by
  refine (IsCompl.compl_eq ⟨?_, ?_⟩).symm
  · rw [disjoint_iff, ← completeHom_inf, inf_compl_eq_bot, BotHomClass.map_bot]
  · rw [codisjoint_iff, ← completeHom_sup, sup_compl_eq_top, TopHomClass.map_top]

/-- `BaseChange.hom j Q` transports every membership-assignment cone
`⨆ p : {p // p.value ≤ z ∈ᴮ name p}, condition p` to the corresponding cone of `mapNames j z`. -/
theorem baseChange_memCone {V E : Type u} [NontrivialCompleteBooleanAlgebra V]
    [NontrivialCompleteBooleanAlgebra E] (j : CompleteLatticeHom V E) (Q z : bSet V) :
    BaseChange.hom j Q
      (⨆ p : {p : Condition Q // p.value ≤ z ∈ᴮ name p},
        Erdos1172PosetCompletion.condition p.val) =
    ⨆ q : {q : Condition (mapNames j Q) // q.value ≤ mapNames j z ∈ᴮ name q},
      Erdos1172PosetCompletion.condition q.val := by
  let rhs := ⨆ q : {q : Condition (mapNames j Q) // q.value ≤ mapNames j z ∈ᴮ name q},
    Erdos1172PosetCompletion.condition q.val
  rw [_root_.map_iSup (BaseChange.hom j Q)]
  apply le_antisymm
  · refine iSup_le fun ⟨p, hp⟩ => ?_
    apply le_of_dense_conditions_le Set.univ (fun q => ⟨q, Set.mem_univ _, le_rfl⟩)
    rintro ⟨q, _⟩ hq
    by_contra hnot
    have hpos : Erdos1172PosetCompletion.condition q ⊓ rhsᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨q₁, hq₁⟩ := Erdos1172PosetCompletion.exists_condition_le hpos
    have hlow_le : Erdos1172PosetCompletion.condition (BaseChange.lower j Q q₁) ≤
        Erdos1172PosetCompletion.condition p :=
      (BaseChange.cone_le_hom j Q q₁ _).mp ((hq₁.trans inf_le_left).trans hq)
    obtain ⟨s, hs_q₁, hs_p⟩ :=
      (Erdos1172PosetCompletion.mem_condition_iff p (BaseChange.lower j Q q₁)).mp
        (Erdos1172PosetCompletion.condition_le_iff.mp hlow_le) (BaseChange.lower j Q q₁) le_rfl
    obtain ⟨r, hr_q₁, hr_eq⟩ := BaseChange.exactLifts j Q q₁ s hs_q₁
    have hs_z : s.value ≤ z ∈ᴮ name s := mem_of_mem_subset hs_p.2 (hs_p.1.trans hp)
    have hr_low : (BaseChange.lower j Q r).value ≤ z ∈ᴮ name (BaseChange.lower j Q r) := by
      have hsr : BaseChange.lower j Q r = s := hr_eq
      rw [hsr]
      exact hs_z
    have hr_z : r.value ≤ mapNames j z ∈ᴮ name r := by
      have h1 : r.value ≤ j (z ∈ᴮ name (BaseChange.lower j Q r)) :=
        (Erdos1172BooleanFactor.lowerProjection_le_iff j).mp
          ((BaseChange.lower_value j Q r).symm.le.trans hr_low)
      simpa only [map_mem, BaseChange.lower_name] using h1
    have hr_rhs : Erdos1172PosetCompletion.condition r ≤ rhs :=
      le_iSup (fun t : {t : Condition (mapNames j Q) // t.value ≤ mapNames j z ∈ᴮ name t} =>
        Erdos1172PosetCompletion.condition t.val) ⟨r, hr_z⟩
    have hr_not : Erdos1172PosetCompletion.condition r ≤ rhsᶜ :=
      (Erdos1172PosetCompletion.condition_mono hr_q₁).trans (hq₁.trans inf_le_right)
    exact Erdos1172PosetCompletion.condition_ne_bot r
      (le_bot_iff.mp ((le_inf hr_rhs hr_not).trans inf_compl_eq_bot.le))
  · refine iSup_le fun ⟨q, hq⟩ => ?_
    let p := BaseChange.lower j Q q
    have hq' : q.value ≤ j (z ∈ᴮ name p) := by
      have h1 : q.value ≤ mapNames j z ∈ᴮ name q := hq
      rwa [← BaseChange.lower_name j Q q, ← map_mem] at h1
    have hp_z : p.value ≤ z ∈ᴮ name p :=
      (BaseChange.lower_value j Q q).le.trans (Erdos1172BooleanFactor.lowerProjection_le j hq')
    have hloc : Erdos1172PosetCompletion.condition q ≤ BaseChange.hom j Q (Erdos1172PosetCompletion.condition p) :=
      (BaseChange.localized_cone j Q q).symm.le.trans inf_le_left
    exact hloc.trans (le_iSup (fun t : {t : Condition Q // t.value ≤ z ∈ᴮ name t} =>
      BaseChange.hom j Q (Erdos1172PosetCompletion.condition t.val)) ⟨p, hp_z⟩)

theorem baseChange_bitValue {V E : Type u} [NontrivialCompleteBooleanAlgebra V]
    [NontrivialCompleteBooleanAlgebra E] (j : CompleteLatticeHom V E) (P Y : PSet.{u}) :
    BaseChange.hom j (ErdosCohen.conditions (omegaOne : bSet V))
      (Erdos1172CohenIteration.bitValue (omegaOne : bSet V) (check P) (check Y)) =
    ⨆ q : {q : Condition (mapNames j (ErdosCohen.conditions (omegaOne : bSet V))) //
        q.value ≤ pair (check P) (check Y) ∈ᴮ name q},
      Erdos1172PosetCompletion.condition q.val := by
  have h := baseChange_memCone j (ErdosCohen.conditions (omegaOne : bSet V)) (pair (check P) (check Y))
  have heq_z : mapNames j (pair (check P) (check Y)) = pair (check P) (check Y) := by
    rw [map_pair, map_check, map_check]
  rw [heq_z] at h
  exact h

end BaseChangeMemCone

section AnonymousSourceCohenHom
variable {θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R] [Nonempty θ.ord.ToType]
local notation "Z" => FirstAlgebra θ
local notation "E" => JointForcing R θ.ord.ToType
local notation "src" => jointSourceHom (R := R) θ.ord.ToType

def matchedUpperHom (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne)) :
    CompleteLatticeHom (Erdos1172LevyCohen.Algebra θ)
      (Erdos1172BooleanNameIteration.Algebra (mapNames src (ErdosCohen.conditions (omegaOne : bSet R)))) :=
  (CompleteLatticeHom.OrderIso.toCompleteLatticeHom (changeEquivalentName same)).comp
    (BaseChange.hom K (ErdosCohen.conditions (omegaOne : bSet Z)))

def jointSourceCohenHom :
    CompleteLatticeHom (Erdos1172CohenIteration.omegaOneAlgebra R)
      (Erdos1172BooleanNameIteration.Algebra (mapNames src (ErdosCohen.conditions (omegaOne : bSet R)))) :=
  BaseChange.hom src (ErdosCohen.conditions (omegaOne : bSet R))

theorem jointSourceCohenHom_injective :
    Function.Injective (jointSourceCohenHom (θ := θ) (R := R)) :=
  BaseChange.hom_injective src (ErdosCohen.conditions (omegaOne : bSet R)) jointSourceHom_injective

omit [Nonempty θ.ord.ToType] in
private theorem matchedUpperHom_bitValue (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne))
    (P Y : PSet.{u}) :
    matchedUpperHom K same
      (Erdos1172CohenIteration.bitValue (omegaOne : bSet Z) (check P) (check Y)) =
    jointSourceCohenHom
      (Erdos1172CohenIteration.bitValue (omegaOne : bSet R) (check P) (check Y)) := by
  change changeEquivalentName same (BaseChange.hom K (ErdosCohen.conditions (omegaOne : bSet Z))
    (Erdos1172CohenIteration.bitValue (omegaOne : bSet Z) (check P) (check Y))) = _
  rw [baseChange_bitValue K P Y, changeEquivalentName_memCone same (pair (check P) (check Y))]
  exact (baseChange_bitValue src P Y).symm

omit [Nonempty θ.ord.ToType] in
private theorem matchedUpperHom_firstStage (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne))
    (z : Z) :
    matchedUpperHom K same (Erdos1172LevyCohen.firstStageHom θ z) =
      sourceHom (mapNames src (ErdosCohen.conditions (omegaOne : bSet R))) (K z) := by
  change changeEquivalentName same (BaseChange.hom K (ErdosCohen.conditions (omegaOne : bSet Z))
    (sourceHom (ErdosCohen.conditions (omegaOne : bSet Z)) z)) = _
  rw [BaseChange.commutes K (ErdosCohen.conditions (omegaOne : bSet Z)) z]
  exact changeEquivalentName_sourceHom same (K z)

omit [Nonempty θ.ord.ToType] in
private theorem jointSourceCohenHom_firstStage (r : R) :
    jointSourceCohenHom (θ := θ) (Erdos1172CohenIteration.omegaOneFirstStageHom r) =
      sourceHom (mapNames src (ErdosCohen.conditions (omegaOne : bSet R))) (src r) :=
  BaseChange.commutes src (ErdosCohen.conditions (omegaOne : bSet R)) r

omit [Nonempty θ.ord.ToType] in
theorem matchedUpperHom_mem_range (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne))
    (x : anonymousAlgebra θ) :
    matchedUpperHom K same (inclusion (anonymousAlgebra θ) x) ∈
      Set.range (jointSourceCohenHom (θ := θ) (R := R)) := by
  let hK := matchedUpperHom K same
  let hsrc := jointSourceCohenHom (θ := θ) (R := R)
  let S_pre : CompleteSubalgebra (Erdos1172LevyCohen.Algebra θ) :=
    { toCompleteSublattice := CompleteSublattice.mk'
        {b | hK b ∈ Set.range hsrc}
        (fun S hS => by
          have himg : hsrc '' (hsrc ⁻¹' (hK '' S)) = hK '' S := by
            apply Set.Subset.antisymm (Set.image_preimage_subset hsrc (hK '' S))
            rintro _ ⟨b, hb, rfl⟩
            obtain ⟨y, hy⟩ := hS hb
            exact ⟨y, ⟨b, hb, hy.symm⟩, hy⟩
          refine ⟨sSup (hsrc ⁻¹' (hK '' S)), ?_⟩
          rw [sSupHomClass.map_sSup, himg, ← sSupHomClass.map_sSup])
        (fun S hS => by
          have himg : hsrc '' (hsrc ⁻¹' (hK '' S)) = hK '' S := by
            apply Set.Subset.antisymm (Set.image_preimage_subset hsrc (hK '' S))
            rintro _ ⟨b, hb, rfl⟩
            obtain ⟨y, hy⟩ := hS hb
            exact ⟨y, ⟨b, hb, hy.symm⟩, hy⟩
          refine ⟨sInf (hsrc ⁻¹' (hK '' S)), ?_⟩
          rw [sInfHomClass.map_sInf, himg, ← sInfHomClass.map_sInf])
      compl_mem' := by
        rintro b ⟨y, hy⟩
        refine ⟨yᶜ, ?_⟩
        let : CompleteBooleanAlgebra
            (Erdos1172BooleanNameIteration.Algebra
              (mapNames src (ErdosCohen.conditions (omegaOne : bSet R)))) :=
          completionCompleteBooleanAlgebra
        rw [completeHom_compl hsrc, completeHom_compl hK, hy] }
  have hle : anonymousAlgebra θ ≤ S_pre := by
    rw [anonymousAlgebra_le_iff θ S_pre]
    intro i
    exact ⟨Erdos1172CohenIteration.bitValue (omegaOne : bSet R)
        (check ((PSet.ordinalMk θ.ord).Func i)) (1 : bSet R),
      (matchedUpperHom_bitValue K same ((PSet.ordinalMk θ.ord).Func i) (PSet.ofNat 1)).symm⟩
  exact hle x.property

/-- Complete Boolean embedding of `anonymousAlgebra θ` into `Erdos1172CohenIteration.omegaOneAlgebra R`,
avoiding any surviving external `Col(ω, θ)` factor. -/
def anonymousSourceCohenHom (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne)) :
    CompleteLatticeHom (anonymousAlgebra θ) (Erdos1172CohenIteration.omegaOneAlgebra R) where
  toFun x := (matchedUpperHom_mem_range K same x).choose
  map_sSup' S := by
    apply jointSourceCohenHom_injective (θ := θ) (R := R)
    rw [(matchedUpperHom_mem_range K same (sSup S)).choose_spec, inclusion_sSup,
      sSupHomClass.map_sSup, sSupHomClass.map_sSup, Set.image_image, Set.image_image]
    congr 1
    ext w
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (matchedUpperHom_mem_range K same x).choose_spec⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (matchedUpperHom_mem_range K same x).choose_spec.symm⟩
  map_sInf' S := by
    apply jointSourceCohenHom_injective (θ := θ) (R := R)
    rw [(matchedUpperHom_mem_range K same (sInf S)).choose_spec, inclusion_sInf,
      sInfHomClass.map_sInf, sInfHomClass.map_sInf, Set.image_image, Set.image_image]
    congr 1
    ext w
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (matchedUpperHom_mem_range K same x).choose_spec⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (matchedUpperHom_mem_range K same x).choose_spec.symm⟩

theorem jointSourceCohenHom_anonymousSourceCohenHom (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne))
    (x : anonymousAlgebra θ) :
    jointSourceCohenHom (θ := θ) (anonymousSourceCohenHom K same x) =
      matchedUpperHom K same (inclusion (anonymousAlgebra θ) x) :=
  (matchedUpperHom_mem_range K same x).choose_spec

theorem anonymousSourceCohenHom_subset (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne)) :
    mapNames (anonymousSourceCohenHom K same) (anonymousSubset θ) =
      Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord) := by
  change bSet.mk (PSet.ordinalMk θ.ord).Type
      (fun i => mapNames (anonymousSourceCohenHom K same)
        (check ((PSet.ordinalMk θ.ord).Func i) : bSet (anonymousAlgebra θ)))
      (fun i => anonymousSourceCohenHom K same
        ⟨(check ((PSet.ordinalMk θ.ord).Func i) : bSet (Erdos1172LevyCohen.Algebra θ)) ∈ᴮ
          Erdos1172CohenIteration.subsetName (B := Z) (PSet.ordinalMk θ.ord),
         Erdos1172CompleteSubalgebra.subset_generated ⟨i, rfl⟩⟩) =
    bSet.mk (PSet.ordinalMk θ.ord).Type
      (fun i => (check ((PSet.ordinalMk θ.ord).Func i) : bSet (Erdos1172CohenIteration.omegaOneAlgebra R)))
      (fun i => Erdos1172CohenIteration.bitValue (omegaOne : bSet R)
        (check ((PSet.ordinalMk θ.ord).Func i)) (1 : bSet R))
  have hchk : (fun i => mapNames (anonymousSourceCohenHom K same)
      (check ((PSet.ordinalMk θ.ord).Func i) : bSet (anonymousAlgebra θ))) =
      fun i => (check ((PSet.ordinalMk θ.ord).Func i) : bSet (Erdos1172CohenIteration.omegaOneAlgebra R)) :=
    funext fun i => map_check _ _
  rw [hchk]
  congr 1
  funext i
  apply jointSourceCohenHom_injective (θ := θ) (R := R)
  rw [jointSourceCohenHom_anonymousSourceCohenHom K same]
  change matchedUpperHom K same
      ((check ((PSet.ordinalMk θ.ord).Func i) : bSet (Erdos1172LevyCohen.Algebra θ)) ∈ᴮ
        Erdos1172CohenIteration.subsetName (B := Z) (PSet.ordinalMk θ.ord)) = _
  rw [Erdos1172CohenIteration.subsetName_member_eq_bitValue (PSet.ordinalMk_inj θ.ord) i]
  exact matchedUpperHom_bitValue K same ((PSet.ordinalMk θ.ord).Func i) (PSet.ofNat 1)

end AnonymousSourceCohenHom

section MasterLocalization
variable {R : Type u} [NontrivialCompleteBooleanAlgebra R]

theorem masterNameCone_ne_bot (m₀ : bSet R) (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀) :
    nameCone (ErdosCohen.conditions (omegaOne : bSet R)) m₀ ≠ ⊥ := by
  have hmem : (⊤ : R) ≤ m₀ ∈ᴮ ErdosCohen.conditions (omegaOne : bSet R) :=
    ErdosCohen.mem_conditions_iff.mpr hm₀
  obtain ⟨p, _, hpeq⟩ := exists_canonical_refinement (top_ne_bot : (⊤ : R) ≠ ⊥) hmem
  intro h0
  have hle : Erdos1172PosetCompletion.condition p ≤
      nameCone (ErdosCohen.conditions (omegaOne : bSet R)) m₀ :=
    le_iSup (fun r : {r : Erdos1172CohenIteration.Conditions (omegaOne : bSet R) //
      r.value ≤ m₀ =ᴮ name r} => Erdos1172PosetCompletion.condition r.val) ⟨p, hpeq⟩
  exact Erdos1172PosetCompletion.condition_ne_bot p (le_bot_iff.mp (hle.trans_eq h0))

/-- Positive element `nameCone (ErdosCohen.conditions omegaOne) m₀` in `omegaOneAlgebra R`
associated with a valid first-stage Cohen condition `m₀ : bSet R`. -/
def masterPositive (m₀ : bSet R) (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀) :
    Positive (Erdos1172CohenIteration.omegaOneAlgebra R) :=
  ⟨nameCone (ErdosCohen.conditions (omegaOne : bSet R)) m₀, masterNameCone_ne_bot m₀ hm₀⟩

/-- Principal-ideal localization of `Erdos1172CohenIteration.omegaOneAlgebra R` below `masterPositive m₀ hm₀`. -/
abbrev LocalizedSourceCohen (R : Type u) [NontrivialCompleteBooleanAlgebra R]
    (m₀ : bSet R) (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀) : Type u :=
  LocalizedBelow (Erdos1172CohenIteration.omegaOneAlgebra R) (masterPositive m₀ hm₀)

/-- Canonical first-stage embedding `R → LocalizedSourceCohen R m₀ hm₀`. -/
def localizedFirstStageHom {m₀ : bSet R} (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀) :
    CompleteLatticeHom R (LocalizedSourceCohen R m₀ hm₀) :=
  (LocalizedBelow.restrict (masterPositive m₀ hm₀)).comp
    Erdos1172CohenIteration.omegaOneFirstStageHom

end MasterLocalization

section StageOneScalarHom
variable {I : Type u} {κ θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R]
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable [CardinalInterFilter (U : Filter I) κ]
variable (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
variable (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
variable (u : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) R)

local notation "Z" => FirstAlgebra θ
local notation "E" => JointForcing R θ.ord.ToType
local notation "src" => jointSourceHom (R := R) θ.ord.ToType

/-- Stage-1 scalar embedding of the bounded anonymous ultrapower `Algebra U (anonymousAlgebra κ)`
into `LocalizedSourceCohen R (sourceCohenMaster u) hm₀`. -/
def stageOneScalarHom
    (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne))
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u)) :
    CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen R (sourceCohenMaster u) hm₀) :=
  (LocalizedBelow.restrict (masterPositive (sourceCohenMaster u) hm₀)).comp
    ((anonymousSourceCohenHom K same).comp
      (Preparation.anonymousUltrapowerHom U a hk.le hf hn ht hκ hθ))

private theorem inf_eq_of_split {α : Type u} [BooleanAlgebra α] {c x y : α}
    (h1 : c ⊓ y ≤ x) (h0 : c ⊓ yᶜ ≤ xᶜ) : c ⊓ x = c ⊓ y := by
  apply le_antisymm
  · calc
      c ⊓ x = (c ⊓ x) ⊓ (y ⊔ yᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = ((c ⊓ x) ⊓ y) ⊔ ((c ⊓ x) ⊓ yᶜ) := inf_sup_left _ _ _
      _ ≤ (c ⊓ y) ⊔ (x ⊓ xᶜ) := by
        refine sup_le_sup (inf_le_inf_right y inf_le_left) ?_
        have hcomm : (c ⊓ x) ⊓ yᶜ = x ⊓ (c ⊓ yᶜ) := by ac_rfl
        rw [hcomm]
        exact inf_le_inf_left x h0
      _ = c ⊓ y := by rw [inf_compl_eq_bot, sup_bot_eq]
  · exact le_inf inf_le_left h1

private theorem master_bitValue_agreement
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u))
    (k : κ.ord.ToType) :
    Erdos1172CohenIteration.bitValue (omegaOne : bSet R)
        (check (PSet.ordinalMk k.toOrd.val)) (1 : bSet R) ⊓
      (masterPositive (sourceCohenMaster u) hm₀).val =
    Erdos1172CohenIteration.omegaOneFirstStageHom (u (Preparation.levyCohenBit κ k)) ⊓
      (masterPositive (sourceCohenMaster u) hm₀).val := by
  let m₀ := sourceCohenMaster u
  let M₀ := (masterPositive m₀ hm₀).val
  let X := Erdos1172CohenIteration.bitValue (omegaOne : bSet R)
    (check (PSet.ordinalMk k.toOrd.val)) (1 : bSet R)
  let b₁ := u (Preparation.levyCohenBit κ k)
  let Y := Erdos1172CohenIteration.omegaOneFirstStageHom b₁
  obtain ⟨i, hi⟩ := PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt (show k.toOrd.val < κ.ord from k.toOrd.property))
  have hchk_κ : (⊤ : FirstAlgebra κ) ≤
      check ((PSet.ordinalMk κ.ord).Func i) =ᴮ check (PSet.ordinalMk k.toOrd.val) :=
    check_bv_eq (PSet.Equiv.symm hi)
  have hchk_R : (⊤ : R) ≤
      check ((PSet.ordinalMk κ.ord).Func i) =ᴮ check (PSet.ordinalMk k.toOrd.val) :=
    check_bv_eq (PSet.Equiv.symm hi)
  have hbit_eq : Erdos1172CohenIteration.bitValue (omegaOne : bSet (FirstAlgebra κ))
        (check ((PSet.ordinalMk κ.ord).Func i)) 1 = Preparation.levyCohenBit κ k := by
    unfold Preparation.levyCohenBit Erdos1172CohenIteration.bitValue
    apply le_antisymm
    · refine iSup_le fun ⟨p, hp⟩ => Erdos1172CohenIteration.condition_le_bitValue ?_
      exact mem_congr (pair_congr (le_top.trans hchk_κ) bv_refl) bv_refl hp
    · refine iSup_le fun ⟨p, hp⟩ => Erdos1172CohenIteration.condition_le_bitValue ?_
      exact mem_congr (pair_congr (le_top.trans (bv_symm hchk_κ)) bv_refl) bv_refl hp
  have hm₀_one : b₁ ≤ pair (check (PSet.ordinalMk k.toOrd.val)) (1 : bSet R) ∈ᴮ m₀ := by
    have h1 := indexedBinaryAssignment_one (PSet.ordinalMk κ.ord)
      (fun j => u (Erdos1172CohenIteration.bitValue (omegaOne : bSet (FirstAlgebra κ))
        (check ((PSet.ordinalMk κ.ord).Func j)) 1))
      (PSet.ordinalMk_inj κ.ord) i
    rw [hbit_eq] at h1
    exact mem_congr (pair_congr (le_top.trans hchk_R) bv_refl) bv_refl h1
  have hm₀_zero : b₁ᶜ ≤ pair (check (PSet.ordinalMk k.toOrd.val)) (0 : bSet R) ∈ᴮ m₀ := by
    have h0 := indexedBinaryAssignment_zero (PSet.ordinalMk κ.ord)
      (fun j => u (Erdos1172CohenIteration.bitValue (omegaOne : bSet (FirstAlgebra κ))
        (check ((PSet.ordinalMk κ.ord).Func j)) 1))
      (PSet.ordinalMk_inj κ.ord) i
    rw [hbit_eq] at h0
    exact mem_congr (pair_congr (le_top.trans hchk_R) bv_refl) bv_refl h0
  change X ⊓ M₀ = Y ⊓ M₀
  erw [inf_comm_eq X M₀, inf_comm_eq Y M₀]
  change (⨆ p : {p : Erdos1172CohenIteration.Conditions (omegaOne : bSet R) //
      p.value ≤ m₀ =ᴮ name p}, Erdos1172PosetCompletion.condition p.val) ⊓ X =
    (⨆ p : {p : Erdos1172CohenIteration.Conditions (omegaOne : bSet R) //
      p.value ≤ m₀ =ᴮ name p}, Erdos1172PosetCompletion.condition p.val) ⊓ Y
  erw [iSup_inf_eq, iSup_inf_eq]
  refine iSup_congr fun ⟨p, hp⟩ => ?_
  have hp_one : Erdos1172PosetCompletion.condition p ⊓ Y ≤ X := by
    by_contra hnot
    have hpos : (Erdos1172PosetCompletion.condition p ⊓ Y) ⊓ Xᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨r, hr⟩ := Erdos1172PosetCompletion.exists_condition_le hpos
    obtain ⟨s, hs_r, hs_p⟩ :=
      (Erdos1172PosetCompletion.mem_condition_iff p r).mp
        (Erdos1172PosetCompletion.condition_le_iff.mp ((hr.trans inf_le_left).trans inf_le_left)) r le_rfl
    have hs_b₁ : s.value ≤ b₁ :=
      hs_r.1.trans ((Erdos1172CohenIteration.condition_le_firstStageHom_iff _ r b₁).mp
        ((hr.trans inf_le_left).trans inf_le_right))
    have hs_m₀ : s.value ≤ pair (check (PSet.ordinalMk k.toOrd.val)) (1 : bSet R) ∈ᴮ name p :=
      mem_congr bv_refl (hs_p.1.trans hp) (hs_b₁.trans hm₀_one)
    have hs_nm : s.value ≤ pair (check (PSet.ordinalMk k.toOrd.val)) (1 : bSet R) ∈ᴮ name s :=
      mem_of_mem_subset hs_p.2 hs_m₀
    have hs_X : Erdos1172PosetCompletion.condition s ≤ X :=
      Erdos1172CohenIteration.condition_le_bitValue hs_nm
    have hs_Xc : Erdos1172PosetCompletion.condition s ≤ Xᶜ :=
      (Erdos1172PosetCompletion.condition_mono hs_r).trans (hr.trans inf_le_right)
    exact Erdos1172PosetCompletion.condition_ne_bot s
      (le_bot_iff.mp ((le_inf hs_X hs_Xc).trans inf_compl_eq_bot.le))
  have hp_zero : Erdos1172PosetCompletion.condition p ⊓ Yᶜ ≤ Xᶜ := by
    by_contra hnot
    have hpos : (Erdos1172PosetCompletion.condition p ⊓ Yᶜ) ⊓ X ≠ ⊥ := fun h0 =>
      hnot (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h0))
    obtain ⟨r, hr⟩ := Erdos1172PosetCompletion.exists_condition_le hpos
    obtain ⟨s, hs_r, hs_p⟩ :=
      (Erdos1172PosetCompletion.mem_condition_iff p r).mp
        (Erdos1172PosetCompletion.condition_le_iff.mp ((hr.trans inf_le_left).trans inf_le_left)) r le_rfl
    have hr_Yc : Erdos1172PosetCompletion.condition r ≤ Erdos1172CohenIteration.omegaOneFirstStageHom b₁ᶜ := by
      rw [Erdos1172CohenIteration.omegaOneFirstStageHom_compl]
      exact (hr.trans inf_le_left).trans inf_le_right
    have hs_b₀ : s.value ≤ b₁ᶜ :=
      hs_r.1.trans ((Erdos1172CohenIteration.condition_le_firstStageHom_iff _ r b₁ᶜ).mp hr_Yc)
    have hs_m₀ : s.value ≤ pair (check (PSet.ordinalMk k.toOrd.val)) (0 : bSet R) ∈ᴮ name p :=
      mem_congr bv_refl (hs_p.1.trans hp) (hs_b₀.trans hm₀_zero)
    have hs_nm : s.value ≤ pair (check (PSet.ordinalMk k.toOrd.val)) (0 : bSet R) ∈ᴮ name s :=
      mem_of_mem_subset hs_p.2 hs_m₀
    have hs_0 : Erdos1172PosetCompletion.condition s ≤
        Erdos1172CohenIteration.bitValue (omegaOne : bSet R) (check (PSet.ordinalMk k.toOrd.val)) 0 :=
      Erdos1172CohenIteration.condition_le_bitValue hs_nm
    have hs_1 : Erdos1172PosetCompletion.condition s ≤ X :=
      (Erdos1172PosetCompletion.condition_mono hs_r).trans (hr.trans inf_le_right)
    exact Erdos1172PosetCompletion.condition_ne_bot s
      (le_bot_iff.mp ((le_inf hs_0 hs_1).trans
        (Erdos1172CohenIteration.bitValue_zero_inf_one_eq_bot _ _).le))
  exact inf_eq_of_split hp_one hp_zero

private theorem completeHom_bitiff {X Y : Type u} [CompleteBooleanAlgebra X] [CompleteBooleanAlgebra Y]
    (e : CompleteLatticeHom X Y) (x y : X) :
    e (Preparation.bitiff x y) = Preparation.bitiff (e x) (e y) := by
  simp only [Preparation.bitiff, completeHom_sup, completeHom_inf, completeHom_compl]

include hk hf hn ht in
/-- Exact agreement on constant germs: for every `b : anonymousAlgebra κ`, `stageOneScalarHom`
maps `value U (fun _ => b)` to `localizedFirstStageHom hm₀ (u (inclusion _ b))`. -/
theorem stageOneBase
    (K : CompleteLatticeHom Z E)
    (square : ∀ x : FirstAlgebra κ, K (initialCollapseHom hk.le x) = src (u (Erdos1172LevyCohen.firstStageHom κ x)))
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne))
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u))
    (b : anonymousAlgebra κ) :
    stageOneScalarHom U a hk hκ hθ hf hn ht u K same hm₀ (value U (fun _ => b)) =
      localizedFirstStageHom hm₀ (u (inclusion (anonymousAlgebra κ) b)) := by
  let W_E := Erdos1172BooleanNameIteration.Algebra
    (mapNames src (ErdosCohen.conditions (omegaOne : bSet R)))
  let cba_WE : CompleteBooleanAlgebra W_E := completionCompleteBooleanAlgebra
  let hK := matchedUpperHom K same
  let hsrc := jointSourceCohenHom (θ := θ) (R := R)
  let M₀ := masterPositive (sourceCohenMaster u) hm₀
  have hME_ne : hsrc M₀.val ≠ ⊥ := fun h0 =>
    M₀.property (jointSourceCohenHom_injective (θ := θ) (R := R) (h0.trans (BotHomClass.map_bot hsrc).symm))
  let M_E : Positive W_E := ⟨hsrc M₀.val, hME_ne⟩
  let ρ_E : CompleteLatticeHom W_E (LocalizedBelow W_E M_E) := LocalizedBelow.restrict M_E
  let ψ := Preparation.levyCohenUltrapowerIso U a hk.le hf hn ht hκ hθ
  let ψ_hom : CompleteLatticeHom
      (Erdos1172BooleanUltrapower.Algebra U (Erdos1172LevyCohen.Algebra κ))
      (Erdos1172LevyCohen.Algebra θ) :=
    CompleteLatticeHom.OrderIso.toCompleteLatticeHom ψ
  let Φ₁ (c : Erdos1172LevyCohen.Algebra κ) : LocalizedBelow W_E M_E :=
    ρ_E (hK (ψ (value U (fun _ => c))))
  let Φ₂ : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) (LocalizedBelow W_E M_E) :=
    ρ_E.comp (hsrc.comp (Erdos1172CohenIteration.omegaOneFirstStageHom.comp u))
  have hΦ_first (x : FirstAlgebra κ) :
      ρ_E (hK (Erdos1172LevyCohen.firstStageHom θ (initialCollapseHom hk.le x))) =
        Φ₂ (Erdos1172LevyCohen.firstStageHom κ x) := by
    change ρ_E (hK (Erdos1172LevyCohen.firstStageHom θ (initialCollapseHom hk.le x))) =
      ρ_E (hsrc (Erdos1172CohenIteration.omegaOneFirstStageHom (u (Erdos1172LevyCohen.firstStageHom κ x))))
    rw [matchedUpperHom_firstStage K same (initialCollapseHom hk.le x), square x,
      ← jointSourceCohenHom_firstStage]
  have hΦ_bit (k : κ.ord.ToType) :
      ρ_E (hK (Preparation.levyCohenBit θ (initialCoordinate hk.le k))) =
        Φ₂ (Preparation.levyCohenBit κ k) := by
    apply Subtype.ext
    change hK (Preparation.levyCohenBit θ (initialCoordinate hk.le k)) ⊓ hsrc M₀.val =
      hsrc (Erdos1172CohenIteration.omegaOneFirstStageHom (u (Preparation.levyCohenBit κ k))) ⊓ hsrc M₀.val
    have hbit_θ : Preparation.levyCohenBit θ (initialCoordinate hk.le k) =
        Erdos1172CohenIteration.bitValue (omegaOne : bSet Z)
          (check (PSet.ordinalMk k.toOrd.val)) (check (PSet.ofNat 1)) := by
      unfold Preparation.levyCohenBit
      rw [initialCoordinate_ordinal hk.le k]
      rfl
    rw [hbit_θ, matchedUpperHom_bitValue K same (PSet.ordinalMk k.toOrd.val) (PSet.ofNat 1)]
    erw [← completeHom_inf hsrc _ _, ← completeHom_inf hsrc _ _]
    exact congrArg hsrc (master_bitValue_agreement u hm₀ k)
  have hΦ_realize (q : Erdos1172Shioya.CohenCover.Condition κ (FirstAlgebra κ)) :
      Φ₁ (Preparation.realizeCondition (Erdos1172LevyCohen.firstStageHom κ)
        (Preparation.levyCohenBit κ) q) =
      Φ₂ (Preparation.realizeCondition (Erdos1172LevyCohen.firstStageHom κ)
        (Preparation.levyCohenBit κ) q) := by
    change (ρ_E.comp hK) (ψ (value U (fun _ =>
        Preparation.realizeCondition (Erdos1172LevyCohen.firstStageHom κ)
          (Preparation.levyCohenBit κ) q))) = _
    rw [Preparation.levyCohenUltrapowerIso_constant_realize U a hk.le hf hn ht hκ hθ q]
    unfold Preparation.realizeCondition
    rw [completeHom_inf (ρ_E.comp hK), completeHom_inf Φ₂, _root_.map_iInf (ρ_E.comp hK),
      _root_.map_iInf Φ₂]
    have hv : (ρ_E.comp hK) (Erdos1172LevyCohen.firstStageHom θ
        (Preparation.initialLiftCoverCondition hk.le q).value) =
        Φ₂ (Erdos1172LevyCohen.firstStageHom κ q.value) :=
      hΦ_first q.value
    rw [hv]
    apply congrArg (_ ⊓ ·)
    have hlen_ord : (Preparation.initialLiftCoverCondition hk.le q).length.toOrd.val =
        q.length.toOrd.val :=
      initialCoordinate_ordinal hk.le q.length
    let eqv : q.length.toOrd.val.ToType ≃
        (Preparation.initialLiftCoverCondition hk.le q).length.toOrd.val.ToType :=
      ⟨fun j => Ordinal.ToType.mk ⟨j.toOrd.val,
          (show j.toOrd.val < q.length.toOrd.val from j.toOrd.property).trans_eq hlen_ord.symm⟩,
       fun j => Ordinal.ToType.mk ⟨j.toOrd.val,
          (show j.toOrd.val < (Preparation.initialLiftCoverCondition hk.le q).length.toOrd.val from
            j.toOrd.property).trans_eq hlen_ord⟩,
       fun j => by
         let z := Ordinal.ToType.mk
           (o := (Preparation.initialLiftCoverCondition hk.le q).length.toOrd.val)
           ⟨j.toOrd.val, (show j.toOrd.val < q.length.toOrd.val from j.toOrd.property).trans_eq hlen_ord.symm⟩
         have hz : z.toOrd.val = j.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
         apply Ordinal.ToType.mk.symm.injective
         exact (Ordinal.ToType.mk.symm_apply_apply _).trans (Subtype.ext hz),
       fun j => by
         let z := Ordinal.ToType.mk (o := q.length.toOrd.val)
           ⟨j.toOrd.val, (show j.toOrd.val < (Preparation.initialLiftCoverCondition hk.le q).length.toOrd.val from
             j.toOrd.property).trans_eq hlen_ord⟩
         have hz : z.toOrd.val = j.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
         apply Ordinal.ToType.mk.symm.injective
         exact (Ordinal.ToType.mk.symm_apply_apply _).trans (Subtype.ext hz)⟩
    rw [← eqv.iInf_comp]
    refine iInf_congr fun j => ?_
    rw [completeHom_bitiff (ρ_E.comp hK), completeHom_bitiff Φ₂]
    have heqv_ord : (eqv j).toOrd.val = j.toOrd.val :=
      congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
    have hbits_eq : (Preparation.initialLiftCoverCondition hk.le q).bits (eqv j) =
        initialCollapseHom hk.le (q.bits j) := by
      dsimp only [Preparation.initialLiftCoverCondition]
      apply congrArg (initialCollapseHom hk.le)
      apply congrArg q.bits
      apply Ordinal.ToType.mk.symm.injective
      exact (Ordinal.ToType.mk.symm_apply_apply _).trans (Subtype.ext heqv_ord)
    let k_j := Erdos1172Shioya.StringName.includeIndex q.length.toOrd.property.le j
    have hinc_eq : Erdos1172Shioya.StringName.includeIndex
        (Preparation.initialLiftCoverCondition hk.le q).length.toOrd.property.le (eqv j) =
        initialCoordinate hk.le k_j := by
      apply Ordinal.ToType.mk.symm.injective
      exact Subtype.ext ((Erdos1172Shioya.StringName.includeIndex_toOrd _ _).trans
        (heqv_ord.trans ((Erdos1172Shioya.StringName.includeIndex_toOrd _ _).symm.trans
          (initialCoordinate_ordinal hk.le k_j).symm)))
    rw [hbits_eq, hinc_eq]
    exact congrArg₂ Preparation.bitiff (hΦ_first (q.bits j)) (hΦ_bit k_j)
  have hΦ₁_mono : Monotone Φ₁ := by
    intro c₁ c₂ hc
    have hv : value U (fun _ => c₁) ≤ value U (fun _ => c₂) :=
      (value_le_value_iff U).mpr (Eventually.of_forall fun _ => hc)
    exact OrderHomClass.mono (ρ_E.comp hK) (ψ.monotone hv)
  have hΦ₁_compl (c : Erdos1172LevyCohen.Algebra κ) : Φ₁ cᶜ = (Φ₁ c)ᶜ := by
    change (ρ_E.comp hK) (ψ_hom (value U (fun _ => cᶜ))) = ((ρ_E.comp hK) (ψ_hom (value U (fun _ => c))))ᶜ
    rw [value_compl, completeHom_compl ψ_hom, completeHom_compl (ρ_E.comp hK)]
  have hΦ₂_le_Φ₁ (c : Erdos1172LevyCohen.Algebra κ) : Φ₂ c ≤ Φ₁ c := by
    let rz := Preparation.realizeCondition (Erdos1172LevyCohen.firstStageHom κ)
      (Preparation.levyCohenBit κ)
    have hcov : c = ⨆ q : {q : Erdos1172Shioya.CohenCover.Condition κ (FirstAlgebra κ) // rz q ≤ c},
        rz q.val := by
      apply le_antisymm ?_ (iSup_le fun q => q.property)
      by_contra hnot
      let sup_q := ⨆ q : {q : Erdos1172Shioya.CohenCover.Condition κ (FirstAlgebra κ) // rz q ≤ c}, rz q.val
      have hpos : c ⊓ sup_qᶜ ≠ ⊥ := fun h0 =>
        hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
      obtain ⟨q, hq⟩ := Preparation.levyCohenRealize_dense κ hκ hpos
      have hq_sup : rz q ≤ sup_q :=
        le_iSup (fun t : {t // rz t ≤ c} => rz t.val) ⟨q, hq.trans inf_le_left⟩
      exact Preparation.levyCohenRealize_ne_bot κ hκ q
        (le_bot_iff.mp ((le_inf hq_sup (hq.trans inf_le_right)).trans inf_compl_eq_bot.le))
    conv_lhs => rw [hcov]
    rw [_root_.map_iSup Φ₂]
    refine iSup_le fun ⟨q, hq⟩ => ?_
    rw [← hΦ_realize q]
    exact hΦ₁_mono hq
  have hΦ_eq (c : Erdos1172LevyCohen.Algebra κ) : Φ₁ c = Φ₂ c := by
    refine le_antisymm ?_ (hΦ₂_le_Φ₁ c)
    have hc := hΦ₂_le_Φ₁ cᶜ
    rw [completeHom_compl Φ₂, hΦ₁_compl] at hc
    exact compl_le_compl_iff_le.mp hc
  have h_b := congrArg Subtype.val (hΦ_eq (inclusion (anonymousAlgebra κ) b))
  change hK (ψ (value U (fun _ => inclusion (anonymousAlgebra κ) b))) ⊓ hsrc M₀.val =
    hsrc (Erdos1172CohenIteration.omegaOneFirstStageHom (u (inclusion (anonymousAlgebra κ) b))) ⊓ hsrc M₀.val at h_b
  apply Subtype.ext
  apply jointSourceCohenHom_injective (θ := θ) (R := R)
  change hsrc ((anonymousSourceCohenHom K same
      (Preparation.anonymousUltrapowerHom U a hk.le hf hn ht hκ hθ (value U (fun _ => b)))) ⊓ M₀.val) =
    hsrc (Erdos1172CohenIteration.omegaOneFirstStageHom (u (inclusion (anonymousAlgebra κ) b)) ⊓ M₀.val)
  erw [completeHom_inf hsrc _ _, completeHom_inf hsrc _ _]
  rw [jointSourceCohenHom_anonymousSourceCohenHom K same,
    Preparation.inclusion_anonymousUltrapowerHom, scalarHom_value]
  exact h_b

omit [CardinalInterFilter (U : Filter I) κ] in
include hk hf hn ht in
/-- `stageOneScalarHom` sends the bounded ultrapower lift of `anonymousSubset κ` to the
canonical generic subset `subsetName (PSet.ordinalMk θ.ord)` restricted to `LocalizedSourceCohen`. -/
theorem stageOneSubsetEq
    (K : CompleteLatticeHom Z E)
    (same : (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ
      mapNames src (ErdosCohen.conditions omegaOne))
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u)) :
    (⊤ : LocalizedSourceCohen R (sourceCohenMaster u) hm₀) ≤
      mapNames (stageOneScalarHom U a hk hκ hθ hf hn ht u K same hm₀)
        (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =ᴮ
      mapNames (LocalizedBelow.restrict (masterPositive (sourceCohenMaster u) hm₀))
        (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord)) := by
  let j_anon := Preparation.anonymousUltrapowerHom U a hk.le hf hn ht hκ hθ
  let j_src := anonymousSourceCohenHom K same
  let ρ := LocalizedBelow.restrict (masterPositive (sourceCohenMaster u) hm₀)
  have h1 := OrderHomClass.mono (ρ.comp j_src)
    (Preparation.anonymousUltrapowerHom_subset U a hk.le hf hn ht hκ hθ)
  rw [TopHomClass.map_top, map_bv_eq (ρ.comp j_src)] at h1
  have h2 : mapNames (ρ.comp j_src) (anonymousSubset θ) =
      mapNames ρ (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord)) := by
    rw [mapNames_comp, anonymousSourceCohenHom_subset K same]
  change (⊤ : LocalizedSourceCohen R (sourceCohenMaster u) hm₀) ≤
    mapNames ((ρ.comp j_src).comp j_anon) (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =ᴮ
      mapNames ρ (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord))
  rw [mapNames_comp, ← h2]
  exact h1

include hk hκ hθ hf hn ht in
/-- Combined existence of `hm₀` and `j₀ : CompleteLatticeHom (Algebra U (anonymousAlgebra κ)) (LocalizedSourceCohen ...)`
from a reasonable collapsing-stage decomposition `(B, b, g)` of `R`. -/
theorem exists_stageOne_anonymous_lift
    {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
    (b_hom : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
    (g : ∀ i, CompleteLatticeHom (B i) R)
    (cc : StrictCC R θ) (dense : DenseStageUnion g) (good : RegularCollapsingStages B)
    (ginj : ∀ i, Function.Injective (g i)) (gg : ∀ {i j} (h : i ≤ j) x, g j (b_hom h x) = g i x)
    (uinj : Function.Injective u) :
    ∃ (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u))
      (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
        (LocalizedSourceCohen R (sourceCohenMaster u) hm₀)),
      (∀ b : anonymousAlgebra κ,
        j₀ (value U (fun _ => b)) = localizedFirstStageHom hm₀ (u (inclusion (anonymousAlgebra κ) b))) ∧
      ((⊤ : LocalizedSourceCohen R (sourceCohenMaster u) hm₀) ≤
        mapNames j₀ (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =ᴮ
          mapNames (LocalizedBelow.restrict (masterPositive (sourceCohenMaster u) hm₀))
            (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord))) := by
  obtain ⟨K, _, square, same, hm₀, _, _⟩ :=
    exists_matching_bounded_source_master b_hom g U a hk hκ hθ hf hn ht u cc dense good ginj gg uinj
  exact ⟨hm₀, stageOneScalarHom U a hk hκ hθ hf hn ht u K same hm₀,
    stageOneBase U a hk hκ hθ hf hn ht u K square same hm₀,
    stageOneSubsetEq U a hk hκ hθ hf hn ht u K same hm₀⟩

end StageOneScalarHom

end Erdos1172LevyCollapse.Matching
