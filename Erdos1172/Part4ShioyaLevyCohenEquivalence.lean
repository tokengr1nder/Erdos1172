/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCodedStageTransport
public import Erdos1172.Part4ShioyaCohenCover
public import Erdos1172.Part4ShioyaDenseCoverIso
public import Erdos1172.Part4ShioyaLevyCardinalBounds

@[expose] public section

/-! # The stage presentation in the two-step Lévy and Cohen forcing

The image of a small stage condition is its positive Lévy value and the
translated string of coefficients. Every mixed string admits a strengthening
at an arbitrarily late bounded stage.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}} [Nonempty (Full κ θ)]
variable (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)
local notation "T" => stageSystem hκ hκθ hθ
local notation "B" => Completion (Full κ θ)
local notation "E" => stageToFull hκ hκθ hθ

def mixedCondition (a : (T).Entry) : CohenCover.Condition θ B where
  value := E a.stage (condition a.point)
  positive := fun he => condition_ne_bot a.point ((stageToFull_injective hκ hκθ hθ a.stage)
    (he.trans (map_bot (E a.stage)).symm))
  length := a.length
  bits i := E a.stage (a.bits i)

private theorem reflect_le {A D : Type u} [CompleteLattice A] [CompleteLattice D]
    (e : CompleteLatticeHom A D) (he : Function.Injective e) {x y : A} :
    e x ≤ e y ↔ x ≤ y := by
  refine ⟨fun h => inf_eq_left.mp (he ?_), fun h => OrderHomClass.mono e h⟩
  rw [← sInf_pair, map_sInf, Set.image_pair, sInf_pair, inf_eq_left.mpr h]

private theorem preserves_inf {A D : Type u} [CompleteLattice A] [CompleteLattice D]
    (e : CompleteLatticeHom A D) (x y : A) : e (x ⊓ y) = e x ⊓ e y := by
  rw [← sInf_pair, map_sInf, Set.image_pair, sInf_pair]

private theorem stage_criteria (a b : (T).Entry) (h : b.stage ≤ a.stage) :
    (mixedCondition hκ hκθ hθ a ≤ mixedCondition hκ hκθ hθ b) ↔
      condition a.point ≤ ((T).restrict h).booleanHom (condition b.point) ∧
      condition a.point ≤ extensionValue ((T).restrict h).booleanHom
        (b.forget T).name (a.forget T).name := by
  rw [CohenCover.Condition.le_iff]
  erw [extensionValue_iff_bits ((T).restrict h).booleanHom (b.forget T).name (a.forget T).name
    (condition_ne_bot a.point)]
  change
    (E a.stage (condition a.point) ≤ E b.stage (condition b.point) ∧
      ∃ hh : b.length.toOrd.val ≤ a.length.toOrd.val, ∀ i,
        E a.stage (condition a.point) ⊓ E b.stage (b.bits i) =
        E a.stage (condition a.point) ⊓ E a.stage (a.bits (StringName.includeIndex hh i))) ↔ _
  have hpoint := reflect_le (E a.stage) (stageToFull_injective hκ hκθ hθ a.stage)
    (x := condition a.point) (y := ((T).restrict h).booleanHom (condition b.point))
  have commute (v : ((T).base b.stage).Algebra) :
      E a.stage (((T).restrict h).booleanHom v) = E b.stage v :=
    stageToFull_restrict hκ hκθ hθ h v
  rw [commute] at hpoint
  apply and_congr hpoint
  apply exists_congr
  intro hh
  apply forall_congr'
  intro i
  have hb : (b.forget T).name.bits i = b.bits i := StringName.bits_ofBits _ i
  have ha : (a.forget T).name.bits (StringName.includeIndex hh i) =
      a.bits (StringName.includeIndex hh i) := StringName.bits_ofBits _ _
  have hmeet (x y : (stageBase hκ hκθ hθ a.stage).Algebra) :
      E a.stage (x ⊓ y) = E a.stage x ⊓ E a.stage y := preserves_inf (E a.stage) x y
  erw [hb, ha, ← commute, ← hmeet, ← hmeet]
  exact (stageToFull_injective hκ hκθ hθ a.stage).eq_iff

theorem stage_le_iff_mixed (a b : (T).Entry) :
    a ≤ b ↔ b.stage ≤ a.stage ∧ mixedCondition hκ hκθ hθ a ≤ mixedCondition hκ hκθ hθ b := by
  constructor
  · rintro ⟨h, hp, hs⟩
    exact ⟨h, (stage_criteria hκ hκθ hθ a b h).mpr ⟨hp, hs⟩⟩
  · rintro ⟨h, he⟩
    exact ⟨h, (stage_criteria hκ hκθ hθ a b h).mp he⟩

def mixedMap : (T).Entry →o CohenCover.Condition θ B :=
  ⟨mixedCondition hκ hκθ hθ, fun _ _ h => ((stage_le_iff_mixed hκ hκθ hθ _ _).mp h).2⟩

theorem mixed_dense_above (i : Index θ) (q : CohenCover.Condition θ B) :
    ∃ a : (T).Entry, i ≤ a.stage ∧ mixedMap hκ hκθ hθ a ≤ q := by
  obtain ⟨p, hp⟩ := exists_condition_le q.positive
  have hsize : Cardinal.mk q.length.toOrd.val.ToType < θ := by
    rw [Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp q.length.toOrd.property
  obtain ⟨j, hij, x, hx, g, hg⟩ := coded_bounded_reading_with_point hκ hκθ hθ hsize q.bits i p
  let a : (T).Entry := ⟨j, x, q.length, g⟩
  refine ⟨a, hij, (CohenCover.Condition.le_iff _ _).mpr ⟨hx.le.trans hp, le_rfl, ?_⟩⟩
  intro k
  have hk : StringName.includeIndex (le_refl q.length.toOrd.val) k = k :=
    Ordinal.ToType.mk.symm.injective (Subtype.ext (StringName.includeIndex_toOrd le_rfl k))
  change _ ⊓ q.bits k = _ ⊓ E j (g (StringName.includeIndex (le_refl q.length.toOrd.val) k))
  rw [hk, hg]

theorem mixedMap_lifts : ForcingCover.Lifts (mixedMap hκ hκθ hθ) := by
  intro a q hq
  obtain ⟨b, hab, hb⟩ := mixed_dense_above hκ hκθ hθ a.stage q
  exact ⟨b, (stage_le_iff_mixed hκ hκθ hθ b a).mpr ⟨hab, hb.trans hq⟩, hb⟩

theorem mixedMap_compatible (a b : (T).Entry) (hab : mixedMap hκ hκθ hθ a ≤ mixedMap hκ hκθ hθ b) :
    ∃ z ≤ a, z ≤ b := by
  obtain ⟨z, hz, hza⟩ := mixed_dense_above hκ hκθ hθ (max a.stage b.stage) (mixedMap hκ hκθ hθ a)
  exact ⟨z, (stage_le_iff_mixed hκ hκθ hθ z a).mpr ⟨(le_max_left _ _).trans hz, hza⟩,
    (stage_le_iff_mixed hκ hκθ hθ z b).mpr ⟨(le_max_right _ _).trans hz, hza.trans hab⟩⟩

def levyCohenStageIso : Completion (CohenCover.Condition θ B) ≃o Completion (T).Entry :=
  ForcingCover.completionIso (mixedMap hκ hκθ hθ) (mixedMap_lifts hκ hκθ hθ)
    (mixedMap_compatible hκ hκθ hθ) (fun q => by
      obtain ⟨a, _, ha⟩ := mixed_dense_above hκ hκθ hθ q.length q
      exact ⟨a, ha⟩)

variable [Fact (Cardinal.aleph0 < κ)]

def levyCohenCoverHom : CompleteLatticeHom (Algebra κ θ) (Completion (CohenCover.Condition θ B)) :=
  (CompleteLatticeHom.OrderIso.toCompleteLatticeHom (levyCohenStageIso hκ hκθ hθ).symm).comp
    (stageCoverHom hκ hκθ hθ)

theorem levyCohenCoverHom_injective : Function.Injective (levyCohenCoverHom hκ hκθ hθ) :=
  (levyCohenStageIso hκ hκθ hθ).symm.injective.comp (stageCoverHom_injective hκ hκθ hθ)

end Erdos1172Shioya.LevyProduct
