/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyCohenEquivalence
public import Erdos1172.Part4ShioyaCohenCardinalBounds

@[expose] public section

/-! # The same generic string in the cover and in Shioya forcing

A mixed Cohen condition decides a bit when its positive first-stage value
decides the corresponding string coefficient. On bounded stage conditions
these decisions agree exactly with those of the forgotten Shioya condition.
The complete embedding therefore identifies the whole generic string.
-/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion
open scoped Flypitch
universe u
namespace Erdos1172Shioya

namespace ForcingCover

/-- Pulling back the Boolean value of a downward-closed set of conditions
gives the Boolean value of its actual preimage under a forcing cover. -/
theorem booleanHom_lower_cones {S T : Type u} [Preorder S] [Preorder T] (f : S →o T)
    (hl : Lifts f) (D : Set T) (hD : IsLowerSet D) :
    booleanHom f hl (⨆ d : D, condition d.val) = ⨆ a : f ⁻¹' D, condition a.val := by
  let K := ⨆ a : f ⁻¹' D, condition a.val
  rw [map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro d
    by_contra h
    have hn : booleanHom f hl (condition d.val) ⊓ Kᶜ ≠ ⊥ :=
      fun he => h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨t, ht⟩ := exists_condition_le hn
    have hm' : t ∈ (booleanHom f hl (condition d.val)).val := condition_le_iff.mp (ht.trans inf_le_left)
    have hm : f t ∈ (condition d.val).val := hm'
    obtain ⟨z, hzt, hzd⟩ := (mem_condition_iff d.val (f t)).mp hm (f t) le_rfl
    obtain ⟨r, hrt, hrz⟩ := hl t z hzt
    have hr : condition r ≤ K := le_iSup (fun a : f ⁻¹' D => condition a.val) ⟨r, hD (hrz.trans hzd) d.property⟩
    exact condition_ne_bot r (bot_unique ((le_inf hr ((condition_mono hrt).trans (ht.trans inf_le_right))).trans
      inf_compl_eq_bot.le))
  · apply iSup_le
    intro a
    apply le_iSup_of_le (⟨f a.val, a.property⟩ : D)
    exact condition_le_iff.mpr (show f a.val ∈ (condition (f a.val)).val from mem_condition_self _)

end ForcingCover

private theorem hom_inf {A D : Type u} [CompleteLattice A] [CompleteLattice D]
    (e : CompleteLatticeHom A D) (x y : A) : e (x ⊓ y) = e x ⊓ e y := by
  rw [← sInf_pair, map_sInf, Set.image_pair, sInf_pair]

namespace CohenCover

variable {θ : Cardinal.{u}} {B : Type u} [NontrivialCompleteBooleanAlgebra B]

def Condition.Decides (q : Condition θ B) (α : θ.ord.ToType) (n : Bool) : Prop :=
  ∃ i : q.length.toOrd.val.ToType, i.toOrd.val = α.toOrd.val ∧
    q.value ≤ if n then q.bits i else (q.bits i)ᶜ

theorem Condition.decides_mono {p q : Condition θ B} (hqp : q ≤ p) {α : θ.ord.ToType} {n : Bool}
    (hp : p.Decides α n) : q.Decides α n := by
  obtain ⟨i, hi, hd⟩ := hp
  obtain ⟨hv, hl, hb⟩ := (Condition.le_iff q p).mp hqp
  refine ⟨StringName.includeIndex hl i, (StringName.includeIndex_toOrd hl i).trans hi, ?_⟩
  cases n with
  | true => exact (le_inf le_rfl (hv.trans hd)).trans ((hb i).le.trans inf_le_right)
  | false =>
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    exact (hb i).ge.trans ((inf_le_inf_right _ (hv.trans hd)).trans compl_inf_eq_bot.le)

def decisionValue (θ : Cardinal.{u}) (B : Type u) [NontrivialCompleteBooleanAlgebra B]
    (α : θ.ord.ToType) (n : Bool) : Completion (Condition θ B) :=
  ⨆ q : {p : Condition θ B // p.Decides α n}, condition q.val

def genericBit (θ : Cardinal.{u}) (B : Type u) [NontrivialCompleteBooleanAlgebra B] (α : θ.ord.ToType) :=
  decisionValue θ B α true

theorem condition_le_decisionValue {p : Condition θ B} {α : θ.ord.ToType} {n : Bool}
    (hp : p.Decides α n) : condition p ≤ decisionValue θ B α n :=
  le_iSup (fun q : {p : Condition θ B // p.Decides α n} => condition q.val) ⟨p,hp⟩

theorem decisionValues_disjoint (α : θ.ord.ToType) :
    Disjoint (decisionValue θ B α false) (genericBit θ B α) := by
  apply disjoint_iff_inf_le.mpr
  unfold genericBit decisionValue
  rw [iSup_inf_eq]
  apply iSup_le
  intro p
  rw [inf_iSup_eq]
  apply iSup_le
  intro q
  apply le_of_eq
  by_contra hn
  obtain ⟨r, hrp, hrq⟩ := (condition_inf_ne_bot_iff p.val q.val).mp hn
  obtain ⟨i, hi, h₀⟩ := Condition.decides_mono hrp p.property
  obtain ⟨j, hj, h₁⟩ := Condition.decides_mono hrq q.property
  obtain rfl : i = j := Ordinal.ToType.mk.symm.injective (Subtype.ext (hi.trans hj.symm))
  exact r.positive (bot_unique ((le_inf h₁ h₀).trans inf_compl_eq_bot.le))

private theorem local_decision (q : Condition θ B) (i : q.length.toOrd.val.ToType) (α : θ.ord.ToType)
    (hi : i.toOrd.val = α.toOrd.val) (n : Bool) :
    condition q ⊓ firstStageHom θ B (if n then q.bits i else (q.bits i)ᶜ) ≤ decisionValue θ B α n := by
  let b := if n then q.bits i else (q.bits i)ᶜ
  have hv := (condition_le_firstStageHom_iff q q.value).mpr le_rfl
  have he : condition q ⊓ firstStageHom θ B (q.value ⊓ b) = condition q ⊓ firstStageHom θ B b := by
    rw [hom_inf]
    exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      (le_inf inf_le_left (le_inf (inf_le_left.trans hv) inf_le_right))
  change condition q ⊓ firstStageHom θ B b ≤ _
  rw [← he]
  by_cases hz : q.value ⊓ b = ⊥
  · rw [hz, map_bot]
    exact inf_le_right.trans bot_le
  · rw [← condition_withValue q hz inf_le_left]
    exact condition_le_decisionValue (show (q.withValue _ hz).Decides α n from ⟨i, hi, inf_le_right⟩)

theorem condition_inf_genericBit (q : Condition θ B) (i : q.length.toOrd.val.ToType)
    (α : θ.ord.ToType) (hi : i.toOrd.val = α.toOrd.val) :
    condition q ⊓ genericBit θ B α = condition q ⊓ firstStageHom θ B (q.bits i) := by
  have h₁ := local_decision q i α hi true
  have h₀ := local_decision q i α hi false
  refine le_antisymm (le_inf inf_le_left ?_) (le_inf inf_le_left h₁)
  apply disjoint_compl_right_iff.mp
  apply disjoint_iff_inf_le.mpr
  calc
    (condition q ⊓ genericBit θ B α) ⊓ (firstStageHom θ B (q.bits i))ᶜ =
        (condition q ⊓ firstStageHom θ B (q.bits i)ᶜ) ⊓ genericBit θ B α := by
          rw [map_compl' (firstStageHom θ B)]
          exact inf_right_comm _ _ _
    _ ≤ _ := (inf_le_inf_right _ h₀).trans (disjoint_iff_inf_le.mp (decisionValues_disjoint α))

def genericString (θ : Cardinal.{u}) (B : Type u) [NontrivialCompleteBooleanAlgebra B]
    [Nonempty (Condition θ B)] : StringName (Completion (Condition θ B)) θ.ord :=
  StringName.ofBits θ.ord (genericBit θ B)

end CohenCover

namespace LevyProduct

variable {κ θ : Cardinal.{u}} [Nonempty (Full κ θ)] [Fact (Cardinal.aleph0 < κ)]
variable (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)
local notation "T" => stageSystem hκ hκθ hθ

omit [Nonempty (Full κ θ)] [Fact (Cardinal.aleph0 < κ)] in
private theorem reflect_stage_le (a : (T).Entry) (b c : ((T).base a.stage).Algebra) :
    stageToFull hκ hκθ hθ a.stage b ≤ stageToFull hκ hκθ hθ a.stage c ↔ b ≤ c := by
  let e := stageToFull hκ hκθ hθ a.stage
  refine ⟨fun h => inf_eq_left.mp (stageToFull_injective hκ hκθ hθ a.stage ?_),
    fun h => OrderHomClass.mono e h⟩
  exact (hom_inf e b c).trans (inf_eq_left.mpr h)

theorem mixed_decides_iff (a : (T).Entry) (α : θ.ord.ToType) (n : Bool) :
    (mixedMap hκ hκθ hθ a).Decides α n ↔ ((T).forgetMap a).Decides α n := by
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  cases n with
  | true => exact reflect_stage_le hκ hκθ hθ a _ _
  | false =>
    change stageToFull hκ hκθ hθ a.stage (condition a.point) ≤
      (stageToFull hκ hκθ hθ a.stage (a.bits i))ᶜ ↔ condition a.point ≤ (a.bits i)ᶜ
    erw [← map_compl' (stageToFull hκ hκθ hθ a.stage)]
    exact reflect_stage_le hκ hκθ hθ a _ _

theorem levyCohenCoverHom_decisionValue (α : θ.ord.ToType) (n : Bool) :
    levyCohenCoverHom hκ hκθ hθ (decisionValue κ θ α n) =
      CohenCover.decisionValue θ (Completion (Full κ θ)) α n := by
  let W := {p : Condition κ θ | p.Decides α n}
  let C := {p : CohenCover.Condition θ (Completion (Full κ θ)) | p.Decides α n}
  have hW : IsLowerSet W := fun _ _ h hd => Condition.decides_mono h hd
  have hC : IsLowerSet C := fun _ _ h hd => CohenCover.Condition.decides_mono h hd
  have he : (T).forgetMap ⁻¹' W = mixedMap hκ hκθ hθ ⁻¹' C :=
    Set.ext (fun a => (mixed_decides_iff hκ hκθ hθ a α n).symm)
  let cones (D : Set (T).Entry) := ⨆ p : D, condition p.val
  apply (levyCohenStageIso hκ hκθ hθ).injective
  change (levyCohenStageIso hκ hκθ hθ) ((levyCohenStageIso hκ hκθ hθ).symm
    (stageCoverHom hκ hκθ hθ (decisionValue κ θ α n))) = _
  rw [OrderIso.apply_symm_apply]
  exact (ForcingCover.booleanHom_lower_cones (T).forgetMap (stage_forget_lifts hκ hκθ hθ) W hW).trans
    ((congrArg cones he).trans
      (ForcingCover.booleanHom_lower_cones (mixedMap hκ hκθ hθ) (mixedMap_lifts hκ hκθ hθ) C hC).symm)

theorem levyCohenCoverHom_genericBit (α : θ.ord.ToType) :
    levyCohenCoverHom hκ hκθ hθ (genericBit κ θ α) =
      CohenCover.genericBit θ (Completion (Full κ θ)) α :=
  levyCohenCoverHom_decisionValue hκ hκθ hθ α true

theorem levyCohenCoverHom_genericString [Nonempty (Condition κ θ)]
    [Nonempty (CohenCover.Condition θ (Completion (Full κ θ)))] :
    (⊤ : Completion (CohenCover.Condition θ (Completion (Full κ θ)))) ≤
      ((genericString κ θ).map (levyCohenCoverHom hκ hκθ hθ)).name =ᴮ
        (CohenCover.genericString θ (Completion (Full κ θ))).name := by
  apply StringName.eq_of_bits
  funext α
  rw [StringName.bits_map]
  simp only [genericString, CohenCover.genericString, StringName.bits_ofBits]
  exact levyCohenCoverHom_genericBit hκ hκθ hθ α

end LevyProduct
end Erdos1172Shioya
