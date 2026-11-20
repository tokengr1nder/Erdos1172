/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaSplitStageRefinement
public import Erdos1172.Part4ShioyaCollapsePresentations

@[expose] public section

/-! # The stage projection to the dual Shioya forcing

The order on stage conditions uses the specified restriction between stages.
A new collapse coordinate absorbs a refinement while preserving this restriction.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya

structure StageSystem (κ θ : Cardinal.{u}) (I : Type u) [Preorder I] where
  base : I → Condition κ θ
  restrict : ∀ {i j : I}, i ≤ j → PartialProjection κ (base j).Poset (base i).Poset
  restrict_id : ∀ i, (restrict (le_refl i)).booleanHom = CompleteLatticeHom.id _
  restrict_comp : ∀ {i j k : I} (h : i ≤ j) (g : j ≤ k),
    (restrict (h.trans g)).booleanHom = (restrict g).booleanHom.comp (restrict h).booleanHom

namespace StageSystem

variable {κ θ : Cardinal.{u}} {I : Type u} [Preorder I] (T : StageSystem κ θ I)

structure Entry where
  stage : I
  point : (T.base stage).Poset
  length : θ.ord.ToType
  bits : length.toOrd.val.ToType → (T.base stage).Algebra

def Entry.forget (a : T.Entry) : Condition κ θ :=
  { T.base a.stage with point := a.point, length := a.length, bits := a.bits }

def Entry.Refines (a b : T.Entry) : Prop :=
  ∃ h : b.stage ≤ a.stage,
    condition a.point ≤ (T.restrict h).booleanHom (condition b.point) ∧
    condition a.point ≤ extensionValue (T.restrict h).booleanHom (b.forget T).name (a.forget T).name

instance : Preorder T.Entry where
  le := Entry.Refines T
  le_refl a := by
    refine ⟨le_rfl, ?_, ?_⟩ <;> rw [T.restrict_id]
    · exact le_rfl
    · exact le_top.trans (extensionValue_refl _)
  le_trans a b c hab hbc := by
    obtain ⟨g, hp, hs⟩ := hab
    obtain ⟨h, hq, ht⟩ := hbc
    refine ⟨h.trans g, ?_, ?_⟩ <;> rw [T.restrict_comp h g]
    · exact hp.trans (OrderHomClass.mono (T.restrict g).booleanHom hq)
    · exact extensionValue_trans _ _ (c.forget T).name (b.forget T).name (a.forget T).name hp ht hs

variable [hunc : Fact (Cardinal.aleph0 < κ)]

def forgetMap : T.Entry →o Condition κ θ where
  toFun := Entry.forget T
  monotone' := by
    rintro a b ⟨h, hp, hs⟩
    exact ⟨T.restrict h, hp, hs⟩

/-- A later stage projects to the product with a large collapse coordinate and
recovers the prescribed earlier restriction on every Boolean value. -/
def HasCollapseFactors : Prop :=
  ∀ (i : I) (μ : Cardinal.{u}), μ < θ →
    ∃ (j : I) (h : i ≤ j) (X : Type u), μ ≤ Cardinal.mk X ∧
      ∃ (c : Collapse.Condition κ X)
        (F : PartialProjection κ (T.base j).Poset ((T.base i).Poset × Collapse.Condition κ X)),
        (T.restrict h).booleanHom = F.booleanHom.comp
          (productProjection (κ := κ) (OrderIso.refl ((T.base i).Poset × Collapse.Condition κ X)) c).booleanHom

def translate (j : I) (q : Condition κ θ)
    (σ : PartialProjection κ (T.base j).Poset q.Poset) : T.Entry :=
  ⟨j, (σ.reaches q.point).choose.val, q.length, fun i => σ.booleanHom (q.bits i)⟩

omit hunc in
private theorem translate_spec (j : I) (q : Condition κ θ)
    (σ : PartialProjection κ (T.base j).Poset q.Poset) :
    condition (T.translate j q σ).point ≤ σ.booleanHom (condition q.point) ∧
      condition (T.translate j q σ).point ≤ extensionValue σ.booleanHom q.name
        ((T.translate j q σ).forget T).name := by
  let x := (σ.reaches q.point).choose
  let a := T.translate j q σ
  have hp : condition a.point ≤ σ.booleanHom (condition q.point) :=
    (σ.dom_condition x _).mpr (condition_mono (σ.reaches q.point).choose_spec)
  have hs : condition a.point ≤ extensionValue σ.booleanHom q.name (a.forget T).name := by
    apply extensionValue_of_bits σ.booleanHom q.name (a.forget T).name le_rfl
    intro i
    have hi : StringName.includeIndex (show q.length.toOrd.val ≤ (a.forget T).length.toOrd.val from le_rfl) i = i :=
      Ordinal.ToType.mk.symm.injective (Subtype.ext (StringName.includeIndex_toOrd le_rfl i))
    rw [hi]
    change condition a.point ⊓ σ.booleanHom ((StringName.ofBits _ q.bits).bits i) =
      condition a.point ⊓ (StringName.ofBits q.length.toOrd.val (fun k => σ.booleanHom (q.bits k))).bits i
    rw [StringName.bits_ofBits, StringName.bits_ofBits]
  exact ⟨hp, hs⟩

theorem factor_projection (hT : T.HasCollapseFactors) (hκ : κ.IsRegular) (i : I)
    (q : Condition κ θ) (π : PartialProjection κ q.Poset (T.base i).Poset) :
    ∃ (j : I) (h : i ≤ j) (σ : PartialProjection κ (T.base j).Poset q.Poset),
      σ.booleanHom.comp π.booleanHom = (T.restrict h).booleanHom := by
  obtain ⟨j, h, X, hX, c, F, hF⟩ := hT i (Cardinal.mk π.dom)
    ((Cardinal.mk_set_le π.dom).trans_lt q.presentation.cardinal_lt)
  let _ : Nonempty π.dom := ⟨(π.dense q.point).choose⟩
  obtain ⟨e⟩ : Nonempty (π.dom ↪ X) := hX
  let _ : Nonempty X := ⟨e (π.dense q.point).choose⟩
  let d := Function.invFun e
  have hd : Function.Surjective d := (Function.leftInverse_invFun e.injective).surjective
  let ρ := π.relativeCollapse d hd hκ (T.base i).complete q.complete
  let σ := F.comp ρ hunc.out (T.base j).complete
  have hσ : σ.booleanHom.comp π.booleanHom = (T.restrict h).booleanHom := by
    rw [hF, show σ.booleanHom = F.booleanHom.comp ρ.booleanHom from
      F.booleanHom_comp ρ hunc.out (T.base j).complete]
    have he := π.relativeCollapse_booleanHom d hd hκ (T.base i).complete q.complete c
    ext x
    exact congrArg F.booleanHom (DFunLike.congr_fun he x)
  exact ⟨j, h, σ, hσ⟩

theorem forget_lifts (hT : T.HasCollapseFactors) (hκ : κ.IsRegular)
    (a : T.Entry) (q : Condition κ θ) (hq : q ≤ T.forgetMap a) :
    ∃ b ≤ a, T.forgetMap b ≤ q := by
  obtain ⟨π, hp, hs⟩ := hq
  obtain ⟨j,h,σ,hσ⟩ := T.factor_projection hT hκ a.stage q π
  let b := T.translate j q σ
  obtain ⟨hbp, hbs⟩ := T.translate_spec j q σ
  have hpoint : condition (T.translate j q σ).point ≤ (T.restrict h).booleanHom (condition a.point) := by
    rw [← hσ]
    exact hbp.trans (OrderHomClass.mono σ.booleanHom hp)
  have hstring : condition (T.translate j q σ).point ≤ extensionValue (T.restrict h).booleanHom
      (a.forget T).name (b.forget T).name := by
    rw [← hσ]
    exact extensionValue_trans π.booleanHom σ.booleanHom (a.forget T).name q.name
      (b.forget T).name hbp hs hbs
  exact ⟨b, ⟨h, hpoint, hstring⟩, σ, hbp, hbs⟩

theorem forget_reaches [Nonempty I] (hT : T.HasCollapseFactors) (hκ : κ.IsRegular)
    (q : Condition κ θ) : ∃ a : T.Entry, T.forgetMap a ≤ q := by
  let i := Classical.arbitrary I
  obtain ⟨j, _, X, hX, _, F, _⟩ := hT i (Cardinal.mk q.Poset) q.presentation.cardinal_lt
  obtain ⟨e⟩ : Nonempty (q.Poset ↪ X) := hX
  let _ : Nonempty X := ⟨e q.point⟩
  let d := Function.invFun e
  have hd : Function.Surjective d := (Function.leftInverse_invFun e.injective).surjective
  let C := Collapse.Condition κ X
  let P := (T.base i).Poset
  let G := productProjection (κ := κ) (OrderIso.prodComm : P × C ≃o C × P) (T.base i).point
  let H := Collapse.treeProjection hκ q.complete d hd q.point
  let σ := (F.comp G hunc.out (T.base j).complete).comp H hunc.out (T.base j).complete
  exact ⟨T.translate j q σ, σ, T.translate_spec j q σ⟩

end StageSystem
end Erdos1172Shioya
