/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyStageCover

@[expose] public section

/-! # Lifts at the greatest point of a Lévy stage

When the refining presentation forces the required string extension at its
greatest point, the lift also uses the greatest point of its stage. The
specified projection to the initial stage still commutes on all Boolean values.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)]
variable (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)
local notation "T" => stageSystem hκ hκθ hθ

omit [Fact (Cardinal.aleph0 < κ)] in
theorem stageBase_greatest (j : Index θ) (x : (stageBase hκ hκθ hθ j).Poset) :
    x ≤ (stageBase hκ hκθ hθ j).point := by
  let e := stageIso hκ hκθ hθ j
  change x ≤ e.symm (empty hκ.pos)
  exact e.le_symm_apply.mpr (le_empty (e x) hκ.pos)

private theorem cone_eq_top {P : Type u} [Preorder P] (p : P) (h : ∀ x, x ≤ p) :
    condition p = ⊤ :=
  top_unique (fun x _ => condition_le_iff.mp (condition_mono (h x)))

theorem greatest_stage_lift (a : (T).Entry) (q : Condition κ θ)
    (π : PartialProjection κ q.Poset ((T).base a.stage).Poset)
    (hp : condition q.point ≤ π.booleanHom (condition a.point))
    (hs : condition q.point ≤ extensionValue π.booleanHom (a.forget T).name q.name)
    (htop : ∀ x, x ≤ q.point) :
    ∃ b ≤ a, ∃ (h : a.stage ≤ b.stage) (σ : PartialProjection κ ((T).base b.stage).Poset q.Poset),
      (∀ x, x ≤ b.point) ∧ (T).forgetMap b ≤ q ∧
      σ.booleanHom.comp π.booleanHom = ((T).restrict h).booleanHom ∧
      (⊤ : ((T).base b.stage).Algebra) ≤ extensionValue σ.booleanHom q.name (b.forget T).name := by
  obtain ⟨j, h, σ, hσ⟩ := (T).factor_projection (stageSystem_hasCollapseFactors hκ hκθ hθ) hκ a.stage q π
  let b : (T).Entry := ⟨j, ((T).base j).point, q.length, fun i => σ.booleanHom (q.bits i)⟩
  have hbp : (⊤ : ((T).base j).Algebra) ≤ σ.booleanHom (condition q.point) := by
    rw [cone_eq_top _ htop, map_top]
  have hbs : (⊤ : ((T).base j).Algebra) ≤ extensionValue σ.booleanHom q.name (b.forget T).name := by
    apply extensionValue_of_bits σ.booleanHom q.name (b.forget T).name le_rfl
    intro i
    have hi : StringName.includeIndex (le_refl q.length.toOrd.val) i = i :=
      Ordinal.ToType.mk.symm.injective (Subtype.ext (StringName.includeIndex_toOrd le_rfl i))
    change ⊤ ⊓ σ.booleanHom ((StringName.ofBits _ q.bits).bits i) =
      ⊤ ⊓ (StringName.ofBits q.length.toOrd.val (fun k => σ.booleanHom (q.bits k))).bits
        (StringName.includeIndex (le_refl q.length.toOrd.val) i)
    rw [hi, StringName.bits_ofBits, StringName.bits_ofBits]
  have hbpoint : (⊤ : ((T).base j).Algebra) ≤ ((T).restrict h).booleanHom (condition a.point) := by
    rw [← hσ]
    exact hbp.trans (OrderHomClass.mono σ.booleanHom hp)
  have hbstring : (⊤ : ((T).base j).Algebra) ≤ extensionValue ((T).restrict h).booleanHom
      (a.forget T).name (b.forget T).name := by
    rw [← hσ]
    exact extensionValue_trans _ _ _ _ _ hbp hs hbs
  exact ⟨b, ⟨h, le_top.trans hbpoint, le_top.trans hbstring⟩, h, σ, stageBase_greatest hκ hκθ hθ j,
    ⟨σ, le_top.trans hbp, le_top.trans hbs⟩, hσ, hbs⟩

end Erdos1172Shioya.LevyProduct
