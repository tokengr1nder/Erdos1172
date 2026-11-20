/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaProjectionRefinement
public import Erdos1172.Part4ShioyaCollapseTreeProjection

@[expose] public section

/-! # Dense canonical collapse presentations

Below every dual Shioya condition there are conditions whose underlying
posets are canonical collapses. Their target cardinals can be chosen
regular and above any prescribed bound below the inaccessible cardinal.
The refinement preserves the length of the original string.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.Condition

variable {κ θ : Cardinal.{u}}

theorem exists_collapse_refinement (p : Condition κ θ) (hκ : κ.IsRegular) (hκθ : κ < θ)
    (hθ : θ.IsInaccessible) (μ : Cardinal.{u}) (hμ : μ < θ) (hμinf : Cardinal.aleph0 ≤ μ)
    (hsize : Cardinal.mk p.Poset ≤ μ) :
    ∃ w : Condition κ θ, Nonempty (w.Poset ≃o Collapse.Condition κ μ.ord.ToType) ∧
      w.length = p.length ∧ Refines w p := by
  have hmk : Cardinal.mk μ.ord.ToType = μ := Cardinal.mk_ord_toType μ
  let : Nontrivial μ.ord.ToType :=
    Cardinal.one_lt_iff_nontrivial.mp (hmk.symm ▸ Cardinal.one_lt_aleph0.trans_le hμinf)
  obtain ⟨e⟩ : Nonempty (p.Poset ↪ μ.ord.ToType) := hsize.trans_eq hmk.symm
  let d := Function.invFun e
  have hd : Function.Surjective d := (Function.leftInverse_invFun e.injective).surjective
  apply p.exists_projection_refinement (Collapse.Condition κ μ.ord.ToType)
    (Collapse.cardinal_lt hθ hκθ (hmk.trans_lt hμ)) (Collapse.separative hκ.aleph0_le)
    (Collapse.shortInfima hκ)
  exact Collapse.treeProjection hκ p.complete d hd p.point

theorem exists_regular_collapse_refinement (p : Condition κ θ) (hκ : κ.IsRegular) (hκθ : κ < θ)
    (hθ : θ.IsInaccessible) (τ : Cardinal.{u}) (hτ : τ < θ) :
    ∃ μ : Cardinal.{u}, τ < μ ∧ κ < μ ∧ μ < θ ∧ μ.IsRegular ∧
      ∃ w : Condition κ θ, Nonempty (w.Poset ≃o Collapse.Condition κ μ.ord.ToType) ∧
        w.length = p.length ∧ Refines w p := by
  let a := max (max τ κ) (Cardinal.mk p.Poset)
  have ha : a < θ := max_lt (max_lt hτ hκθ) p.presentation.cardinal_lt
  have hκa : κ ≤ a := (le_max_right τ κ).trans (le_max_left _ _)
  have hτa : τ ≤ a := (le_max_left τ κ).trans (le_max_left _ _)
  have haμ := Order.lt_succ a
  have hμθ : Order.succ a < θ := hθ.isSuccLimit.succ_lt ha
  refine ⟨Order.succ a, hτa.trans_lt haμ, hκa.trans_lt haμ, hμθ,
    Cardinal.isRegular_succ (hκ.aleph0_le.trans hκa), ?_⟩
  exact p.exists_collapse_refinement hκ hκθ hθ (Order.succ a) hμθ
    (hκ.aleph0_le.trans (hκa.trans haμ.le)) ((le_max_right _ _).trans haμ.le)

end Erdos1172Shioya.Condition
