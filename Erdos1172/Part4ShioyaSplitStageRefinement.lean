/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaRelativeCollapse
public import Erdos1172.Part4ShioyaProjectionRefinement

@[expose] public section

/-! # Split presentations over a fixed Shioya refinement

Given the particular projection witnessing a refinement, another strengthening
has a presentation by the original base times a collapse. Projection onto the
base agrees on every Boolean value with the composite through the intermediate
condition. The collapse cardinal can be chosen arbitrarily high below θ.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}}

namespace PartialProjection

/-- A commuting square with the first product projection persists under relabelling. -/
theorem precomposeIso_first_square {S P Q R : Type u} [PartialOrder S] [PartialOrder P]
    [PartialOrder Q] [PartialOrder R] (π : PartialProjection κ Q P)
    (ρ : PartialProjection κ (P × R) Q) (e : S ≃o P × R) (c : R)
    (hsquare : ρ.booleanHom.comp π.booleanHom =
      (productProjection (κ := κ) (OrderIso.refl (P × R)) c).booleanHom) :
    (ρ.precomposeIso e).booleanHom.comp π.booleanHom =
      (productProjection (κ := κ) e c).booleanHom := by
  let σ := ρ.precomposeIso e
  let F := productProjection (κ := κ) e c
  let G := productProjection (κ := κ) (OrderIso.refl (P × R)) c
  ext b
  have he : ρ.booleanHom (π.booleanHom b) = G.booleanHom b := DFunLike.congr_fun hsquare b
  have hm (y : σ.dom) :
      condition y.val ≤ σ.booleanHom (π.booleanHom b) ↔ condition y.val ≤ F.booleanHom b := by
    let z : ρ.dom := ⟨e y.val, y.property⟩
    have hz := ρ.dom_condition z (π.booleanHom b)
    rw [he] at hz
    exact (σ.dom_condition y _).trans (hz.symm.trans
      ((G.dom_condition ⟨e y.val, Set.mem_univ _⟩ b).trans
        (F.dom_condition ⟨y.val, Set.mem_univ _⟩ b).symm))
  have hdense (s : S) : ∃ y ∈ σ.dom, y ≤ s := by
    obtain ⟨y, hy⟩ := σ.dense s
    exact ⟨y.val, y.property, hy⟩
  exact le_antisymm (le_of_dense_conditions_le σ.dom hdense fun y => (hm y).mp)
    (le_of_dense_conditions_le σ.dom hdense fun y => (hm y).mpr)

end PartialProjection

namespace Condition

/-- The refinement of q witnesses the specified projection to p on every Boolean value,
and its first product projection itself witnesses the Shioya order inequalities to p. -/
def SplitStageAlong {p q : Condition κ θ} (π : PartialProjection κ q.Poset p.Poset)
    (w : Condition κ θ) {X : Type u}
    (e : w.Poset ≃o p.Poset × Collapse.Condition κ X) : Prop :=
  w.length = q.length ∧ ∃ σ : PartialProjection κ w.Poset q.Poset,
    condition w.point ≤ σ.booleanHom (condition q.point) ∧
    condition w.point ≤ extensionValue σ.booleanHom q.name w.name ∧
    ∀ c : Collapse.Condition κ X,
      σ.booleanHom.comp π.booleanHom = (productProjection (κ := κ) e c).booleanHom ∧
      condition w.point ≤ (productProjection (κ := κ) e c).booleanHom (condition p.point) ∧
      condition w.point ≤ extensionValue (productProjection (κ := κ) e c).booleanHom p.name w.name

variable [Fact (Cardinal.aleph0 < κ)] {p q : Condition κ θ}

set_option maxHeartbeats 800000 in
theorem exists_split_stage_refinement (π : PartialProjection κ q.Poset p.Poset)
    (hpoint : condition q.point ≤ π.booleanHom (condition p.point))
    (hstring : condition q.point ≤ extensionValue π.booleanHom p.name q.name)
    (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)
    (μ : Cardinal.{u}) (hμ : μ < θ) (hμinf : Cardinal.aleph0 ≤ μ)
    (hsize : Cardinal.mk π.dom ≤ μ) :
    ∃ w ≤ q, ∃ e : w.Poset ≃o p.Poset × Collapse.Condition κ μ.ord.ToType,
      SplitStageAlong π w e := by
  let X := μ.ord.ToType
  have hmk : Cardinal.mk X = μ := Cardinal.mk_ord_toType μ
  let _ : Nontrivial X :=
    Cardinal.one_lt_iff_nontrivial.mp (hmk.symm ▸ Cardinal.one_lt_aleph0.trans_le hμinf)
  let _ : Nonempty π.dom := ⟨(π.dense q.point).choose⟩
  obtain ⟨j⟩ : Nonempty (π.dom ↪ X) := hsize.trans_eq hmk.symm
  let d := Function.invFun j
  have hd : Function.Surjective d := (Function.leftInverse_invFun j.injective).surjective
  let C := Collapse.Condition κ X
  have hC : Cardinal.mk C < θ := Collapse.cardinal_lt hθ hκθ (hmk.trans_lt hμ)
  have hPC : Cardinal.mk (p.Poset × C) < θ := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le p.presentation.cardinal_lt hC
  obtain ⟨A, ⟨e⟩⟩ := exists_small_presentation (p.Poset × C) hPC
  let ρ := π.relativeCollapse d hd hκ p.complete q.complete
  let σ := ρ.precomposeIso e
  obtain ⟨x, hx⟩ := σ.reaches q.point
  let w : Condition κ θ :=
    ⟨A, separative_of_iso e (separative_prod p.separative (Collapse.separative hκ.aleph0_le)),
      shortInfima_of_iso e (shortInfima_prod p.complete (Collapse.shortInfima hκ)),
      x.val, q.length, fun i => σ.booleanHom (q.bits i)⟩
  have hwp : condition w.point ≤ σ.booleanHom (condition q.point) :=
    (σ.dom_condition x _).mpr (condition_mono hx)
  let _ : Nonempty A.Carrier := ⟨w.point⟩
  let _ : NontrivialCompleteBooleanAlgebra w.Algebra :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  have hws : condition w.point ≤ extensionValue σ.booleanHom q.name w.name := by
    apply extensionValue_of_bits σ.booleanHom q.name w.name le_rfl
    intro i
    have hi : StringName.includeIndex (show q.length.toOrd.val ≤ w.length.toOrd.val from le_rfl) i = i :=
      Ordinal.ToType.mk.symm.injective (Subtype.ext (StringName.includeIndex_toOrd le_rfl i))
    simp only [hi, name, StringName.bits_ofBits]
    exact rfl
  refine ⟨w, ⟨σ, hwp, hws⟩, e, rfl, σ, hwp, hws, ?_⟩
  intro c
  have hs := π.precomposeIso_first_square ρ e c
    (π.relativeCollapse_booleanHom d hd hκ p.complete q.complete c)
  refine ⟨hs, ?_, ?_⟩ <;> rw [← hs]
  · exact hwp.trans (OrderHomClass.mono σ.booleanHom hpoint)
  · exact extensionValue_trans π.booleanHom σ.booleanHom p.name q.name w.name hwp hstring hws

theorem exists_regular_split_stage_refinement (π : PartialProjection κ q.Poset p.Poset)
    (hpoint : condition q.point ≤ π.booleanHom (condition p.point))
    (hstring : condition q.point ≤ extensionValue π.booleanHom p.name q.name)
    (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible) (τ : Cardinal.{u}) (hτ : τ < θ) :
    ∃ μ : Cardinal.{u}, τ < μ ∧ κ < μ ∧ μ < θ ∧ μ.IsRegular ∧
      ∃ w ≤ q, ∃ e : w.Poset ≃o p.Poset × Collapse.Condition κ μ.ord.ToType,
        SplitStageAlong π w e := by
  let a := max (max τ κ) (Cardinal.mk π.dom)
  have hdom : Cardinal.mk π.dom < θ := (Cardinal.mk_set_le π.dom).trans_lt q.presentation.cardinal_lt
  have ha : a < θ := max_lt (max_lt hτ hκθ) hdom
  have hκa : κ ≤ a := (le_max_right τ κ).trans (le_max_left _ _)
  have hτa : τ ≤ a := (le_max_left τ κ).trans (le_max_left _ _)
  have haμ := Order.lt_succ a
  have hμθ : Order.succ a < θ := hθ.isSuccLimit.succ_lt ha
  refine ⟨Order.succ a, hτa.trans_lt haμ, hκa.trans_lt haμ, hμθ,
    Cardinal.isRegular_succ (hκ.aleph0_le.trans hκa), ?_⟩
  exact exists_split_stage_refinement π hpoint hstring hκ hκθ hθ _ hμθ
    (hκ.aleph0_le.trans (hκa.trans haμ.le)) ((le_max_right _ _).trans haμ.le)

end Condition
end Erdos1172Shioya
