/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationCoefficients
public import Erdos1172.Part4ShioyaUltrapowerProjection

@[expose] public section

/-! # Bounded representatives for the prepared collapse coefficients -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172Shioya.UltrapowerStage
open Erdos1172LevyCohen Erdos1172BooleanUltrapower
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)

include hk hf hn ht in
/-- For carriers of size at most the critical cardinal, every full germ
already occurs in the bounded ultrapower. Its support can depend on the germ. -/
theorem exists_bounded_representative {V : Type u} (hV : Cardinal.mk V ≤ κ) (f : I → V) :
    ∃ p : Point U a V, p.val = Germ.ofFun f := by
  classical
  have small : Cardinal.mk V ≤ Cardinal.mk κ.ord.ToType := by simpa only [Cardinal.mk_ord_toType] using hV
  let enc : V ↪ κ.ord.ToType := Classical.choice small
  let code (v : V) := (enc v).toOrd.val.toZFSet
  have inj : Function.Injective code := fun v w he =>
    enc.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext (Ordinal.toZFSet_injective he)))
  obtain ⟨i₀,_⟩ := (Filter.Eventually.of_forall (fun _ : I => True.intro) : ∀ᶠ _ in U, True).exists
  let _ : Nonempty V := ⟨f i₀⟩
  let decode := Function.invFun code
  have inverse : Function.LeftInverse decode code := Function.leftInverse_invFun inj
  obtain ⟨ξ,hξ⟩ := hn (fun i => fiberEmbedding a hk i (enc (f i)))
    ((fiber_range U a hk ht).mono fun i hi => hi ▸ Set.mem_range_self _)
  have rank : Germ.ofFun (fun i => code (f i)) = fineRankGerm U κ θ a ξ := by
    apply Germ.coe_eq.mpr
    filter_upwards [ht,hf ξ,hξ] with i hi hm he
    change _ = (if h : Nonempty (κ.ord.ToType ≃o a i) ∧ ξ ∈ a i then
      ((Classical.choice h.1).symm ⟨ξ,h.2⟩).toOrd.val.toZFSet else ∅)
    rw [dif_pos ⟨hi,hm⟩]
    have hval : ((Classical.choice hi) (enc (f i))).val = ξ := by
      simp only [fiberEmbedding,dif_pos hi] at he
      exact he
    exact congrArg (fun k : κ.ord.ToType => k.toOrd.val.toZFSet)
      ((Classical.choice hi).eq_symm_apply.mpr (Subtype.ext hval))
  obtain ⟨η,g,hg⟩ := fineRankGerm_boundedSupport U κ θ a ξ hf ht
  refine ⟨represent U a η (fun S => decode (g S)),?_⟩
  apply Germ.coe_eq.mpr
  exact (Germ.coe_eq.mp (hg.trans rank.symm)).mono fun i he => (congrArg decode he).trans (inverse (f i))

variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]

include hk hf hn ht in
theorem exists_bounded_coefficient (hκ : κ.IsInaccessible) (c : FirstAlgebra θ) :
    ∃ p : Point U a (FirstAlgebra κ),
      collapseCompletionIso U a hk hf hn ht (value U (repr U a p)) = c := by
  obtain ⟨f,hf'⟩ := exists_prepared_coefficient U a hf hn hk ht (hκ.aleph0_lt.trans_le hk) c
  obtain ⟨p,hp⟩ := exists_bounded_representative U a hk hf hn ht (below_completion_cardinal_le κ hκ) f
  refine ⟨p,?brg⟩
  have he := Germ.coe_eq.mp ((repr_eq U a p).trans hp)
  exact (congrArg (collapseCompletionIso U a hk hf hn ht) (value_eq_of_eventuallyEq U he)).trans hf'

end Erdos1172LevyCollapse.Preparation
