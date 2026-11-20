/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingClosedUnion

@[expose] public section

/-! # The stage matching hypotheses from unbounded regular collapsing suborders -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PosetCompletion Erdos1172PosetProjection Erdos1172PositiveBoolean
open Erdos1172BooleanFactor bSet
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching

variable {θ : Cardinal.{u}} (B : θ.ord.ToType → Type u) [∀ i, NontrivialCompleteBooleanAlgebra (B i)]

/-- The unbounded regular stages in the source collapse have density at most
their cardinal and collapse that cardinal to countable size. -/
def RegularCollapsingStages : Prop := ∀ ξ : Cardinal.{u}, ξ < θ →
  ∃ (μ : Cardinal.{u}) (hm : μ < θ), ξ < μ ∧ ℵ₀ < μ ∧ μ.IsRegular ∧
    (∃ d : μ.ord.ToType → Positive (B (cardinalStage hm)), ∀ a, ∃ k, d k ≤ a) ∧
    (⊤ : B (cardinalStage hm)) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega

variable {B}

/-- All source stages have small density, by projecting a dense family of
the next good stage. A subsequent good stage supplies both collapsing factors. -/
theorem exists_collapsing_pairs
    (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
    (hb : ∀ {i j} (h : i ≤ j), Function.Injective (b h)) (good : RegularCollapsingStages B) :
    ∀ (i t : θ.ord.ToType), Nonempty (CollapsingPair B ClosedStage i t) := by
  intro i t
  let ξ := max i.toOrd.val.card t.toOrd.val.card
  have hξ : ξ < θ := max_lt (Cardinal.lt_ord.mp i.toOrd.property) (Cardinal.lt_ord.mp t.toOrd.property)
  obtain ⟨μ,hm,hξμ,_,_,⟨d,hd⟩,_⟩ := good ξ hξ
  obtain ⟨ν,hn,hmn,hu,reg,⟨v,hv⟩,count⟩ := good μ hm
  let j := cardinalStage hm
  let k := cardinalStage hn
  have before {l : θ.ord.ToType} {α : Cardinal.{u}} (ha : α < θ) (hl : l.toOrd.val.card < α) :
      l ≤ cardinalStage ha := by
    apply (Ordinal.ToType.mk.symm.le_iff_le).mp
    change l.toOrd.val ≤ (cardinalStage ha).toOrd.val
    rw [cardinalStage_rank]
    exact (Cardinal.lt_ord.mpr hl).le
  have ij : i ≤ j := before hm ((le_max_left _ _).trans_lt hξμ)
  have ik : i ≤ k := before hn (((le_max_left _ _).trans_lt hξμ).trans hmn)
  have tk : t ≤ k := before hn (((le_max_right _ _).trans_lt hξμ).trans hmn)
  let e := b ij
  let old (a : μ.ord.ToType) : Positive (B i) :=
    ⟨lowerProjection e (d a).val,lowerProjection_ne_bot e (d a).property⟩
  have dense (a : Positive (B i)) : ∃ x, old x ≤ a := by
    have pos : e a.val ≠ ⊥ := fun he => a.property (hb ij (he.trans (map_bot e).symm))
    obtain ⟨x,hx⟩ := hd ⟨e a.val,pos⟩
    exact ⟨x,lowerProjection_le e hx⟩
  obtain ⟨⟨w,hw⟩,hc⟩ := closedStage_matching_data _ hu.le (cardinalStage_rank hn)
  exact ⟨⟨k,ik,tk,ν,hu,reg,μ.ord.ToType,old,by simpa only [Cardinal.mk_ord_toType] using hmn,
    dense,v,hv,w,hw,count,hc⟩⟩

end Erdos1172LevyCollapse.Matching
