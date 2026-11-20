/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationFiberRelabel

@[expose] public section

/-! # The actual upper Lévy condition order is the ultrapower of the lower order -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
open scoped Erdos1172LevyCollapse
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
local notation "K" => κ.ord.ToType
local notation "L" => θ.ord.ToType

private theorem const_countable {X : Type*} [Countable X] (f : I → X) : ∃ x, ∀ᶠ i in U, f i = x := by
  by_contra! h
  obtain ⟨i,hi⟩ := (eventually_countable_forall.mpr h).exists
  exact hi (f i) rfl

private theorem normal_finset (hn : NormalOn U a) (s : I → Finset L)
    (sub : ∀ᶠ i in U, (s i : Set L) ⊆ a i) : ∃ S, ∀ᶠ i in U, s i = S := by
  classical
  obtain ⟨n,hn'⟩ := const_countable U (fun i => (s i).card)
  let equiv (i : I) (h : (s i).card = n) : Fin n ≃ ↥(s i) :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using h)).symm
  let v (k : Fin n) (i : I) := if h : (s i).card = n then (equiv i h k).val else Classical.choice inferInstance
  have row (k : Fin n) : ∀ᶠ i in U, v k i ∈ a i := by
    filter_upwards [hn',sub] with i hc hs
    have eq : (s i).card = n := hc
    simp only [v,dif_pos eq]
    exact hs (equiv i eq k).property
  choose x hx using fun k => hn (v k) (row k)
  refine ⟨Finset.univ.image x,?_⟩
  filter_upwards [hn',eventually_countable_forall.mpr hx] with i hc hi
  have eq : (s i).card = n := hc
  have atIndex (k : Fin n) : (equiv i eq k).val = x k := by simpa only [v,dif_pos eq] using hi k
  ext y
  constructor
  · intro hy
    let k := (equiv i eq).symm ⟨y,hy⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,(atIndex k).symm.trans (congrArg Subtype.val
      ((equiv i eq).apply_symm_apply ⟨y,hy⟩))⟩
  · intro hy
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hy
    rw [← atIndex k]
    exact (equiv i eq k).property

omit [Nonempty θ.ord.ToType] in
private theorem labels_represents (p : BelowCondition θ) (z : ZFSet.{u}) (hz : z ∈ conditionGraph p) :
    ∃ (x y : ↥(labels p)) (n : ℕ), entryTriple x.val.toOrd.val n y.val.toOrd.val = z := by
  obtain ⟨i,n,hn,rfl⟩ := (mem_conditionGraph_iff _ _).mp hz
  have si : i ∈ p.support := DFinsupp.mem_support_iff.mpr (fun h => by rw [h] at hn; exact Nat.not_lt_zero _ hn)
  exact ⟨⟨i,support_mem_labels p si⟩,⟨_,letter_mem_labels p ((p i).entries[n]) (List.getElem_mem hn)⟩,n,rfl⟩

private theorem fixed_conditions (hn : NormalOn U a) (p : I → BelowCondition θ)
    (sub : ∀ᶠ i in U, (labels (p i) : Set L) ⊆ a i) : ∃ q, ∀ᶠ i in U, p i = q := by
  classical
  obtain ⟨S,hS⟩ := normal_finset U a hn _ sub
  let key (e : ↥S × ℕ × ↥S) := entryTriple e.1.val.toOrd.val e.2.1 e.2.2.val.toOrd.val
  let bits (e : ↥S × ℕ × ↥S) := ∀ᶠ i in U, key e ∈ conditionGraph (p i)
  have bit (e : ↥S × ℕ × ↥S) : ∀ᶠ i in U, (key e ∈ conditionGraph (p i) ↔ bits e) := by
    by_cases h : bits e
    · exact (show ∀ᶠ i in U, key e ∈ conditionGraph (p i) from h).mono fun _ hi => iff_of_true hi h
    · exact (U.eventually_not.mpr h).mono fun _ hi => iff_of_false hi h
  have whole := hS.and (eventually_countable_forall.mpr bit)
  obtain ⟨j,hj⟩ := whole.exists
  refine ⟨p j,whole.mono fun i hi => conditionGraph_injective ?_⟩
  ext z
  have rep (k : I) (eq : labels (p k) = S) (h : z ∈ conditionGraph (p k)) :
      ∃ e : ↥S × ℕ × ↥S, key e = z := by
    obtain ⟨x,y,n,he⟩ := labels_represents _ _ h
    exact ⟨(⟨x.val,eq ▸ x.property⟩,n,⟨y.val,eq ▸ y.property⟩),he⟩
  constructor
  · intro h
    obtain ⟨e,rfl⟩ := rep i hi.1 h
    exact (hj.2 e).mpr ((hi.2 e).mp h)
  · intro h
    obtain ⟨e,rfl⟩ := rep j hj.1 h
    exact (hi.2 e).mpr ((hj.2 e).mp h)

variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)

/-- On fibers of the prescribed order type this is their increasing enumeration. -/
def fiberEmbedding (i : I) : K ↪o L := by
  classical
  exact if h : Nonempty (K ≃o a i) then (Classical.choice h).toOrderEmbedding.trans
    (OrderEmbedding.subtype (a i)) else (initialCoordinate hk).toOrderEmbedding

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
include ht in
theorem fiber_range : ∀ᶠ i in U, Set.range (fiberEmbedding a hk i) = a i := ht.mono fun i h => by
  classical
  ext x
  simp only [fiberEmbedding,dif_pos h,Set.mem_range]
  exact ⟨fun ⟨j,he⟩ => he ▸ ((Classical.choice h) j).property,fun hx =>
    ⟨(Classical.choice h).symm ⟨x,hx⟩,congrArg Subtype.val ((Classical.choice h).apply_symm_apply ⟨x,hx⟩)⟩⟩

include hn ht in
theorem germ_has_upper_condition (f : I → BelowCondition κ) :
    ∃ p : BelowCondition θ, ∀ᶠ i in U, relabel (fiberEmbedding a hk i) (f i) = p := by
  apply fixed_conditions U a hn
  exact (fiber_range U a hk ht).mono fun i hi _ hx => hi ▸ relabel_labels _ _ hx

omit [Nonempty θ.ord.ToType] in
include hf ht in
theorem upper_condition_has_germ (p : BelowCondition θ) :
    ∃ f : I → BelowCondition κ, ∀ᶠ i in U, relabel (fiberEmbedding a hk i) (f i) = p := by
  classical
  have hit : ∀ᶠ i in U, ∀ x : ↥(labels p), x.val ∈ a i :=
    eventually_countable_forall.mpr fun x => hf x.val
  let possible (i : I) := ∃ q, relabel (fiberEmbedding a hk i) q = p
  have pos : ∀ᶠ i in U, possible i := by
    filter_upwards [hit,fiber_range U a hk ht] with i hi eq
    exact exists_relabel_eq _ p (fun x hx => eq ▸ hi ⟨x,hx⟩)
  exact ⟨fun i => if h : possible i then h.choose else ⊤,pos.mono fun i hi => by
    simp only [dif_pos hi]; exact hi.choose_spec⟩

def upper (f : I → BelowCondition κ) := (germ_has_upper_condition U a hk hn ht f).choose

theorem upper_le {f g : I → BelowCondition κ} :
    upper U a hk hn ht f ≤ upper U a hk hn ht g ↔ ∀ᶠ i in U, f i ≤ g i := by
  let selected (x : I → BelowCondition κ) := (germ_has_upper_condition U a hk hn ht x).choose_spec
  have both := (selected f).and (selected g)
  constructor
  · intro h
    exact both.mono fun i hi => (relabel_le_iff _ _ _).mp (hi.1.trans_le (h.trans_eq hi.2.symm))
  · intro h
    obtain ⟨i,⟨h₁,h₂⟩,hi⟩ := (both.and h).exists
    exact h₁.symm.trans_le (((relabel_le_iff _ _ _).mpr hi).trans_eq h₂)

def collapseGermIso : Germ (U : Filter I) (BelowCondition κ) ≃o BelowCondition θ := by
  let F (x : Germ (U : Filter I) (BelowCondition κ)) := Germ.liftOn x (upper U a hk hn ht) (fun f g h =>
    le_antisymm ((upper_le U a hk hn ht).mpr h.le) ((upper_le U a hk hn ht).mpr h.symm.le))
  have le (x y) : F x ≤ F y ↔ x ≤ y := by
    induction x,y using Germ.inductionOn₂ with
    | _ f g => exact upper_le U a hk hn ht
  let emb : Germ (U : Filter I) (BelowCondition κ) ↪o BelowCondition θ :=
    ⟨⟨F,fun x y eq => le_antisymm ((le x y).mp eq.le) ((le y x).mp eq.ge)⟩,le _ _⟩
  refine ⟨Equiv.ofBijective F ⟨emb.injective,?_⟩,le _ _⟩
  intro p
  obtain ⟨f,hf'⟩ := upper_condition_has_germ U a hk hf ht p
  obtain ⟨i,h₁,h₂⟩ := ((germ_has_upper_condition U a hk hn ht f).choose_spec.and hf').exists
  exact ⟨Germ.ofFun f,h₁.symm.trans h₂⟩

theorem collapseGermIso_spec (f : I → BelowCondition κ) :
    ∀ᶠ i in U, relabel (fiberEmbedding a hk i) (f i) = collapseGermIso U a hk hf hn ht (Germ.ofFun f) :=
  (germ_has_upper_condition U a hk hn ht f).choose_spec

end Erdos1172LevyCollapse.Preparation
