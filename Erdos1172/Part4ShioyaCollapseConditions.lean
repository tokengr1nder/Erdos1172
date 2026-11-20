/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4DualShioyaForcing
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! # Partial-function conditions for the uncountable Lévy collapse

The coordinate set is κ and the alphabet is arbitrary. A condition is
a functional graph of size strictly below κ, ordered by reverse inclusion.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.Collapse

structure Condition (κ : Cardinal.{u}) (α : Type u) where
  graph : Set (κ.ord.ToType × α)
  functional : ∀ {i x y}, (i, x) ∈ graph → (i, y) ∈ graph → x = y
  small : Cardinal.mk graph < κ

variable {κ : Cardinal.{u}} {α : Type u}

theorem graph_injective : Function.Injective (Condition.graph : Condition κ α → _) := by
  rintro ⟨g, _, _⟩ ⟨h, _, _⟩ rfl
  rfl

instance : PartialOrder (Condition κ α) :=
  PartialOrder.lift (fun p => OrderDual.toDual p.graph) graph_injective

theorem le_iff {p q : Condition κ α} : p ≤ q ↔ q.graph ⊆ p.graph := Iff.rfl

def empty (hκ : 0 < κ) : Condition κ α where
  graph := ∅
  functional := by simp
  small := by simpa using hκ

theorem le_empty (p : Condition κ α) (hκ : 0 < κ) : p ≤ empty hκ := Set.empty_subset _

theorem shortInfima (hκ : κ.IsRegular) : ShortInfima κ (Condition κ α) := by
  intro L _ _ hL f hf
  let g := ⋃ l : L, (f l).graph
  have hfun : ∀ {i x y}, (i, x) ∈ g → (i, y) ∈ g → x = y := by
    intro i x y hx hy
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
    rcases le_total l m with hlm | hml
    · exact (f m).functional ((le_iff.mp (hf hlm)) hl) hm
    · exact (f l).functional hl ((le_iff.mp (hf hml)) hm)
  have hsize : Cardinal.mk g < κ :=
    (Cardinal.mk_iUnion_le _).trans_lt (Cardinal.mul_lt_of_lt hκ.aleph0_le hL
      (Cardinal.iSup_lt_of_lt_cof_ord (a := κ) (by rwa [hκ.cof_ord]) (fun l => (f l).small)))
  refine ⟨⟨g, hfun, hsize⟩, ?_, ?_⟩
  · rintro _ ⟨l, rfl⟩
    exact le_iff.mpr (Set.subset_iUnion (fun j => (f j).graph) l)
  · intro q hq
    exact Set.iUnion_subset (fun l => le_iff.mp (hq (Set.mem_range_self l)))

def assign (p : Condition κ α) (hκ : Cardinal.aleph0 ≤ κ)
    (i : κ.ord.ToType) (x : α) (h : ∀ y, (i, y) ∈ p.graph → y = x) : Condition κ α where
  graph := insert (i, x) p.graph
  functional := by
    intro j y z hy hz
    rcases hy with h₁ | h₁ <;> rcases hz with h₂ | h₂
    · exact (Prod.mk.inj h₁).2.trans (Prod.mk.inj h₂).2.symm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
      exact (h z h₂).symm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
      exact h y h₁
    · exact p.functional h₁ h₂
  small := Cardinal.mk_insert_le.trans_lt
    (Cardinal.add_lt_of_lt hκ p.small (Cardinal.one_lt_aleph0.trans_le hκ))

theorem assign_le (p : Condition κ α) (hκ : Cardinal.aleph0 ≤ κ)
    (i : κ.ord.ToType) (x : α) (h : ∀ y, (i, y) ∈ p.graph → y = x) :
    assign p hκ i x h ≤ p := Set.subset_insert _ _

theorem mem_assign (p : Condition κ α) (hκ : Cardinal.aleph0 ≤ κ)
    (i : κ.ord.ToType) (x : α) (h : ∀ y, (i, y) ∈ p.graph → y = x) :
    (i, x) ∈ (assign p hκ i x h).graph := Set.mem_insert _ _

theorem exists_fresh (p : Condition κ α) : ∃ i, ∀ x, (i, x) ∉ p.graph := by
  classical
  by_contra! hall
  have hfull : Prod.fst '' p.graph = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    obtain ⟨x, hx⟩ := hall i
    exact ⟨(i, x), hx, rfl⟩
  have hs : Cardinal.mk (Prod.fst '' p.graph) < κ := Cardinal.mk_image_le.trans_lt p.small
  rw [hfull, Cardinal.mk_univ, Cardinal.mk_ord_toType] at hs
  exact (lt_irrefl κ) hs

theorem exists_assign [Nonempty α] (hκ : Cardinal.aleph0 ≤ κ) (p : Condition κ α)
    (i : κ.ord.ToType) : ∃ q ≤ p, ∃ x, (i, x) ∈ q.graph := by
  classical
  by_cases h : ∃ x, (i, x) ∈ p.graph
  · exact ⟨p, le_rfl, h⟩
  · let x := Classical.choice ‹Nonempty α›
    have hf (y : α) (hy : (i, y) ∈ p.graph) : y = x := (h ⟨y, hy⟩).elim
    exact ⟨assign p hκ i x hf, assign_le p hκ i x hf, x, mem_assign p hκ i x hf⟩

theorem exists_hit (hκ : Cardinal.aleph0 ≤ κ) (p : Condition κ α) (x : α) :
    ∃ q ≤ p, ∃ i, (i, x) ∈ q.graph := by
  obtain ⟨i, hi⟩ := exists_fresh p
  have hf (y : α) (hy : (i, y) ∈ p.graph) : y = x := (hi y hy).elim
  exact ⟨assign p hκ i x hf, assign_le p hκ i x hf, i, mem_assign p hκ i x hf⟩

theorem separative [Nontrivial α] (hκ : Cardinal.aleph0 ≤ κ) : Separative (Condition κ α) := by
  classical
  intro p q hpq
  obtain ⟨⟨i, x⟩, hx, hn⟩ := Set.not_subset.mp (show ¬q.graph ⊆ p.graph from hpq)
  suffices hd : ∃ r ≤ p, ∃ y, (i, y) ∈ r.graph ∧ y ≠ x by
    obtain ⟨r, hrp, y, hy, hne⟩ := hd
    refine ⟨r, hrp, ?_⟩
    rintro ⟨t, htr, htq⟩
    exact hne (t.functional (le_iff.mp htr hy) (le_iff.mp htq hx))
  by_cases h : ∃ y, (i, y) ∈ p.graph
  · obtain ⟨y, hy⟩ := h
    exact ⟨p, le_rfl, y, hy, fun he => hn (he ▸ hy)⟩
  · obtain ⟨y, hne⟩ := exists_ne x
    have hf (z : α) (hz : (i, z) ∈ p.graph) : z = y := (h ⟨z, hz⟩).elim
    exact ⟨assign p hκ i y hf, assign_le p hκ i y hf, y, mem_assign p hκ i y hf, hne⟩

theorem cardinal_lt {θ : Cardinal.{u}} (hθ : θ.IsInaccessible) (hκ : κ < θ) (hα : Cardinal.mk α < θ) :
    Cardinal.mk (Condition κ α) < θ := by
  apply (Cardinal.mk_le_of_injective graph_injective).trans_lt
  rw [Cardinal.mk_set, Cardinal.mk_prod, Cardinal.mk_ord_toType]
  simp only [Cardinal.lift_id]
  exact hθ.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hκ hα)

end Erdos1172Shioya.Collapse
