/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Card
public import Erdos1172.Statement

@[expose] public section

open Cardinal Ordinal

universe u

namespace Ordinal

/-- Every smaller ordinal occurs as the order type of a subset of a well-ordered set. -/
theorem exists_subset_typeLT_eq {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) {β : Ordinal.{u}} (hβ : β ≤ typeLT s) :
    ∃ t : Set α, t ⊆ s ∧ typeLT t = β := by
  have htype : typeLT β.ToType ≤ typeLT s := by
    simpa only [type_toType] using hβ
  obtain ⟨f⟩ := type_le_iff.mp htype
  let e : β.ToType ↪o α :=
    f.toOrderEmbedding.trans (OrderEmbedding.subtype fun x ↦ x ∈ s)
  refine ⟨Set.range e, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (f x).property
  · exact e.orderIso.ordinalType_congr.symm.trans (type_toType β)

end Ordinal

namespace OrdinalRamsey

/-- The binary ordinal partition relation is monotone downwards in both targets. -/
theorem mono_targets {α β β' γ γ' : Ordinal.{u}}
    (h : OrdinalRamsey α β γ) (hβ : β' ≤ β) (hγ : γ' ≤ γ) :
    OrdinalRamsey α β' γ' := by
  intro red blue hcompl
  obtain ⟨s, hs, hstype⟩ | ⟨s, hs, hstype⟩ := h red blue hcompl
  · obtain ⟨t, hts, httype⟩ :=
      Ordinal.exists_subset_typeLT_eq s (hβ.trans_eq hstype.symm)
    exact Or.inl ⟨t, hs.subset hts, httype⟩
  · obtain ⟨t, hts, httype⟩ :=
      Ordinal.exists_subset_typeLT_eq s (hγ.trans_eq hstype.symm)
    exact Or.inr ⟨t, hs.subset hts, httype⟩

/-- Swapping the two complementary colors swaps the two targets. -/
theorem swap {α β γ : Ordinal.{u}} (h : OrdinalRamsey α β γ) :
    OrdinalRamsey α γ β := by
  intro red blue hcompl
  obtain ⟨s, hs, hstype⟩ | ⟨s, hs, hstype⟩ := h blue red hcompl.symm
  · exact Or.inr ⟨s, hs, hstype⟩
  · exact Or.inl ⟨s, hs, hstype⟩

/-- If the source contains the blue target, then `α → (2, γ)²`. -/
theorem two_left {α γ : Ordinal.{u}} (hγ : γ ≤ α) : OrdinalRamsey α 2 γ := by
  classical
  intro red blue hcompl
  by_cases hred : ∃ x y, red.Adj x y
  · obtain ⟨x, y, hxy⟩ := hred
    refine Or.inl ⟨{x, y}, ?_, ?_⟩
    · rw [SimpleGraph.isClique_pair]
      exact fun _ ↦ hxy
    · rw [Ordinal.type_fintype, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq, Set.ncard_pair hxy.ne]
      simp
  · have huniv : typeLT (Set.univ : Set α.ToType) = α :=
      (OrderIso.Set.univ.ordinalType_congr).trans (Ordinal.type_toType α)
    obtain ⟨t, -, httype⟩ :=
      Ordinal.exists_subset_typeLT_eq (Set.univ : Set α.ToType) (hγ.trans_eq huniv.symm)
    refine Or.inr ⟨t, ?_, httype⟩
    intro x _ y _ hxy
    rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
    exact ⟨hxy, fun h ↦ hred ⟨x, y, h⟩⟩

/-- If the source contains the red target, then `α → (β, 2)²`. -/
theorem two_right {α β : Ordinal.{u}} (hβ : β ≤ α) : OrdinalRamsey α β 2 :=
  (two_left hβ).swap

end OrdinalRamsey
