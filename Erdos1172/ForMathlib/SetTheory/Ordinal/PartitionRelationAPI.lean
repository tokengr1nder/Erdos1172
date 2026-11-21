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

end OrdinalRamsey
