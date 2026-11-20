/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Card
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelation

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

/-- The binary ordinal partition relation is monotone downwards in the red target. -/
theorem mono_red {α β β' γ : Ordinal.{u}}
    (h : OrdinalRamsey α β γ) (hβ : β' ≤ β) : OrdinalRamsey α β' γ :=
  h.mono_targets hβ le_rfl

/-- The binary ordinal partition relation is monotone downwards in the blue target. -/
theorem mono_blue {α β γ γ' : Ordinal.{u}}
    (h : OrdinalRamsey α β γ) (hγ : γ' ≤ γ) : OrdinalRamsey α β γ' :=
  h.mono_targets le_rfl hγ

/-- Swapping the two complementary colors swaps the two targets. -/
theorem swap {α β γ : Ordinal.{u}} (h : OrdinalRamsey α β γ) :
    OrdinalRamsey α γ β := by
  intro red blue hcompl
  obtain ⟨s, hs, hstype⟩ | ⟨s, hs, hstype⟩ := h blue red hcompl.symm
  · exact Or.inr ⟨s, hs, hstype⟩
  · exact Or.inl ⟨s, hs, hstype⟩

/-- Color symmetry as an equivalence. -/
theorem swap_iff {α β γ : Ordinal.{u}} :
    OrdinalRamsey α β γ ↔ OrdinalRamsey α γ β :=
  ⟨swap, swap⟩

/-- Enlarging the source preserves a binary ordinal partition relation. -/
theorem mono_source {α α' β γ : Ordinal.{u}}
    (h : OrdinalRamsey α β γ) (hα : α ≤ α') : OrdinalRamsey α' β γ := by
  classical
  have htype : typeLT α.ToType ≤ typeLT α'.ToType := by
    simpa only [Ordinal.type_toType] using hα
  let f := Classical.choice (Ordinal.type_le_iff.mp htype)
  let e : α.ToType ↪o α'.ToType := f.toOrderEmbedding
  intro red blue hcompl
  obtain ⟨s, hs, hstype⟩ | ⟨s, hs, hstype⟩ :=
    h (red.comap e) ((red.comap e)ᶜ) isCompl_compl
  · refine Or.inl ⟨e '' s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hs hx hy fun hxy' ↦ hxy (congrArg e hxy')
    · have heq : typeLT s = typeLT (e '' s) :=
        ((e.strictMono.strictMonoOn s).orderIso e s).ordinalType_congr
      exact heq.symm.trans hstype
  · refine Or.inr ⟨e '' s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have hedge := hs hx hy fun hxy' ↦ hxy (congrArg e hxy')
      rw [SimpleGraph.compl_adj] at hedge
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨hxy, hedge.2⟩
    · have heq : typeLT s = typeLT (e '' s) :=
        ((e.strictMono.strictMonoOn s).orderIso e s).ordinalType_congr
      exact heq.symm.trans hstype

/-- Simultaneous source and target monotonicity. -/
theorem mono {α α' β β' γ γ' : Ordinal.{u}}
    (h : OrdinalRamsey α β γ) (hα : α ≤ α') (hβ : β' ≤ β) (hγ : γ' ≤ γ) :
    OrdinalRamsey α' β' γ' :=
  (h.mono_source hα).mono_targets hβ hγ

/-- Transport the three ordinal parameters across equalities. -/
theorem congr {α α' β β' γ γ' : Ordinal.{u}}
    (hα : α = α') (hβ : β = β') (hγ : γ = γ') :
    OrdinalRamsey α β γ ↔ OrdinalRamsey α' β' γ' := by
  subst α'
  subst β'
  subst γ'
  rfl

/-- An order isomorphism between the source types transports the partition relation. -/
theorem iff_of_source_orderIso {α α' β γ : Ordinal.{u}}
    (e : α.ToType ≃o α'.ToType) :
    OrdinalRamsey α β γ ↔ OrdinalRamsey α' β γ := by
  have hα : α = α' := by
    simpa only [Ordinal.type_toType] using e.ordinalType_congr
  exact congr hα rfl rfl

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
