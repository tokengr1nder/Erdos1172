/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteHechlerSuccessor

@[expose] public section

/-!
# Exact successor orders and their full-iteration restrictions

The carrier bijection preserves and reflects the actual named Hechler
relation, including every new-value bound. Composing with the full-stage
restriction gives a complete restriction to each named successor, with
exact agreement of its base with the earlier full-stage projection.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TransfiniteHechlerSuccessorOrder

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3SparseIterationCarriers
open Erdos1172Part3SparseIterationUnions
open Erdos1172Part3TransfiniteHechlerOrder
open Erdos1172Part3TransfiniteHechlerClosure (stemAt_mono)
open Erdos1172Part3TransfiniteHechlerSuccessor
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3IteratedHechlerOrder (Condition)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3FunctionDecisions (BoundedAt)

theorem sideAt_mono (hGCH : GCH) {a : Cut} {q p : Stage hGCH a} (hqp : q ≤ p)
    (i : W2) : (sideAt p i).val ⊆ (sideAt q i).val := by
  cases hd : value p i with
  | none =>
    have hs : sideAt p i = emptySide := congrArg Prod.snd (dataAt_of_none hd)
    rw [hs]
    exact Set.empty_subset _
  | some d =>
    obtain ⟨e, he, hed⟩ := (le_iff hGCH q p).mp hqp i (lt_of_value_some hd) d hd
    rw [sideAt_of_some hd, sideAt_of_some he]
    exact hed.2.1

theorem active_of_field_extensions {a : Cut} {q p : Carrier a} {i : W2}
    (hs : ∀ j v, (stemAt p i).val j = some v → (stemAt q i).val j = some v)
    (ht : (sideAt p i).val ⊆ (sideAt q i).val) {d : Datum} (hd : value p i = some d) :
    ∃ e : Datum, value q i = some e := by
  cases he : value q i with
  | some e => exact ⟨e, rfl⟩
  | none =>
    have hqs : stemAt q i = emptyStem := congrArg Prod.fst (dataAt_of_none he)
    have hqt : sideAt q i = emptySide := congrArg Prod.snd (dataAt_of_none he)
    apply False.elim
    apply d.property
    apply Prod.ext
    · apply Subtype.ext
      funext j
      cases hv : d.val.1.val j with
      | none => rfl
      | some v =>
        have hpv : (stemAt p i).val j = some v := by rw [stemAt_of_some hd]; exact hv
        have hqv := hs j v hpv
        rw [hqs] at hqv
        cases hqv
    · apply Subtype.ext
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have hcp : c ∈ (sideAt p i).val := by rw [sideAt_of_some hd]; exact hc
      have hcq := ht hcp
      rw [hqt] at hcq
      exact hcq

theorem toStep_mono (hGCH : GCH) (i : W2) : Monotone (toStep hGCH i) := by
  intro q p hqp
  refine ⟨Erdos1172Part3TransfiniteHechlerRestrictions.restrict_le hGCH
    (WithTop.coe_le_coe.mpr (lt_next i).le) hqp, ?_, ?_, ?_⟩
  · intro j v hv
    exact stemAt_mono hGCH hqp hv
  · rintro F ⟨c, hc, rfl⟩
    exact ⟨c, sideAt_mono hGCH hqp i hc, rfl⟩
  · rintro j hpj v hqv F ⟨c, hc, rfl⟩
    change (stemAt p i).val j = none at hpj
    change (stemAt q i).val j = some v at hqv
    cases hd : value p i with
    | none =>
      have ht : sideAt p i = emptySide := congrArg Prod.snd (dataAt_of_none hd)
      rw [ht] at hc
      exact hc.elim
    | some d =>
      obtain ⟨e, he, hed⟩ := (le_iff hGCH q p).mp hqp i (lt_of_value_some hd) d hd
      rw [stemAt_of_some hd] at hpj
      rw [stemAt_of_some he] at hqv
      rw [sideAt_of_some hd] at hc
      exact hed.2.2 j hpj v hqv c hc

theorem le_of_toStep_le (hGCH : GCH) (i : W2) {q p : Earlier hGCH (next i)}
    (hqp : toStep hGCH i q ≤ toStep hGCH i p) : q ≤ p := by
  classical
  apply (le_iff hGCH q p).mpr
  intro j hj d hd
  by_cases hji : j < i
  · have hbase := hqp.1
    have hpd : value (toStep hGCH i p).base j = some d := by
      change value (truncate p.val (i : Cut)) j = some d
      rw [value_truncate, if_pos (WithTop.coe_lt_coe.mpr hji)]
      exact hd
    obtain ⟨e, he, hed⟩ := (le_iff hGCH _ _).mp hbase j (WithTop.coe_lt_coe.mpr hji) d hpd
    refine ⟨e, ?_, ?_⟩
    · change value (truncate q.val (i : Cut)) j = some e at he
      rwa [value_truncate q.val (i : Cut) j, if_pos (WithTop.coe_lt_coe.mpr hji)] at he
    · change DatumExtends (stage hGCH (j : Cut))
        (truncate (truncate q.val (i : Cut)).val (j : Cut)) e d at hed
      rwa [truncate_truncate q.val (WithTop.coe_le_coe.mpr hji.le)] at hed
  · have hjeq : j = i := le_antisymm ((lt_next_iff i j).mp (WithTop.coe_lt_coe.mp hj))
      (le_of_not_gt hji)
    subst j
    have hs : ∀ j v, (stemAt p i).val j = some v → (stemAt q i).val j = some v := hqp.2.1
    have ht : (sideAt p i).val ⊆ (sideAt q i).val := by
      intro c hc
      obtain ⟨e, he, hec⟩ := hqp.2.2.1 (show nameEquiv hGCH i c ∈ (toStep hGCH i p).side
        from ⟨c, hc, rfl⟩)
      have heq : e = c := (nameEquiv hGCH i).injective hec
      exact heq ▸ he
    obtain ⟨e, he⟩ := active_of_field_extensions hs ht hd
    refine ⟨e, he, ?_, ?_, ?_⟩
    · intro j v hdv
      have hpv : (stemAt p i).val j = some v := by rw [stemAt_of_some hd]; exact hdv
      have hqv := hs j v hpv
      rwa [stemAt_of_some he] at hqv
    · rwa [sideAt_of_some hd, sideAt_of_some he] at ht
    · intro j hdj v hev c hcd
      have hpj : (toStep hGCH i p).stem j = none := by
        change (stemAt p i).val j = none
        rw [stemAt_of_some hd]
        exact hdj
      have hqv : (toStep hGCH i q).stem j = some v := by
        change (stemAt q i).val j = some v
        rw [stemAt_of_some he]
        exact hev
      have hcp : c ∈ (sideAt p i).val := by rw [sideAt_of_some hd]; exact hcd
      exact hqp.2.2.2 j hpj v hqv (nameEquiv hGCH i c) ⟨c, hcp, rfl⟩

noncomputable def orderIso (hGCH : GCH) (i : W2) :
    Earlier hGCH (next i) ≃o Condition (Earlier hGCH i) where
  toEquiv := carrierEquiv hGCH i
  map_rel_iff' := ⟨le_of_toStep_le hGCH i, fun h => toStep_mono hGCH i h⟩

noncomputable def fullSuccessorRestriction (hGCH : GCH) (i : W2) :
    CompleteRestriction (Full hGCH) (Condition (Earlier hGCH i)) where
  restrict := ⟨fun p => orderIso hGCH i ((restriction hGCH (next i)).restrict p),
    fun _ _ h => (orderIso hGCH i).monotone ((restriction hGCH (next i)).restrict.monotone h)⟩
  embed := ⟨fun q => (restriction hGCH (next i)).embed ((orderIso hGCH i).symm q),
    fun _ _ h => (restriction hGCH (next i)).embed.monotone ((orderIso hGCH i).symm.monotone h)⟩
  restrict_embed q := by
    change orderIso hGCH i ((restriction hGCH (next i)).restrict
      ((restriction hGCH (next i)).embed ((orderIso hGCH i).symm q))) = q
    rw [(restriction hGCH (next i)).restrict_embed, OrderIso.apply_symm_apply]
  below_embed p := by
    change p ≤ (restriction hGCH (next i)).embed
      ((orderIso hGCH i).symm (orderIso hGCH i ((restriction hGCH (next i)).restrict p)))
    rw [OrderIso.symm_apply_apply]
    exact (restriction hGCH (next i)).below_embed p
  lift p q hqp := by
    have hraw : (orderIso hGCH i).symm q ≤ (restriction hGCH (next i)).restrict p := by
      have h := (orderIso hGCH i).symm.monotone hqp
      change (orderIso hGCH i).symm q ≤
        (orderIso hGCH i).symm (orderIso hGCH i ((restriction hGCH (next i)).restrict p)) at h
      rwa [OrderIso.symm_apply_apply] at h
    obtain ⟨s, hsp, hs⟩ := (restriction hGCH (next i)).lift p ((orderIso hGCH i).symm q) hraw
    refine ⟨s, hsp, ?_⟩
    change orderIso hGCH i ((restriction hGCH (next i)).restrict s) = q
    rw [hs, OrderIso.apply_symm_apply]

theorem fullSuccessorRestriction_base (hGCH : GCH) (i : W2) (p : Full hGCH) :
    ((fullSuccessorRestriction hGCH i).restrict p).base = (restriction hGCH i).restrict p :=
  truncate_truncate p.val (WithTop.coe_le_coe.mpr (lt_next i).le)

end Erdos1172Part3TransfiniteHechlerSuccessorOrder
