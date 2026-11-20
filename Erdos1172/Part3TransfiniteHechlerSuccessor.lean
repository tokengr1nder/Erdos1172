/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteStageLocality

@[expose] public section

/-!
# Identifying a successor carrier with a named Hechler stage

The final coordinate is decoded using the earlier stage's exact name
dictionary. Conversely, its side names are encoded bijectively and the
final coordinate is normalized. The maps retain the earlier sparse
condition exactly, including when the new coordinate is wholly empty.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TransfiniteHechlerSuccessor

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3CountableSupportProfiles (support)
open Erdos1172Part3SparseIterationCarriers
open Erdos1172Part3SparseIterationUnions
open Erdos1172Part3TransfiniteHechlerOrder
open Erdos1172Part3TransfiniteStageLocality (Earlier)
open Erdos1172Part3NiceFunctionNames (NiceFunctionName)
open Erdos1172Part3IteratedHechlerOrder (Condition)

local instance : NoMaxOrder W2 := by
  change NoMaxOrder (ω_ 2).ToType
  rw [← Cardinal.ord_aleph]
  exact Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph 2)

noncomputable def next (i : W2) : W2 := Order.succ i

theorem lt_next (i : W2) : i < next i := Order.lt_succ i

theorem lt_next_iff (i j : W2) : j < next i ↔ j ≤ i := Order.lt_succ_iff

noncomputable def nameEquiv (hGCH : GCH) (i : W2) :
    W2 ≃ NiceFunctionName (Earlier hGCH i) W1 W1 := (stage hGCH (i : Cut)).decode

noncomputable def toStep (hGCH : GCH) (i : W2) (p : Earlier hGCH (next i)) :
    Condition (Earlier hGCH i) where
  base := truncate p.val (i : Cut)
  stem := (stemAt p i).val
  stem_countable := (stemAt p i).property
  side := nameEquiv hGCH i '' (sideAt p i).val
  side_countable := (sideAt p i).property.image _

noncomputable def encodedData (hGCH : GCH) (i : W2) (p : Condition (Earlier hGCH i)) :
    Erdos1172Part3HechlerCentering.Stem × SideCodes :=
  (⟨p.stem, p.stem_countable⟩,
    ⟨(nameEquiv hGCH i).symm '' p.side, p.side_countable.image _⟩)

theorem encodedData_toStep (hGCH : GCH) (i : W2) (p : Earlier hGCH (next i)) :
    encodedData hGCH i (toStep hGCH i p) = dataAt p i := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (nameEquiv hGCH i).symm '' (nameEquiv hGCH i '' (sideAt p i).val) =
      (sideAt p i).val
    simp

noncomputable def fromStep (hGCH : GCH) (i : W2) (p : Condition (Earlier hGCH i)) :
    Earlier hGCH (next i) := by
  classical
  let f (j : W2) := if j = i then pack (encodedData hGCH i p) else value p.base j
  have hs : {j | f j ≠ none} ⊆ insert i (support p.base.val) := by
    intro j hj
    by_cases hji : j = i
    · exact Or.inl hji
    · right
      change value p.base j ≠ none
      change f j ≠ none at hj
      simpa only [f, if_neg hji] using hj
  refine ⟨⟨f, (p.base.val.property.insert i).mono hs⟩, ?_⟩
  intro j hj
  rcases hs hj with rfl | hjp
  · exact WithTop.coe_lt_coe.mpr (lt_next _)
  · exact (p.base.property j hjp).trans (WithTop.coe_lt_coe.mpr (lt_next i))

theorem value_fromStep (hGCH : GCH) (i : W2) (p : Condition (Earlier hGCH i)) (j : W2) :
    value (fromStep hGCH i p) j =
      if j = i then pack (encodedData hGCH i p) else value p.base j := by
  classical
  rfl

theorem dataAt_fromStep (hGCH : GCH) (i : W2) (p : Condition (Earlier hGCH i)) :
    dataAt (fromStep hGCH i p) i = encodedData hGCH i p := by
  classical
  change unpack (value (fromStep hGCH i p) i) = encodedData hGCH i p
  rw [value_fromStep hGCH i p i, if_pos rfl, unpack_pack]

theorem truncate_fromStep (hGCH : GCH) (i : W2) (p : Condition (Earlier hGCH i)) :
    truncate (fromStep hGCH i p).val (i : Cut) = p.base := by
  classical
  apply carrier_ext
  intro j
  by_cases hji : j < i
  · rw [value_truncate, if_pos (WithTop.coe_lt_coe.mpr hji)]
    change value (fromStep hGCH i p) j = value p.base j
    rw [value_fromStep hGCH i p j, if_neg hji.ne]
  · rw [value_truncate, if_neg (by simpa only [WithTop.coe_lt_coe] using hji)]
    exact (value_none_of_not_lt p.base (by simpa only [WithTop.coe_lt_coe] using hji)).symm

theorem fromStep_toStep (hGCH : GCH) (i : W2) (p : Earlier hGCH (next i)) :
    fromStep hGCH i (toStep hGCH i p) = p := by
  classical
  apply carrier_ext
  intro j
  rw [value_fromStep hGCH i (toStep hGCH i p) j]
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl, encodedData_toStep]
    exact pack_unpack (value p i)
  · rw [if_neg hji]
    change value (truncate p.val (i : Cut)) j = value p j
    by_cases hjlt : j < i
    · rw [value_truncate, if_pos (WithTop.coe_lt_coe.mpr hjlt)]
      rfl
    · rw [value_truncate, if_neg (by simpa only [WithTop.coe_lt_coe] using hjlt)]
      apply (value_none_of_not_lt p ?_).symm
      intro h
      exact hji (le_antisymm ((lt_next_iff i j).mp (WithTop.coe_lt_coe.mp h))
        (le_of_not_gt hjlt))

theorem condition_ext {P : Type} [Preorder P] {p q : Condition P}
    (hb : p.base = q.base) (hs : p.stem = q.stem) (ht : p.side = q.side) : p = q := by
  cases p
  cases q
  cases hb
  cases hs
  cases ht
  rfl

theorem toStep_fromStep (hGCH : GCH) (i : W2) (p : Condition (Earlier hGCH i)) :
    toStep hGCH i (fromStep hGCH i p) = p := by
  apply condition_ext
  · exact truncate_fromStep hGCH i p
  · change (dataAt (fromStep hGCH i p) i).1.val = p.stem
    rw [dataAt_fromStep]
    rfl
  · change nameEquiv hGCH i '' (dataAt (fromStep hGCH i p) i).2.val = p.side
    rw [dataAt_fromStep]
    change nameEquiv hGCH i '' ((nameEquiv hGCH i).symm '' p.side) = p.side
    simp

noncomputable def carrierEquiv (hGCH : GCH) (i : W2) :
    Earlier hGCH (next i) ≃ Condition (Earlier hGCH i) where
  toFun := toStep hGCH i
  invFun := fromStep hGCH i
  left_inv := fromStep_toStep hGCH i
  right_inv := toStep_fromStep hGCH i

end Erdos1172Part3TransfiniteHechlerSuccessor
