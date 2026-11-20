/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ConvergentSquareCore

@[expose] public section

/-!
# The finite ideal of ordinal-small traces on a red square

Finite unions of traces of order type below omegaOne squared remain
small. Every positive set contains a red square from the original core.
Countable completeness is neither needed nor asserted.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3SquareTraceIdeal

open Erdos1172Part3CoreObjectCode Erdos1172Part3CoreObjectIdeal
open Erdos1172Part3ConvergentSquareCore
open Erdos1172Part3LocalRedBlock
open Erdos1172Part3FiniteIdealEndpoint (FiniteSmallness)
open ErdosRadoCHAsym (W2)

theorem square_pos : (0 : Ordinal.{0}) < (ω_ 1) ^ (2 : Ordinal.{0}) :=
  Ordinal.opow_pos _ (Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1))

theorem typeLT_union_lt_square {s t : Set W2}
    (hs : typeLT s < (ω_ 1) ^ (2 : Ordinal.{0}))
    (ht : typeLT t < (ω_ 1) ^ (2 : Ordinal.{0})) :
    typeLT (s ∪ t : Set W2) < (ω_ 1) ^ (2 : Ordinal.{0}) := by
  have hprincipal := Ordinal.isPrincipal_add_opow_of_isPrincipal_add
    (Ordinal.isPrincipal_add_omega (1 : Ordinal.{0})) (2 : Ordinal.{0})
  obtain hzero | ⟨e, he⟩ := Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hprincipal
  · exact (square_pos.ne' hzero).elim
  · change (ω : Ordinal.{0}) ^ e = (ω_ 1) ^ (2 : Ordinal.{0}) at he
    rw [← he] at hs ht ⊢
    exact Erdos1172Part3BHTFiniteCommonBlueColumns.typeLT_union_lt_opow hs ht

def squareTraceSmallness (core : Set W2) : FiniteSmallness W2 where
  small := SquareTraceSmall core
  empty_small := by
    change typeLT (core ∩ (∅ : Set W2) : Set W2) < (ω_ 1) ^ (2 : Ordinal.{0})
    rw [Set.inter_empty]
    simpa only [Ordinal.type_eq_zero_of_empty] using square_pos
  mono := by
    intro s t hst ht
    exact (Ordinal.type_mono (Set.inter_subset_inter_right core hst)).trans_lt ht
  union_small := by
    intro s t hs ht
    change typeLT (core ∩ (s ∪ t) : Set W2) < _
    rw [Set.inter_union_distrib_left]
    exact typeLT_union_lt_square hs ht

theorem core_of_square_trace_positive {G : SimpleGraph W2} {core x : Set W2}
    (hc : G.IsClique core) (ht : typeLT core = (ω_ 1) ^ (2 : Ordinal.{0}))
    (hx : ¬SquareTraceSmall core x) :
    G.IsClique (core ∩ x) ∧ typeLT (core ∩ x : Set W2) = (ω_ 1) ^ (2 : Ordinal.{0}) := by
  exact ⟨hc.subset Set.inter_subset_left,
    ((Ordinal.type_mono Set.inter_subset_left).trans_eq ht).antisymm (le_of_not_gt hx)⟩

structure SquareCoreData (r : Code ↪ W2) (G H : SimpleGraph W2)
    (source : Set W2) (a : W2) where
  core : Set W2
  subset_prior : core ⊆ source ∩ Set.Iio a
  clique : G.IsClique core
  type_eq : typeLT core = (ω_ 1) ^ (2 : Ordinal.{0})
  cofinal : IsLUB core a
  small_traces : ∀ x : Set W2, Small r G H a x → SquareTraceSmall core x

theorem squareCoreData_of_local_red_block {r : Code ↪ W2} {σ : Obj ↪ W2}
    {G H : SimpleGraph W2} {source : Set W2} {a : W2}
    (ha : GoodCut r σ G H a) (hlocal : LocalRedBlock r σ G H source a) :
    Nonempty (SquareCoreData r G H source a) := by
  obtain ⟨core, hsub, hclique, htype, hcofinal, htraces⟩ :=
    exists_cofinal_square_with_small_traces ha source hlocal
  exact ⟨⟨core, hsub, hclique, htype, hcofinal, htraces⟩⟩

end Erdos1172Part3SquareTraceIdeal
