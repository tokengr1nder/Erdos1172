/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceFunctionNames

@[expose] public section

/-!
# A small ground cover of every possible point decision

The chain condition bounds possible values at each coordinate by
alephOne. Thus an at-most-alephOne-indexed decision system has a single
ground set of that size containing all its possible values, not merely
the values along one chosen descending sequence.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3SmallDecisionRange

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)

variable {P I V : Type} [Preorder P]

theorem exists_small_value_cover (hcc : OmegaTwoCC P) (hI : #I ≤ ℵ_ 1)
    (F : FunctionDecisions P I V) :
    ∃ R : Set V, #R ≤ ℵ_ 1 ∧ ∀ p i v, F.decides p i v → v ∈ R := by
  obtain ⟨N, hN⟩ := Erdos1172Part3NiceFunctionNames.exists_nice_name hcc F
  let R : Set V := ⋃ i : I, Prod.snd '' N.graph i
  have hsmall : #R ≤ ℵ_ 1 := by
    calc
      #R ≤ Cardinal.sum (fun i : I => #(Prod.snd '' N.graph i)) :=
        Cardinal.mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : I => (ℵ_ 1 : Cardinal.{0})) :=
        Cardinal.sum_le_sum _ _ (fun i => Cardinal.mk_image_le.trans (N.small i))
      _ = #I * ℵ_ 1 := Cardinal.sum_const' I (ℵ_ 1)
      _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' hI le_rfl
      _ = ℵ_ 1 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)
  refine ⟨R, hsmall, ?_⟩
  intro p i v hv
  obtain ⟨q, hqp, w, hw⟩ := N.toDecisions.dense p i
  have heq : v = w := F.unique (F.persistent hqp hv) (hN q i w hw)
  obtain ⟨r, hr, _⟩ := hw
  subst w
  exact Set.mem_iUnion.mpr ⟨i, (r, v), hr, rfl⟩

theorem exists_small_clique_cover [LinearOrder I] [LinearOrder V]
    (hcc : OmegaTwoCC P) (hI : #I ≤ ℵ_ 1) {G : SimpleGraph V}
    (core : CliqueDecisions P I V G) :
    ∃ R : Set V, #R ≤ ℵ_ 1 ∧ ∀ p i v, core.decides p i v → v ∈ R :=
  exists_small_value_cover hcc hI
    ⟨core.decides, core.dense, core.persistent, core.unique⟩

end Erdos1172Part3SmallDecisionRange
