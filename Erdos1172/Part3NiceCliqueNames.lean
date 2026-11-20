/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SmallDecisionRange

@[expose] public section

/-!
# Small names for ordered cliques

Clique decisions have small predense representations. The representation
retains order and adjacency, and its full set of possible values is small.
That value set is a cover, not necessarily a clique.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3NiceCliqueNames

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3NiceFunctionNames (NiceFunctionName)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)

structure NiceCliqueName (P I V : Type) [Preorder P] [LinearOrder I] [LinearOrder V]
    (G : SimpleGraph V) where
  function : NiceFunctionName P I V
  ordered : ∀ {p i j x y}, i < j → function.toDecisions.decides p i x →
    function.toDecisions.decides p j y → x < y
  adjacent : ∀ {p i j x y}, i ≠ j → function.toDecisions.decides p i x →
    function.toDecisions.decides p j y → G.Adj x y

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}

def NiceCliqueName.toClique (N : NiceCliqueName P I V G) : CliqueDecisions P I V G where
  decides := N.function.toDecisions.decides
  dense := N.function.toDecisions.dense
  persistent := N.function.toDecisions.persistent
  unique := N.function.toDecisions.unique
  ordered := N.ordered
  adjacent := N.adjacent

theorem NiceCliqueName.ext {N M : NiceCliqueName P I V G} (h : N.function = M.function) :
    N = M := by
  cases N
  cases M
  cases h
  rfl

theorem exists_nice_clique_name (hcc : OmegaTwoCC P) (core : CliqueDecisions P I V G) :
    ∃ N : NiceCliqueName P I V G,
      ∀ p i x, N.toClique.decides p i x → core.decides p i x := by
  let F : FunctionDecisions P I V :=
    ⟨core.decides, core.dense, core.persistent, core.unique⟩
  obtain ⟨N, hN⟩ := Erdos1172Part3NiceFunctionNames.exists_nice_name hcc F
  exact ⟨⟨N, fun h hx hy => core.ordered h (hN _ _ _ hx) (hN _ _ _ hy),
    fun h hx hy => core.adjacent h (hN _ _ _ hx) (hN _ _ _ hy)⟩, hN⟩

def NiceCliqueName.values (N : NiceCliqueName P I V G) : Set V :=
  ⋃ i : I, Prod.snd '' N.function.graph i

theorem NiceCliqueName.mk_values_le (N : NiceCliqueName P I V G) (hI : #I ≤ ℵ_ 1) :
    #N.values ≤ ℵ_ 1 := by
  calc
    #N.values ≤ Cardinal.sum (fun i : I => #(Prod.snd '' N.function.graph i)) :=
      Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : I => (ℵ_ 1 : Cardinal.{0})) :=
      Cardinal.sum_le_sum _ _ (fun i => Cardinal.mk_image_le.trans (N.function.small i))
    _ = #I * ℵ_ 1 := Cardinal.sum_const' I (ℵ_ 1)
    _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' hI le_rfl
    _ = ℵ_ 1 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)

theorem NiceCliqueName.mem_values_of_decides (N : NiceCliqueName P I V G)
    {p : P} {i : I} {x : V} (hx : N.toClique.decides p i x) : x ∈ N.values := by
  obtain ⟨q, hq, _⟩ := hx
  exact Set.mem_iUnion.mpr ⟨i, (q, x), hq, rfl⟩

/-- The graph values are exactly the possible point decisions. In
particular, this cover does not add extraneous vertices. -/
theorem NiceCliqueName.values_eq_possible (N : NiceCliqueName P I V G) :
    N.values = {x : V | ∃ p : P, ∃ i : I, N.toClique.decides p i x} := by
  ext x
  constructor
  · rintro hx
    obtain ⟨i, pair, hp, heq⟩ := Set.mem_iUnion.mp hx
    refine ⟨pair.1, i, pair.1, ?_, le_rfl⟩
    cases pair with
    | mk p v =>
      change v = x at heq
      subst x
      exact hp
  · rintro ⟨p, i, hx⟩
    exact N.mem_values_of_decides hx

/-- Small-name normalization preserves all ground pointwise properties
below a condition, including source containment and common-future edges. -/
theorem ground_property_iff_of_refines (core : CliqueDecisions P I V G)
    (N : NiceCliqueName P I V G)
    (href : ∀ p i x, N.toClique.decides p i x → core.decides p i x)
    (p0 : P) (B : I → V → Prop) :
    (∀ p : P, p ≤ p0 → ∀ i x, N.toClique.decides p i x → B i x) ↔
      (∀ p : P, p ≤ p0 → ∀ i x, core.decides p i x → B i x) := by
  constructor
  · intro h p hpp0 i x hx
    obtain ⟨q, hqp, y, hy⟩ := N.toClique.dense p i
    have heq : x = y := core.unique (core.persistent hqp hx) (href q i y hy)
    exact heq ▸ h q (hqp.trans hpp0) i y hy
  · intro h p hpp0 i x hx
    exact h p hpp0 i x (href p i x hx)

end Erdos1172Part3NiceCliqueNames
