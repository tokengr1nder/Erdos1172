/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceFunctionNames

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

end Erdos1172Part3NiceCliqueNames
