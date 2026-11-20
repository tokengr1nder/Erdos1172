/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousCheckedSequenceReading

@[expose] public section

/-! # Reading countable subsets through the anonymous collapse

A supported enumeration of a nonempty countable subset has a reading through
the anonymous algebra. Bounded images commute with the complete inclusion,
so its range gives an anonymous name for the original subset on each piece.
-/

set_option autoImplicit false

noncomputable section
open scoped Flypitch
open Lattice
universe u

namespace bSet.ErdosNameTransport

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

private theorem image_mk_bounded {I J : Type u} (x : I → bSet B)
    (b : I → B) (y : J → bSet B) (c : J → B) (f : bSet B) :
    image (.mk I x b) (.mk J y c) f =
      .mk J y (fun j => (⨆ i, b i ⊓ (pair (x i) (y j) ∈ᴮ f)) ⊓ c j) := by
  unfold image subset.mk set_of_indicator
  congr 1
  funext j
  exact congrArg (· ⊓ c j)
    (@bounded_exists B _ (.mk I x b) (fun z => pair z (y j) ∈ᴮ f)
      (h_congr := B_ext_pair_mem_left)).symm

theorem map_bounded_image (e : CompleteLatticeHom B C) (x y f : bSet B) :
    mapNames e (image x y f) = image (mapNames e x) (mapNames e y) (mapNames e f) := by
  cases x
  cases y
  simp only [image_mk_bounded, mapNames_mk, map_iSup, map_inf, map_mem, map_pair]

end bSet.ErdosNameTransport
