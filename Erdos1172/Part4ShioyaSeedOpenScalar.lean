/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrder
public import Erdos1172.Part4BooleanNameTransport

@[expose] public section

/-! # Signed target tests under scalar extension, including the small auxiliary -/

set_option autoImplicit false
noncomputable section
universe u
open Lattice bSet bSet.ErdosNameTransport
open scoped Flypitch
namespace bSet.ErdosShioyaInternal
variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (e : CompleteLatticeHom B C)

theorem map_named_allIn (T : bSet B) (f : bSet B → B) (g : bSet C → C)
    (hf : B_ext f) (hg : B_ext g) (h : ∀ x, e (f x) = g (mapNames e x)) :
    e (allIn T f) = allIn (mapNames e T) g := by
  cases T with
  | mk J F w =>
    unfold allIn
    rw [← bounded_forall (h_congr := hf),← bounded_forall (h_congr := hg)]
    change e (⨅ i : J, w i ⟹ f (F i)) = ⨅ i : J, e (w i) ⟹ g (mapNames e (F i))
    simp only [_root_.map_iInf,map_imp,h]

theorem map_named_someIn (T : bSet B) (f : bSet B → B) (g : bSet C → C)
    (hf : B_ext f) (hg : B_ext g) (h : ∀ x, e (f x) = g (mapNames e x)) :
    e (someIn T f) = someIn (mapNames e T) g := by
  cases T with
  | mk J F w =>
    unfold someIn
    rw [← bounded_exists (h_congr := hf),← bounded_exists (h_congr := hg)]
    change e (⨆ i : J, w i ⊓ f (F i)) = ⨆ i : J, e (w i) ⊓ g (mapNames e (F i))
    simp only [_root_.map_iSup,InfHomClass.map_inf,h]

end bSet.ErdosShioyaInternal
