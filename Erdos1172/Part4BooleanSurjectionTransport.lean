/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanFunctionTransport
public import Erdos1172.Part4InternalCHHartogs

@[expose] public section

/-!
# Bounded surjectivity and forward cardinal transport

Surjectivity is normalized to the original domain and codomain child
indices, so its exact Boolean value is preserved by a complete homomorphism.
Weak partial-surjection graphs are first restricted to their product before
transporting functionality. This yields only forward preservation of the
unbounded existential comparison `larger_than`.

Injection transport uses the proved ordinal least-preimage construction.
Its target-ordinal hypothesis is explicitly in the target algebra; no
unbounded elementarity, ordinal transport, or nonemptiness is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNameTransport

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B]
variable [NontrivialCompleteBooleanAlgebra C]

/-- Both quantifiers in surjectivity are genuinely bounded, including when
either bounding name is empty or has mixed membership coefficients. -/
theorem is_surj_eq_bounded (X Y f : bSet B) :
    is_surj X Y f =
      ⨅ i : Y.type, _root_.imp (Y.bval i)
        (⨆ j : X.type, X.bval j ⊓ pair (X.func j) (Y.func i) ∈ᴮ f) := by
  unfold is_surj
  rw [show (⨅ v : bSet B, _root_.imp (v ∈ᴮ Y)
        (⨆ w : bSet B, w ∈ᴮ X ⊓ pair w v ∈ᴮ f)) =
      (⨅ i : Y.type, _root_.imp (Y.bval i)
        (⨆ w : bSet B, w ∈ᴮ X ⊓ pair w (Y.func i) ∈ᴮ f)) from
    (@bounded_forall B _ Y
      (fun v => ⨆ w : bSet B, w ∈ᴮ X ⊓ pair w v ∈ᴮ f)
      (h_congr := B_ext_iSup
        (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right))).symm]
  congr 1
  ext i
  congr 1
  exact (@bounded_exists B _ X (fun w => pair w (Y.func i) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)).symm

/-- Exact bounded transport does not require graph support or functionality. -/
theorem map_is_surj (e : CompleteLatticeHom B C) (X Y f : bSet B) :
    e (is_surj X Y f) =
      is_surj (mapNames e X) (mapNames e Y) (mapNames e f) := by
  cases X with
  | mk ι X w =>
    cases Y with
    | mk κ Y v =>
      simp only [is_surj_eq_bounded, mapNames_mk, bSet.type, bSet.func,
        bSet.bval, map_iInf, map_iSup, map_imp, map_inf, map_mem, map_pair]

theorem map_is_surj_of (e : CompleteLatticeHom B C)
    {X Y f : bSet B} {Γ : B} (Hsurj : Γ ≤ is_surj X Y f) :
    e Γ ≤ is_surj (mapNames e X) (mapNames e Y) (mapNames e f) := by
  rw [← map_is_surj]
  exact OrderHomClass.mono e Hsurj

/-- Normalize the weak graph before mapping it. The witness may differ
from the original graph, but its partial-surjection domain is unchanged. -/
theorem map_larger_than_of_partial_surjection (e : CompleteLatticeHom B C)
    {X Y S f : bSet B} {Γ : B}
    (Hsub : Γ ≤ S ⊆ᴮ X)
    (Hfunc : Γ ≤ is_func' S Y f)
    (Hsurj : Γ ≤ is_surj S Y f) :
    e Γ ≤ larger_than (mapNames e X) (mapNames e Y) := by
  let g := function_of_func' Hfunc
  have Hg : Γ ≤ is_function S Y g := function_of_func'_is_function Hfunc
  have Hgsurj : Γ ≤ is_surj S Y g :=
    function_of_func'_surj_of_surj Hfunc Hsurj
  unfold larger_than
  apply le_iSup_of_le (mapNames e S)
  apply le_iSup_of_le (mapNames e g)
  refine le_inf (le_inf ?_ ?_) (map_is_surj_of e Hgsurj)
  · rw [← map_subset]
    exact OrderHomClass.mono e Hsub
  · exact is_func'_of_is_function (map_is_function_of e Hg)

/-- Only the forward inequality is claimed: the target algebra may have
partial-surjection names not arising by hereditary transport. -/
theorem map_larger_than (e : CompleteLatticeHom B C) (X Y : bSet B) :
    e (larger_than X Y) ≤ larger_than (mapNames e X) (mapNames e Y) := by
  change e (⨆ S : bSet B, ⨆ f : bSet B,
      (S ⊆ᴮ X ⊓ is_func' S Y f) ⊓ is_surj S Y f) ≤ _
  rw [map_iSup]
  apply iSup_le
  intro S
  rw [map_iSup]
  apply iSup_le
  intro f
  exact map_larger_than_of_partial_surjection e
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right

theorem map_larger_than_of (e : CompleteLatticeHom B C)
    {X Y : bSet B} {Γ : B} (Hlarge : Γ ≤ larger_than X Y) :
    e Γ ≤ larger_than (mapNames e X) (mapNames e Y) :=
  (OrderHomClass.mono e Hlarge).trans (map_larger_than e X Y)

/-- A transported ordinal target turns the transported reverse partial
surjection into an injection, including the empty-domain case. -/
theorem map_injects_into_of_ordinal (e : CompleteLatticeHom B C)
    {X Y : bSet B} {Γ : B}
    (Hinj : Γ ≤ injects_into X Y)
    (HOrd : e Γ ≤ Ord (mapNames e Y)) :
    e Γ ≤ injects_into (mapNames e X) (mapNames e Y) :=
  ErdosCHHartogs.injects_into_of_larger_than_ordinal HOrd
    (map_larger_than_of e (ErdosCHHartogs.larger_than_of_injects_into Hinj))

end bSet.ErdosNameTransport
