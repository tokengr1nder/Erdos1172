/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapsePath
public import Erdos1172.Part4InternalImageRecursionInvariant

@[expose] public section

/-! # The named graph of the native collapse path projection -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosBoundedImageRecursion ErdosRelationGraph ErdosPartialInjection
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def finalTest (P R l h p : N) : B := (p ∈ᴮ P) ⊓ allIn P (fun x =>
  let kept := survives (image l (bv_powerset P) h) x
  (kept ⟹ edge R x p) ⊓ (edge R x p ⟹ kept))

def branch (K P R f p l h : N) : B := (l ∈ᴮ K) ⊓ (is_function l P f ⊓
  (is_function l (bv_powerset P) h ⊓ (trace P R f h ⊓ finalTest P R l h p)))

def value (K P R f p : N) : B := ⨆ l : N, ⨆ h : N, branch K P R f p l h

end bSet.ErdosShioyaInternal.CollapsePath
