/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrderMatrix
public import Erdos1172.Part4ShioyaInternalCarrier
public import Erdos1172.Part4LevyAnonymousSmallAuxiliary

@[expose] public section

/-! # Absolute order and word predicates for internal ordinal presentations -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosNameTransport
variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def Fields.map (e : CompleteLatticeHom B C) (s : Fields B) : Fields C :=
  ⟨mapNames e s.carrier,mapNames e s.order,mapNames e s.point,mapNames e s.length,mapNames e s.bits⟩

theorem ordinalCarrier_cases {Γ b : B} {x : bSet B} {o : Ordinal.{u}} (hx : Γ ≤ x ∈ᴮ ordinalCarrier o)
    (branch : ∀ (i : o.ToType) (Δ : B), Δ ≤ Γ → Δ ≤ x =ᴮ ordinalLabel i → Δ ≤ b) : Γ ≤ b := by
  have decomp : (x ∈ᴮ ordinalCarrier o) = ⨆ i : o.ToType, x =ᴮ ordinalLabel i := by
    unfold ordinalCarrier
    rw [PSet.ordinalMk_eq_def o,check_unfold,mem_unfold]
    exact iSup_congr fun _ => top_inf_eq _
  apply ((inf_eq_left.mpr hx).symm.le.trans_eq (congrArg (Γ ⊓ ·) decomp)).trans
  rw [inf_iSup_eq]
  exact iSup_le fun i => branch i _ inf_le_left inf_le_right

end bSet.ErdosShioyaInternal
