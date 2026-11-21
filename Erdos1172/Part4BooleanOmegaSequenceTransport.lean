/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaSequence
public import Erdos1172.Part4InternalBoundedFunctionValue
public import Erdos1172.Part4BooleanFunctionTransport

@[expose] public section

/-!
# Supported omega graphs and hereditary name transport

Numeral values determine the entire supported internal graph, including
mixed natural arguments. Graph support is essential: functionality alone
would not exclude unrelated entries. All equalities preserve the original
Boolean context; no global equality of chosen values is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaSequence

open ErdosNameTransport ErdosBoundedFunctionValue

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B]
variable [NontrivialCompleteBooleanAlgebra C]

theorem sequenceGraph_subset_of_pairs {v : ℕ → bSet B} {f : bSet B} {Γ : B}
    (Hpairs : ∀ n, Γ ≤ pair (of_nat n) (v n) ∈ᴮ f) :
    Γ ≤ sequenceGraph v ⊆ᴮ f := by
  rw [subset_unfold]
  apply le_iInf
  intro n
  change Γ ≤ (⊤ : B) ⟹ pair (of_nat n.down) (v n.down) ∈ᴮ f
  rw [top_imp]
  exact Hpairs n.down

/-- Supported graph equality follows from its actual numeral pairs. -/
theorem eq_sequenceGraph_of_pairs {v : ℕ → bSet B} {S f : bSet B} {Γ : B}
    (Hf : Γ ≤ is_function omega S f)
    (Hpairs : ∀ n, Γ ≤ pair (of_nat n) (v n) ∈ᴮ f) :
    Γ ≤ f =ᴮ sequenceGraph v := by
  apply (le_inf ?_ (sequenceGraph_subset_of_pairs Hpairs)).trans
    (eq_of_subset_subset f (sequenceGraph v))
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  have Hzprod : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ prod omega S :=
    mem_of_mem_subset (inf_le_left.trans (subset_prod_of_is_function Hf)) inf_le_right
  apply (le_inf le_rfl Hzprod).trans
  rw [mem_unfold (u := z) (v := prod omega S), inf_iSup_eq]
  apply iSup_le
  intro i
  let Δ := (Γ ⊓ z ∈ᴮ f) ⊓
    (((omega : bSet B).bval i.1 ⊓ S.bval i.2) ⊓ z =ᴮ pair ((omega : bSet B).func i.1) (S.func i.2))
  change Δ ≤ z ∈ᴮ sequenceGraph v
  have HΓ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hz : Δ ≤ z =ᴮ pair (of_nat i.1.down) (S.func i.2) := inf_le_right.trans inf_le_right
  have Hpair : Δ ≤ pair (of_nat i.1.down) (S.func i.2) ∈ᴮ f :=
    mem_congr Hz bv_refl (inf_le_left.trans inf_le_right)
  have Hvalue : Δ ≤ S.func i.2 =ᴮ v i.1.down :=
    eq_of_is_function_of_eq (HΓ.trans Hf) bv_refl Hpair (HΓ.trans (Hpairs _))
  exact mem_congr (bv_symm (bv_trans Hz (pair_congr bv_refl Hvalue))) bv_refl sequenceGraph_pair

theorem eq_sequenceGraph_graphValue {S f : bSet B} {Γ : B}
    (Hf : Γ ≤ is_function omega S f) :
    Γ ≤ f =ᴮ sequenceGraph (fun n => graphValue S f (of_nat n)) :=
  eq_sequenceGraph_of_pairs Hf (fun _ => graphValue_pair_mem Hf of_nat_mem_omega)

/-- Hereditary transport of the actual graph, not unbounded elementarity. -/
theorem map_sequenceGraph (e : CompleteLatticeHom B C) (v : ℕ → bSet B) :
    mapNames e (sequenceGraph v) = sequenceGraph (fun n => mapNames e (v n)) := by
  change mapNames e (.mk (ULift.{u} ℕ)
    (fun n => pair (of_nat n.down) (v n.down)) (fun _ => ⊤)) =
      .mk (ULift.{u} ℕ) (fun n => pair (of_nat n.down) (mapNames e (v n.down))) (fun _ => ⊤)
  simp only [mapNames_mk, map_pair, of_nat, map_check, map_top]

theorem sequenceGraph_congr {v w : ℕ → bSet B} {Γ : B}
    (H : ∀ n, Γ ≤ v n =ᴮ w n) :
    Γ ≤ sequenceGraph v =ᴮ sequenceGraph w := by
  apply (le_inf ?_ ?_).trans (eq_of_subset_subset _ _)
  · apply sequenceGraph_subset_of_pairs
    intro n
    exact mem_congr (pair_congr bv_refl (bv_symm (H n))) bv_refl sequenceGraph_pair
  · apply sequenceGraph_subset_of_pairs
    intro n
    exact mem_congr (pair_congr bv_refl (H n)) bv_refl sequenceGraph_pair

end bSet.ErdosOmegaSequence
