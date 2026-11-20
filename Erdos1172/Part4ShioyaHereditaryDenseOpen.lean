/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrder
public import Erdos1172.Part4BooleanUltrapowerNormality

@[expose] public section

/-! # Bounded universal tests and dense subsets in a hereditary Boolean ultrapower -/

set_option autoImplicit false
noncomputable section
universe u
open Filter bSet bSet.ErdosShioyaInternal Lattice
open scoped Flypitch
namespace Erdos1172BooleanUltrapower
variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)
variable [CountableInterFilter (U : Filter I)]
local notation "V" => Algebra U B

theorem hereditary_allIn (F : I → bSet B) (P : I → bSet B → B) (Q : bSet V → V)
    (pExt : ∀ i, B_ext (P i)) (qExt : B_ext Q)
    (commutes : ∀ X : I → bSet B, value U (fun i => P i (X i)) = Q (hereditary U X)) :
    value U (fun i => allIn (F i) (P i)) = allIn (hereditary U F) Q := by
  have source (i : I) : allIn (F i) (P i) = ⨅ k : (F i).type, (F i).bval k ⟹ P i ((F i).func k) :=
    (bounded_forall (h_congr := pExt i)).symm
  have target : allIn (hereditary U F) Q =
      ⨅ a : Children U F, value U (weight U F a) ⟹ Q (hereditary U (child U F a)) := by
    apply (bounded_forall (v := hereditary U F) (h_congr := qExt)).symm.trans
    conv_lhs => rw [show hereditary U F = _ from liftName_eq U _ F]
    rfl
  rw [target]
  calc
    _ = _ := congrArg (value U) (_root_.funext source)
    _ = _ := value_bounded_forall U F P
    _ = _ := iInf_congr fun a => congrArg (value U (weight U F a) ⟹ ·) (commutes (child U F a))

theorem hereditary_edge_value (R X Y : I → bSet B) :
    value U (fun i => edge (R i) (X i) (Y i)) = edge (hereditary U R) (hereditary U X) (hereditary U Y) := by
  unfold edge
  rw [value_name_mem]
  exact (bv_rw (top_unique (hereditary_pair U X Y)) (fun z => z ∈ᴮ hereditary U R) (h_congr := B_ext_mem_left)).symm

end Erdos1172BooleanUltrapower
