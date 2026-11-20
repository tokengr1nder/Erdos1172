/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceCliqueNames
public import Erdos1172.Part3SquareLossBounds
public import Erdos1172.Part3CoreObjectCode

@[expose] public section

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CliqueNameCoding

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3NiceFunctionNames (NiceFunctionName)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3HechlerOrder (Condition)

variable {P I V : Type} [Preorder P]

/-- The small-name count also permits omegaTwo-valued decisions; it
does not count arbitrary predicates on all conditions. -/
theorem mk_nice_function_name_le (hGCH : GCH)
    (hP : #P ≤ ℵ_ 2) (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 2) :
    #(NiceFunctionName P I V) ≤ ℵ_ 2 := by
  let Code := {s : Set (P × V) // #s ≤ ℵ_ 1}
  have hprod : #(P × V) ≤ ℵ_ 2 := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id]
    exact (mul_le_mul' hP hV).trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))
  have hcode : #Code ≤ ℵ_ 2 := by
    apply (Cardinal.mk_bounded_set_le (P × V) (ℵ_ 1)).trans
    exact (Cardinal.power_le_power_right (max_le hprod (Cardinal.aleph0_le_aleph 2))).trans_eq
      hGCH.aleph_two_power_aleph_one
  let encode (N : NiceFunctionName P I V) : I → Code := fun i => ⟨N.graph i, N.small i⟩
  have hinj : Injective encode := by
    intro N M h
    apply Erdos1172Part3NiceFunctionNames.NiceFunctionName.ext
    funext i
    exact congrArg (fun code : I → Code => (code i).val) h
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id]
  exact (Cardinal.power_le_power_right hcode).trans
    ((Cardinal.power_le_power_left (Cardinal.aleph_pos 2).ne' hI).trans_eq
      hGCH.aleph_two_power_aleph_one)

theorem mk_nice_clique_name_le [LinearOrder I] [LinearOrder V]
    (hGCH : GCH) (hP : #P ≤ ℵ_ 2) (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 2)
    (G : SimpleGraph V) : #(NiceCliqueName P I V G) ≤ ℵ_ 2 := by
  have hinj : Injective (NiceCliqueName.function : NiceCliqueName P I V G →
      NiceFunctionName P I V) := fun _ _ h => NiceCliqueName.ext h
  exact (Cardinal.mk_le_of_injective hinj).trans (mk_nice_function_name_le hGCH hP hI hV)

theorem mk_square_le : #Square ≤ ℵ_ 1 := by
  change #(W1 × W1) ≤ ℵ_ 1
  simp only [Cardinal.mk_prod, Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
  rw [Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)]

abbrev SquareName (G : SimpleGraph W2) := NiceCliqueName Condition Square W2 G

noncomputable def conditionRank (hGCH : GCH) : Condition ↪ W2 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      Erdos1172Part3HechlerCentering.mk_Condition_le hGCH))

noncomputable def squareNameRank (hGCH : GCH) (G : SimpleGraph W2) : SquareName G ↪ W2 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      mk_nice_clique_name_le hGCH (Erdos1172Part3HechlerCentering.mk_Condition_le hGCH)
        mk_square_le (by simp only [W2, Cardinal.mk_toType, Ordinal.card_omega, le_refl]) G))

def squareValues {G : SimpleGraph W2} (N : SquareName G) : Erdos1172Part3CoreObjectCode.Obj :=
  ⟨N.values, N.mk_values_le mk_square_le⟩

theorem exists_square_value_bound {G : SimpleGraph W2} (N : SquareName G) :
    ∃ b : W2, ∀ x ∈ N.values, x < b :=
  Erdos1172Part3CoreObjectCode.exists_objectBound (squareValues N)

end Erdos1172Part3CliqueNameCoding
