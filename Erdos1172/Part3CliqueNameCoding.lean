/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceCliqueNames
public import Erdos1172.Part3StationarySquareDecisions

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

end Erdos1172Part3CliqueNameCoding
