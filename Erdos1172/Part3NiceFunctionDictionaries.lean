/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceFunctionNames

@[expose] public section

/-!
# Exact dictionaries for small function names

For a small decision order with a weakest condition, the nice function
names have cardinality exactly alephTwo under GCH. In particular the
dictionary is a bijection: two side-condition codes denote the same name
only when the codes agree. The order used by the names is the actual
specified preorder, not a ground-function substitute.
-/

open Cardinal Ordinal Set Function

namespace Erdos1172Part3NiceFunctionDictionaries

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3NiceFunctionNames
open Erdos1172Part3StationaryDecisions (Compatible)

variable {P I V : Type} [Preorder P]

def groundName (one : P) (hOne : ∀ p : P, p ≤ one) (f : I → V) :
    NiceFunctionName P I V where
  graph i := {(one, f i)}
  small i := by
    simp only [Cardinal.mk_singleton]
    exact Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1)
  consistent := by
    intro i p v q w hp hq _
    exact (congrArg Prod.snd (Set.mem_singleton_iff.mp hp)).trans
      (congrArg Prod.snd (Set.mem_singleton_iff.mp hq)).symm
  predense p i := ⟨one, f i, Set.mem_singleton _, p, le_rfl, hOne p⟩

theorem groundName_injective (one : P) (hOne : ∀ p : P, p ≤ one) :
    Injective (groundName (I := I) (V := V) one hOne) := by
  intro f g h
  funext i
  have heq := congrArg (fun N : NiceFunctionName P I V => N.graph i) h
  have hm : (one, f i) ∈ (groundName one hOne g).graph i :=
    heq ▸ Set.mem_singleton _
  exact congrArg Prod.snd (Set.mem_singleton_iff.mp hm)

theorem mk_nice_function_name_eq (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (one : P) (hOne : ∀ p : P, p ≤ one) : #(NiceFunctionName P W1 W1) = ℵ_ 2 := by
  apply le_antisymm (mk_nice_function_name_le hGCH hP)
  have h := Cardinal.mk_le_of_injective (groundName_injective (I := W1) (V := W1) one hOne)
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id, W1, Cardinal.mk_toType,
    Ordinal.card_omega, Cardinal.power_self_eq (Cardinal.aleph0_le_aleph 1),
    hGCH.two_power_aleph_one] using h

noncomputable def dictionary (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (one : P) (hOne : ∀ p : P, p ≤ one) : W2 ≃ NiceFunctionName P W1 W1 :=
  Classical.choice (Cardinal.eq.mp (by
    rw [mk_nice_function_name_eq hGCH hP one hOne]
    simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]))

end Erdos1172Part3NiceFunctionDictionaries
