/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaSequence
public import Erdos1172.Part4InternalSmallFiberBound

@[expose] public section

/-!
# Internal countability is preserved by set successor

An actual countable injection is composed with the internal numeral-shift
graph. Zero is outside its image, so adjoining a fresh domain element with
value zero yields another actual injection. The set-successor case uses
foundation to show that the set itself is a fresh element. No ordinal or
nonempty-set premise, nor a ground presentation of the countable set, is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableSuccessor

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaSequence ErdosInjectionExtension

def naturalShift : bSet 𝔹 :=
  sequenceGraph (fun n => of_nat (n + 1))

theorem naturalShift_is_injective {Γ : 𝔹} :
    Γ ≤ is_injective_function bSet.omega bSet.omega (naturalShift : bSet 𝔹) :=
  sequenceGraph_is_injective (fun _ => of_nat_mem_omega)
    (fun _ _ h => of_nat_mem_of_lt' (Nat.add_lt_add_right h 1))

private theorem bot_of_zero_shift_value {i : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ pair i (0 : bSet 𝔹) ∈ᴮ naturalShift) : Γ ≤ ⊥ := by
  have Hjoin := H.trans (mem_sequenceGraph
    (fun n => (of_nat (n + 1) : bSet 𝔹)) (pair i 0)).le
  apply Hjoin.trans
  apply iSup_le
  intro n
  have Heq : pair i (0 : bSet 𝔹) =ᴮ pair (of_nat n.down) (of_nat (n.down + 1)) ≤
      (of_nat 0 : bSet 𝔹) =ᴮ of_nat (n.down + 1) :=
    eq_of_eq_pair_right' le_rfl
  exact Heq.trans (of_nat_inj' (show 0 ≠ n.down + 1 by omega)).le

/-- Composing with the shift reserves the actual zero name as a new code,
including under conditions where the old domain is empty. -/
theorem zero_not_mem_shifted_image {A f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function A bSet.omega f) :
    Γ ≤ ((0 : bSet 𝔹) ∈ᴮ image A bSet.omega
      (injective_function_comp Hf (naturalShift_is_injective (Γ := Γ))))ᶜ := by
  rw [← imp_bot, ← deduction]
  have Hrange := (mem_image_iff.mp
    (show Γ ⊓ ((0 : bSet 𝔹) ∈ᴮ image A bSet.omega
      (injective_function_comp Hf (naturalShift_is_injective (Γ := Γ)))) ≤
      (0 : bSet 𝔹) ∈ᴮ image A bSet.omega
        (injective_function_comp Hf (naturalShift_is_injective (Γ := Γ))) from
      inf_le_right)).2
  obtain ⟨x, Hx⟩ := exists_convert Hrange
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hcomp := (mem_is_func'_comp_iff (is_func'_of_is_injective_function Hf)
    (is_func'_of_is_injective_function (naturalShift_is_injective (Γ := Γ)))).mp
      (Hx.trans inf_le_right)
  obtain ⟨i, Hi⟩ := exists_convert Hcomp.2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
  exact bot_of_zero_shift_value (Hi.trans (inf_le_right.trans inf_le_right))

/-- A fresh point may be added to any internally countable set. -/
theorem insert_countable_of_fresh {A a : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ injects_into A bSet.omega) (Ha : Γ ≤ (a ∈ᴮ A)ᶜ) :
    Γ ≤ injects_into (bSet.insert1 a A) bSet.omega := by
  obtain ⟨f, Hf⟩ := exists_convert (injection_into_of_injects_into HA)
    ErdosSmallFiberBound.B_ext_injective_code
  let g := injective_function_comp Hf (naturalShift_is_injective (Γ := Γ))
  have Hg : Γ ≤ is_injective_function A bSet.omega g :=
    injective_function_comp_is_injective_function
      (H₁ := Hf) (H₂ := naturalShift_is_injective (Γ := Γ))
  have Hfresh : Γ ≤ ((0 : bSet 𝔹) ∈ᴮ image A bSet.omega g)ᶜ :=
    zero_not_mem_shifted_image Hf
  exact injects_into_of_injection_into
    (le_iSup_of_le (bSet.insert1 (pair a (0 : bSet 𝔹)) g)
      (is_injective_function_insertPair Hg Ha
        (show Γ ≤ (of_nat 0 : bSet 𝔹) ∈ᴮ bSet.omega from of_nat_mem_omega) Hfresh))

/-- The successor of an arbitrary internally countable name is countable.
There is no ordinal or nonemptiness hypothesis. -/
theorem succ_countable {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ injects_into A bSet.omega) :
    Γ ≤ injects_into (succ A) bSet.omega := by
  apply insert_countable_of_fresh HA
  rw [← imp_bot, ← deduction]
  exact bot_of_mem_self' inf_le_right

end bSet.ErdosCountableSuccessor
