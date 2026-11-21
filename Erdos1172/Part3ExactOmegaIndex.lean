/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaSuccessorCore

@[expose] public section

/-!
# Exact omega indices and genuinely smaller bounded pieces

The existing lower bounds are equalities. An explicit interval embedding
places the n-th finite level between omegaOne^n and omegaOne^(n+1).
Bounded level prefixes and bounded outer rows have strictly smaller order
types. These bounds support order-type smallness, not merely weak traces.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ExactOmegaIndex

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex omega_power_le_type)
open Erdos1172Part3OmegaSuccessorCore (OmegaSuccessor)

noncomputable def levelValue (n : ℕ) (i : Index n) : Ordinal :=
  (ω_ 1) ^ (n : Ordinal) + Ordinal.typein ((· < ·) : Index n → Index n → Prop) i

theorem levelValue_lt (n : ℕ) (i : Index n) :
    levelValue n i < (ω_ 1) ^ ((n + 1 : ℕ) : Ordinal) := by
  apply Ordinal.isPrincipal_add_opow_of_isPrincipal_add (Ordinal.isPrincipal_add_omega 1)
  · apply (Ordinal.opow_lt_opow_iff_right
      (Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1))).mpr
    exact_mod_cast Nat.lt_succ_self n
  · exact (Ordinal.typein_lt_type _ i).trans_eq (typeLT_index n)

theorem levelValue_lt_omega_power (n : ℕ) (i : Index n) :
    levelValue n i < (ω_ 1) ^ ω :=
  (levelValue_lt n i).trans ((Ordinal.opow_lt_opow_iff_right
    (Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1))).mpr (Ordinal.natCast_lt_omega0 (n + 1)))

noncomputable def value (z : OmegaIndex) : Ordinal := levelValue (ofLex z).1 (ofLex z).2

theorem value_strict : StrictMono value := by
  intro x y hxy
  cases hxy with
  | left i j hnm =>
    apply (levelValue_lt _ i).trans_le
    apply (Ordinal.opow_le_opow_right (Ordinal.omega_pos 1)
      (show (( _ + 1 : ℕ) : Ordinal) ≤ (_ : ℕ) by exact_mod_cast Nat.succ_le_of_lt hnm)).trans
    exact le_self_add
  | right i j hij =>
    exact (add_lt_add_iff_left _).mpr ((Ordinal.typein_lt_typein _).mpr hij)

noncomputable def omegaEmbedding : OmegaIndex ↪o ((ω_ 1 : Ordinal.{0}) ^ ω).ToType :=
  OrderEmbedding.ofStrictMono
    (fun z => Ordinal.ToType.mk ⟨value z, levelValue_lt_omega_power (ofLex z).1 (ofLex z).2⟩)
    (fun _ _ h => Ordinal.ToType.mk.strictMono (value_strict h))

theorem typeLT_omegaIndex : typeLT OmegaIndex = (ω_ 1 : Ordinal.{0}) ^ ω := by
  apply le_antisymm _ omega_power_le_type
  have h := (RelEmbedding.ofMonotone omegaEmbedding omegaEmbedding.strictMono).ordinal_type_le
  simpa only [Ordinal.type_toType] using h

theorem typeLT_omegaSuccessor : typeLT OmegaSuccessor = (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
  change Ordinal.type (Prod.Lex ((· < ·) : W1 → W1 → Prop)
    ((· < ·) : OmegaIndex → OmegaIndex → Prop)) = _
  rw [Ordinal.type_prod_lex]
  change (typeLT OmegaIndex) * (typeLT W1) = _
  rw [typeLT_omegaIndex, Ordinal.type_toType, Ordinal.opow_add_one]

def boundedRows (bound : W1) : Set OmegaSuccessor := {z | (ofLex z).1 ≤ bound}

theorem boundedRows_type_lt (bound : W1) :
    typeLT (boundedRows bound) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
  let f : boundedRows bound → Set.Iic bound ×ₗ OmegaIndex :=
    fun z => toLex (⟨(ofLex z.val).1, z.property⟩, (ofLex z.val).2)
  have hf : StrictMono f := by
    intro x y hxy
    change x.val < y.val at hxy
    dsimp only [f]
    rw [Prod.Lex.lt_iff] at hxy ⊢
    rcases hxy with hfirst | ⟨heq, hsecond⟩
    · exact Or.inl hfirst
    · exact Or.inr ⟨Subtype.ext heq, hsecond⟩
  have htype := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  change typeLT (boundedRows bound) ≤ Ordinal.type
    (Prod.Lex ((· < ·) : Set.Iic bound → Set.Iic bound → Prop)
      ((· < ·) : OmegaIndex → OmegaIndex → Prop)) at htype
  rw [Ordinal.type_prod_lex] at htype
  change typeLT (boundedRows bound) ≤ (typeLT OmegaIndex) * (typeLT (Set.Iic bound)) at htype
  rw [typeLT_omegaIndex] at htype
  have hbound : typeLT (Set.Iic bound) < ω_ 1 := by
    rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_type]
    exact Erdos1172Part3ConvergentCore.mk_Iic_W1_lt bound
  rw [Ordinal.opow_add_one]
  exact htype.trans_lt (mul_lt_mul_of_pos_left hbound (Ordinal.opow_pos _ (Ordinal.omega_pos 1)))

end Erdos1172Part3ExactOmegaIndex
