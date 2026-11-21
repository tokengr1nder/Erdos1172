/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ProductTraceExtraction

@[expose] public section

/-!
# Trace-preserving extraction at every finite power

Index n has order type omegaOne^(n+1). The recursively constructed trace
scheme has countable-union and exact restriction laws at every finite
depth, and every positive trace has a full trace-preserving subsequence.
Prefix n indexes all proper prefixes, including the empty prefix.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FiniteTraceSchemes

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3TraceScheme (TraceScheme Extracts)

@[reducible] def Index : ℕ → Type
  | 0 => W1
  | n + 1 => W1 ×ₗ Index n

@[instance_reducible]
noncomputable def indexLinearOrder (n : ℕ) : LinearOrder (Index n) :=
  Nat.rec (motive := fun k => LinearOrder (Index k)) (inferInstanceAs (LinearOrder W1))
    (fun k ih => @Prod.Lex.instLinearOrder W1 (Index k) inferInstance ih) n

attribute [instance] indexLinearOrder

theorem indexWellFoundedLT (n : ℕ) : WellFoundedLT (Index n) :=
  Nat.rec (motive := fun k => WellFoundedLT (Index k)) (inferInstanceAs (WellFoundedLT W1))
    (fun k ih => letI := ih; inferInstanceAs (WellFoundedLT (W1 ×ₗ Index k))) n

attribute [instance] indexWellFoundedLT

theorem mk_index_le (n : ℕ) : #(Index n) ≤ ℵ_ 1 := by
  induction n with
  | zero => exact le_of_eq (by simp only [Index, W1, Cardinal.mk_toType, Ordinal.card_omega])
  | succ n ih => exact Erdos1172Part3RankedCoreBlockAssembly.mk_product_le ih

theorem typeLT_index (n : ℕ) : typeLT (Index n) = (ω_ 1 : Ordinal.{0}) ^ (↑(n + 1) : Ordinal) := by
  induction n with
  | zero =>
    simp only [Index, indexLinearOrder, Nat.rec_zero, Nat.zero_add, Nat.cast_one, Ordinal.opow_one]
    exact Ordinal.type_toType _
  | succ n ih =>
    change Ordinal.type (Prod.Lex ((· < ·) : W1 → W1 → Prop)
      ((· < ·) : Index n → Index n → Prop)) = _
    rw [Ordinal.type_prod_lex]
    change (typeLT (Index n)) * (typeLT W1) = _
    rw [ih]
    change (ω_ 1 : Ordinal.{0}) ^ (↑(n + 1) : Ordinal) * (typeLT (ω_ 1).ToType) = _
    rw [Ordinal.type_toType, show (↑(n + 1 + 1) : Ordinal.{0}) = (↑(n + 1) : Ordinal) + 1 by simp]
    rw [Ordinal.opow_add_one]

noncomputable def scheme (G : SimpleGraph W2) : (n : ℕ) → TraceScheme (Index n) G
  | 0 => Erdos1172Part3TraceScheme.line G
  | n + 1 => (scheme G n).product

theorem scheme_extracts (G : SimpleGraph W2) (n : ℕ) : Extracts (scheme G n) := by
  induction n with
  | zero => exact Erdos1172Part3TraceScheme.line_extracts G
  | succ n ih => exact Erdos1172Part3ProductTraceExtraction.extracts_product (scheme G n) ih (mk_index_le n)

@[reducible] def Prefix : ℕ → Type
  | 0 => Unit
  | n + 1 => Unit ⊕ (W1 × Prefix n)

def root : (n : ℕ) → Prefix n
  | 0 => ()
  | _ + 1 => Sum.inl ()

theorem mk_prefix_le (n : ℕ) : #(Prefix n) ≤ ℵ_ 1 := by
  induction n with
  | zero => simpa only [Prefix, Cardinal.mk_unit] using
      (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1))
  | succ n ih =>
    change #(Unit ⊕ (W1 × Prefix n)) ≤ ℵ_ 1
    rw [Cardinal.mk_sum, Cardinal.mk_prod]
    simp only [Cardinal.lift_id, Cardinal.mk_unit, W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.add_le_of_le (Cardinal.aleph0_le_aleph 1)
      (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1))
      ((mul_le_mul' le_rfl ih).trans (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)).le)

end Erdos1172Part3FiniteTraceSchemes
