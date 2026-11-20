/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteStemSelection

@[expose] public section

/-!
# One domination function for every finite cutoff tree

The nonempty prefixes are coded by omegaOne. A bounded set of codes
meets only boundedly many outer rows, independently of the inner prefix.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FiniteCutoffCoding

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Prefix root mk_prefix_le)
open Erdos1172Part3FiniteTraceCutoffs (reindexBounds)
open Erdos1172Part3FunctionDecisions (FunctionDecisions BoundedAt)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

theorem mk_row_prefix (n : ℕ) : #(W1 × Prefix n) = #W1 := by
  apply le_antisymm
  · rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact (mul_le_mul' le_rfl (mk_prefix_le n)).trans_eq
      (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))
  · exact (Cardinal.le_def _ _).mpr ⟨⟨fun i => (i, root n), fun _ _ h => congrArg Prod.fst h⟩⟩

noncomputable def prefixCode (n : ℕ) : (W1 × Prefix n) ≃ W1 :=
  Classical.choice (Cardinal.eq.mp (mk_row_prefix n))

theorem exists_late_rows_above_code_bound (n : ℕ) (bound : W1) :
    ∃ rowBound : W1, ∀ i : W1, rowBound < i → ∀ e : Prefix n, bound < prefixCode n (i, e) := by
  have hcount : (Set.Iic bound).Countable := Cardinal.le_aleph0_iff_set_countable.mp
    (Cardinal.lt_aleph_one_iff.mp (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt bound))
  obtain ⟨rowBound, hrow⟩ := exists_bound_of_countable
    ((fun k : W1 => ((prefixCode n).symm k).1) '' Set.Iic bound) (hcount.image _)
  refine ⟨rowBound, ?_⟩
  intro i hi e
  by_contra h
  have hmem : i ∈ (fun k : W1 => ((prefixCode n).symm k).1) '' Set.Iic bound :=
    ⟨prefixCode n (i, e), le_of_not_gt h,
      congrArg Prod.fst ((prefixCode n).symm_apply_apply (i, e))⟩
  exact (hrow i hmem).asymm hi

variable {P : Type} [Preorder P]

noncomputable def encodedBounds (n : ℕ) (B : FunctionDecisions P (Prefix (n + 1)) W1) :
    FunctionDecisions P W1 W1 := reindexBounds B (fun k => Sum.inr ((prefixCode n).symm k))

theorem encodedBounds_bound (n : ℕ) {B : FunctionDecisions P (Prefix (n + 1)) W1}
    {p : P} {i : W1} {e : Prefix n} {v : W1}
    (h : BoundedAt (encodedBounds n B) p (prefixCode n (i, e)) v) :
    ∀ q : P, q ≤ p → ∀ w : W1, B.decides q (Sum.inr (i, e)) w → w < v := by
  intro q hqp w hw
  apply h q hqp w
  change B.decides q (Sum.inr ((prefixCode n).symm (prefixCode n (i, e)))) w
  simpa only [Equiv.symm_apply_apply] using hw

end Erdos1172Part3FiniteCutoffCoding
