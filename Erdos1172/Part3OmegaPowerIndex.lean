/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FullStationaryFiniteCores
public import Mathlib.Data.Sigma.Order

@[expose] public section

/-!
# A countable ordered sum of growing finite powers

The index is small enough for ground clique extraction and contains a
copy of every finite-power index. Its order type therefore dominates
omegaOne^omega. Exact target extraction uses this proved lower bound.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OmegaPowerIndex

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index mk_index_le typeLT_index)

abbrev OmegaIndex := Σₗ n : ℕ, Index n

instance omegaIndexWellFoundedLT : WellFoundedLT OmegaIndex := by
  have hac : ∀ n (i : Index n), Acc (Sigma.Lex ((· < ·) : ℕ → ℕ → Prop)
      (fun k => ((· < ·) : Index k → Index k → Prop))) ⟨n, i⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i
      induction i using WellFoundedLT.induction with
      | ind i hi =>
        refine Acc.intro _ ?_
        intro z hz
        cases hz with
        | left j _ hjn => exact ih _ hjn j
        | right j _ hji => exact hi j hji
  refine Subrelation.wf (r := InvImage (Sigma.Lex ((· < ·) : ℕ → ℕ → Prop)
      (fun k => ((· < ·) : Index k → Index k → Prop))) ofLex) (fun h => h) ?_
  exact InvImage.wf ofLex (WellFounded.intro fun z : Σ n : ℕ, Index n => hac z.1 z.2)

theorem mk_omegaIndex_le : #OmegaIndex ≤ ℵ_ 1 := by
  change #(Σ n : ℕ, Index n) ≤ ℵ_ 1
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n => #(Index n)) ≤ Cardinal.sum (fun _ : ℕ => ℵ_ 1) :=
      Cardinal.sum_le_sum _ _ mk_index_le
    _ = ℵ₀ * ℵ_ 1 := by simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_id]
    _ ≤ ℵ_ 1 := (mul_le_mul' (Cardinal.aleph0_le_aleph 1) le_rfl).trans_eq
      (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))

theorem finite_index_type_le (n : ℕ) : typeLT (Index n) ≤ typeLT OmegaIndex := by
  let f : Index n → OmegaIndex := fun i => toLex ⟨n, i⟩
  have hf : StrictMono f := fun _ _ h => Sigma.Lex.right _ _ h
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

theorem omega_power_le_type : (ω_ 1 : Ordinal.{0}) ^ ω ≤ typeLT OmegaIndex := by
  rw [← Ordinal.iSup_pow_natCast (Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1))]
  apply Ordinal.iSup_le_iff.mpr
  intro n
  rw [← Ordinal.opow_natCast]
  apply (Ordinal.opow_le_opow_right
    (Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1))
    (show (↑n : Ordinal.{0}) ≤ ↑(n + 1) by exact_mod_cast Nat.le_succ n)).trans
  rw [← typeLT_index n]
  exact finite_index_type_le n

end Erdos1172Part3OmegaPowerIndex
