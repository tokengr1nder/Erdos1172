/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenCoverFusion
public import Erdos1172.Part4CohenReadingBridge

@[expose] public section

/-!
# Local checked-value covers for countable ambient sequences

A cover valid only below the original completed condition is padded by
that condition's complement. Actual countable cover fusion and canonical
refinement give one stronger condition reading every padded row. Its cone
lies below the original condition, so the dummy reading vanishes on its
first-stage value. The remaining joins are genuine checked-label readings.

The ground family need not be inhabited, and membership is not assumed at
top. Natural values may be mixed, and no single ground label is selected
at the whole original context. The ambient-name specialization uses the
canonical nontrivial Boolean structure on the actual omega-one iteration.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- A stronger condition cannot read the complement of the weaker cone
on any positive part of its own first-stage value. -/
theorem value_inf_reads_compl_eq_bot_of_le {K : bSet B}
    {r p : Conditions K} (Hrp : r ≤ p) :
    r.value ⊓ reads (condition p)ᶜ (Erdos1172BooleanNameIteration.name r) = ⊥ := by
  apply eq_bot_iff.mpr
  have Hread : r.value ≤ reads (condition p) (Erdos1172BooleanNameIteration.name r) :=
    value_le_reads (condition_mono Hrp)
  exact (inf_le_inf Hread le_rfl).trans
    (reads_inf_compl_eq_bot (condition p) (Erdos1172BooleanNameIteration.name r)).le

/-- Countably many set-indexed covers need cover only the starting cone.
Padding by its complement removes any need for globally valid covers or
inhabited label types. Only the already established local Hartogs condition
is needed for countable fusion. -/
theorem exists_countable_local_cover_extension {K : bSet B}
    (p : Conditions K)
    (HK : p.value ≤ ErdosHartogs.hartogsProperty omega K)
    {I : ℕ → Type u} (c : ∀ n : ℕ, I n → Algebra K)
    (Hcover : ∀ n : ℕ, condition p ≤ ⨆ i : I n, c n i) :
    ∃ r : Conditions K, r ≤ p ∧ ∀ n : ℕ,
      r.value ≤ ⨆ i : I n, reads (c n i) (Erdos1172BooleanNameIteration.name r) := by
  let padded : ∀ n : ℕ, Option (I n) → Algebra K := fun n i =>
    match i with
    | none => (condition p)ᶜ
    | some j => c n j
  have Hpadded (n : ℕ) : (⨆ i : Option (I n), padded n i) = ⊤ := by
    apply eq_top_iff.mpr
    calc
      (⊤ : Algebra K) = condition p ⊔ (condition p)ᶜ := sup_compl_eq_top.symm
      _ ≤ ⨆ i : Option (I n), padded n i :=
        sup_le ((Hcover n).trans (iSup_le (fun i =>
          le_iSup_of_le (some i) le_rfl))) (le_iSup_of_le none le_rfl)
  obtain ⟨q, Hq, Hsub, Hread⟩ := exists_countable_cover_extension HK
    (ErdosCohen.mem_conditions_iff.mp (Erdos1172BooleanNameIteration.name_mem p))
    padded Hpadded
  obtain ⟨r, Hrp, Hrv, Heq⟩ :=
    Erdos1172BooleanNameIteration.exists_extension_refinement p p.nonzero le_rfl
      (ErdosCohen.mem_conditions_iff.mpr Hq) Hsub
  refine ⟨r, Hrp, ?_⟩
  intro n
  have Hrread : r.value ≤ ⨆ i : Option (I n),
      reads (padded n i) (Erdos1172BooleanNameIteration.name r) :=
    bv_rw'' Heq (Hrv.trans (Hread n))
      (B_ext_iSup (h := fun i => reads_ext (padded n i)))
  calc
    r.value ≤ r.value ⊓ (⨆ i : Option (I n),
        reads (padded n i) (Erdos1172BooleanNameIteration.name r)) :=
      le_inf le_rfl Hrread
    _ = ⨆ i : Option (I n), r.value ⊓
        reads (padded n i) (Erdos1172BooleanNameIteration.name r) := inf_iSup_eq _ _
    _ ≤ ⨆ i : I n, reads (c n i) (Erdos1172BooleanNameIteration.name r) := by
      apply iSup_le
      intro i
      cases i with
      | none => exact (value_inf_reads_compl_eq_bot_of_le Hrp).le.trans bot_le
      | some i => exact inf_le_right.trans (le_iSup_of_le i le_rfl)

/-- An arbitrary ambient sequence, whose values lie in a checked ground
set only below `p`, has one actual stronger condition with a full local
checked-label reading cover for every coordinate. No nonemptiness of `A`,
external interpretation of mixed values, or global validity is supplied. -/
theorem exists_checked_sequence_cover
    (p : Conditions (ErdosOmegaTwo.omegaOne : bSet B))
    (A : PSet.{u}) (v : ℕ → bSet (omegaOneAlgebra B))
    (Hv : condition p ≤ ⨅ n : ℕ, v n ∈ᴮ check A) :
    ∃ r : Conditions (ErdosOmegaTwo.omegaOne : bSet B), r ≤ p ∧ ∀ n : ℕ,
      r.value ≤ ⨆ i : A.Type,
        reads (v n =ᴮ check (A.Func i)) (Erdos1172BooleanNameIteration.name r) := by
  apply exists_countable_local_cover_extension p ErdosOmegaTwo.omegaOne_property
    (fun n i => v n =ᴮ check (A.Func i))
  intro n
  apply (Hv.trans (iInf_le _ n)).trans
  rw [mem_unfold]
  apply iSup_le
  intro i
  apply inf_le_right.trans
  rw [check_func]
  exact le_iSup_of_le (check_cast i) le_rfl

end Erdos1172CohenIteration
