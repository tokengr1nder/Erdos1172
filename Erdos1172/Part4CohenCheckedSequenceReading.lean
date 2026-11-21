/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenCheckedSequenceCover
public import Erdos1172.Part4CohenCheckedReadingWitness
public import Erdos1172.Part4BooleanOmegaSequenceTransport

@[expose] public section

/-!
# Actual first-stage recovery of supported checked-value omega sequences

Local cover fusion and fullness provide one source value sequence on an
actual stronger condition. The supported graph theorem then recovers the
entire ambient graph, including arbitrary mixed natural arguments.

The final theorem covers the original Boolean condition by actual source
function names with their source validity guards retained. It asserts
neither one global source representative nor recovery through the anonymous
subalgebra, which remains a separate construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet ErdosNameTransport ErdosOmegaSequence ErdosBoundedFunctionValue
open Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- One actual stronger cone recovers the whole supported function graph. -/
theorem exists_checked_sequence_reading
    (p : Conditions (ErdosOmegaTwo.omegaOne : bSet B))
    (A : PSet.{u}) (f : bSet (omegaOneAlgebra B))
    (Hf : condition p ≤ is_function omega (check A) f) :
    ∃ r : Conditions (ErdosOmegaTwo.omegaOne : bSet B), r ≤ p ∧
      ∃ g : bSet B, r.value ≤ is_function omega (check A) g ∧
        condition r ≤ f =ᴮ mapNames omegaOneFirstStageHom g := by
  classical
  let v : ℕ → bSet (omegaOneAlgebra B) := fun n => graphValue (check A) f (of_nat n)
  have Hv : condition p ≤ ⨅ n : ℕ, v n ∈ᴮ check A :=
    le_iInf (fun _ => graphValue_mem Hf of_nat_mem_omega)
  obtain ⟨r, Hrp, Hread⟩ := exists_checked_sequence_cover p A v Hv
  have Hvalues : ∀ n : ℕ, ∃ y : bSet B, r.value ≤ y ∈ᴮ check A ∧
      condition r ≤ v n =ᴮ mapNames omegaOneFirstStageHom y :=
    fun n => exists_checked_reading_witness r A (v n) (Hread n)
  choose y Hy using Hvalues
  refine ⟨r, Hrp, sequenceGraph y, sequenceGraph_is_function (fun n => (Hy n).1), ?_⟩
  have Hgraph : condition r ≤ f =ᴮ sequenceGraph v :=
    (condition_mono Hrp).trans (eq_sequenceGraph_graphValue Hf)
  rw [map_sequenceGraph]
  exact bv_trans Hgraph (sequenceGraph_congr (fun n => (Hy n).2))

/-- Every locally supported omega-to-check-A function is covered by actual
first-stage function names at its original Boolean condition. -/
theorem checked_sequence_reading_cover (A : PSet.{u})
    {f : bSet (omegaOneAlgebra B)} {Γ : omegaOneAlgebra B}
    (Hf : Γ ≤ is_function omega (check A) f) :
    Γ ≤ ⨆ g : bSet B,
      omegaOneFirstStageHom (is_function omega (check A) g) ⊓
        (f =ᴮ mapNames omegaOneFirstStageHom g) := by
  classical
  let V : omegaOneAlgebra B := ⨆ g : bSet B,
    omegaOneFirstStageHom (is_function omega (check A) g) ⊓ (f =ᴮ mapNames omegaOneFirstStageHom g)
  change Γ ≤ V
  by_contra Hnot
  have Hpositive : Γ ⊓ Vᶜ ≠ ⊥ := by
    intro Hzero
    apply Hnot
    have H : Γ ≤ (Vᶜ)ᶜ := le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr Hzero.le)
    simpa only [compl_compl] using H
  obtain ⟨p, Hp⟩ := exists_condition_le Hpositive
  obtain ⟨r, Hrp, g, Hg, Heq⟩ := exists_checked_sequence_reading p A f
    (Hp.trans (inf_le_left.trans Hf))
  have HrV : condition r ≤ V := le_iSup_of_le g
    (le_inf ((condition_le_firstStageHom_iff ErdosOmegaTwo.omegaOne r _).mpr Hg) Heq)
  have HrnotV : condition r ≤ Vᶜ := (condition_mono Hrp).trans (Hp.trans inf_le_right)
  exact condition_ne_bot r (bot_unique ((le_inf HrV HrnotV).trans inf_compl_eq_bot.le))

end Erdos1172CohenIteration
