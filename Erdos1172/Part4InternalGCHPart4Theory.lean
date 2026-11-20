/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Statement
public import Erdos1172.Part4InternalFullGCHSentence
public import Erdos1172.Part4InternalLocalConsistency
public import Erdos1172.Part4InternalPartitionFromIdeal

@[expose] public section

/-!
# The exact ZFC plus full-GCH plus balanced-Part-4 theory

Full GCH is one closed sentence ranging over all internal infinite sets,
not merely the CH premise used by the combinatorial partition theorem.
The same Boolean condition must force full GCH and the graph-independent
ideal data. A supplied nonzero condition then yields consistency of the
whole augmented theory by Boolean soundness.

No such condition, ideal, or joint model is constructed here. The final
theorem is conditional on those explicit mathematical inputs; it is not
an unconditional solution of the consistency question.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Fol bSet

namespace Erdos1172Part4InternalGCHTheory

open Erdos1172Part4InternalFullGCHSentence
open Erdos1172Part4InternalPartitionSentence
open bSet.ErdosFullGCH bSet.ErdosPartition bSet.ErdosPartitionFromIdeal
open bSet.ErdosOmegaTwo bSet.ErdosIdeal bSet.ErdosDenseBasis

theorem mem_gchPart4Theory {f : sentence L_ZFC} :
    f ∈ gchPart4Theory ↔ f ∈ ZFC ∨ f = fullGCHSentence ∨ f = part4Sentence := by
  simp only [gchPart4Theory, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

/-- Every axiom and both additional sentences hold at the same condition. -/
theorem forces_gchPart4Theory_of_values {Γ : β}
    (HGCH : Γ ≤ (fullGCHValue : β)) (Hpart : Γ ≤ (part4Value : β)) :
    Γ ⊩ₜ[V β] gchPart4Theory := by
  unfold all_forced_in
  apply le_iInf
  intro f
  apply le_iInf
  intro Hf
  rcases mem_gchPart4Theory.mp Hf with HZFC | rfl | rfl
  · have HZ : (⊤ : β) ≤ ⨅ f ∈ ZFC, boolean_realize_sentence (V β) f :=
      bSet_models_ZFC
    exact le_top.trans (HZ.trans ((iInf_le _ f).trans (iInf_le _ HZFC)))
  · exact forces_fullGCHSentence_iff.mpr HGCH
  · exact forces_part4Sentence_iff.mpr Hpart

/-- The partition sentence is derived, not a model hypothesis. Full GCH
and all eight ideal/basis fields are retained explicitly. -/
theorem forces_gchPart4Theory_of_ideal
    {J I D : bSet β} {Γ : β}
    (HGCH : Γ ≤ (fullGCHValue : β))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne) : Γ ⊩ₜ[V β] gchPart4Theory :=
  forces_gchPart4Theory_of_values HGCH
    (part4Value_of_normal_dense_ideal (CH_of_fullGCH HGCH)
      HJ Habsorb Hclosure Hdiag HD HDpos Hdense HI)

/-- A genuine nonzero joint condition would prove consistency of the
entire stated theory. Its existence is deliberately not asserted. -/
theorem consistent_gchPart4_of_nonzero_ideal
    {J I D : bSet β} {Γ : β}
    (Hnonzero : Γ ≠ ⊥)
    (HGCH : Γ ≤ (fullGCHValue : β))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne) : gchPart4Theory.is_consistent :=
  Fol.ErdosLocalConsistency.consistent_of_nonzero_forces_theory Hnonzero
    (forces_gchPart4Theory_of_ideal HGCH HJ Habsorb Hclosure Hdiag HD HDpos Hdense HI)

end Erdos1172Part4InternalGCHTheory
