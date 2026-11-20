/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionLanguage
public import Erdos1172.Part4InternalHartogsUniqueness

@[expose] public section

/-!
A closed first-order sentence for the internal balanced two-block partition
target. Its Boolean value is proved equal to the value at the actual internal
omega-one and omega-two names. No theorem asserts that this value is top.
This is the displayed balanced relation, not the stronger all-target variant
and not a sentence asserting GCH or relative consistency.
-/

open Fol bSet
open Erdos1172Part4InternalCardinalLanguage
open Erdos1172Part4InternalPartitionLanguage

namespace Erdos1172Part4InternalPartitionSentence

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

theorem realize_firstHartogsFormula (α δ : bSet β) :
    boolean_realize_bounded_formula (S := V β)
      (DVec.cons δ (DVec.cons α DVec.nil)) firstHartogsFormula DVec.nil =
      ErdosHartogs.hartogsProperty bSet.omega α := by
  exact ((boolean_realize_bounded_formula_insert_lift (S := V β)
    (DVec.cons α DVec.nil) δ 0 (by omega)
    (subst0_bounded_formula least_noninjecting_ordinal_f
      (omega' : bounded_term L_ZFC 1)) DVec.nil).trans
    (boolean_realize_subst_formula0 (V β) least_noninjecting_ordinal_f
      (omega' : bounded_term L_ZFC 1) (DVec.cons α DVec.nil))).trans
    (realize_least_noninjecting_ordinal_f (κ := bSet.omega) (α := α))

theorem realize_secondHartogsFormula (α δ : bSet β) :
    boolean_realize_bounded_formula (S := V β)
      (DVec.cons δ (DVec.cons α DVec.nil)) secondHartogsFormula DVec.nil =
      ErdosHartogs.hartogsProperty α δ := by
  unfold secondHartogsFormula
  rw [boolean_realize_subst_formula0 (V β)
    (least_noninjecting_ordinal_f.cast (by omega) : bounded_formula L_ZFC 3)
    (bd_var ⟨1, by omega⟩) (DVec.cons δ (DVec.cons α DVec.nil))]
  change boolean_realize_bounded_formula (S := V β)
    (DVec.cons α (DVec.cons δ (DVec.cons α DVec.nil)))
    (least_noninjecting_ordinal_f.cast (by omega)) DVec.nil = _
  rw [boolean_realize_cast_bounded_formula (S := V β)
    (f := least_noninjecting_ordinal_f)
    (v := DVec.cons α (DVec.cons δ (DVec.cons α DVec.nil)))]
  exact realize_least_noninjecting_ordinal_f (κ := α) (α := δ)

theorem realize_partitionBody (α δ : bSet β) :
    boolean_realize_bounded_formula (S := V β)
      (DVec.cons δ (DVec.cons α DVec.nil)) partitionBody DVec.nil =
      ErdosPartition.partitionValue δ α bSet.omega :=
  realize_partitionFormula (DVec.cons δ (DVec.cons α DVec.nil)) _ _ _

theorem partitionValue_congr {α δ α' δ' : bSet β} {Γ : β}
    (Hα : Γ ≤ α =ᴮ α') (Hδ : Γ ≤ δ =ᴮ δ')
    (H : Γ ≤ ErdosPartition.partitionValue δ α bSet.omega) :
    Γ ≤ ErdosPartition.partitionValue δ' α' bSet.omega := by
  rw [← realize_partitionBody α δ] at H
  rw [← realize_partitionBody α' δ']
  have Henv : Γ ≤ ⨅ m : Fin 2,
      (V β).eq ((DVec.cons δ (DVec.cons α DVec.nil)).nth m.1 m.2)
        ((DVec.cons δ' (DVec.cons α' DVec.nil)).nth m.1 m.2) := by
    apply le_iInf
    intro m
    fin_cases m
    · exact Hδ
    · exact Hα
  exact (le_inf Henv H).trans
    (boolean_realize_bounded_formula_congr (S := V β) inferInstance
      (DVec.cons δ (DVec.cons α DVec.nil))
      (DVec.cons δ' (DVec.cons α' DVec.nil)) partitionBody DVec.nil)

theorem realize_part4Sentence_expanded :
    boolean_realize_bounded_formula (S := V β) DVec.nil part4Sentence DVec.nil =
      ⨆ α : bSet β, ⨆ δ : bSet β,
        ErdosHartogs.hartogsProperty bSet.omega α ⊓
          (ErdosHartogs.hartogsProperty α δ ⊓ ErdosPartition.partitionValue δ α bSet.omega) := by
  simp only [part4Sentence, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_and]
  apply iSup_congr
  intro α
  change bSet β at α
  apply iSup_congr
  intro δ
  change bSet β at δ
  exact congrArg₂ (fun a b : β => a ⊓ b) (realize_firstHartogsFormula α δ)
    (congrArg₂ (fun a b : β => a ⊓ b) (realize_secondHartogsFormula α δ)
      (realize_partitionBody α δ))

/-- Exact interpretation: internal cardinal existential witnesses cannot
weaken the partition target, since their Hartogs properties determine them. -/
theorem realize_part4Sentence :
    boolean_realize_bounded_formula (S := V β) DVec.nil part4Sentence DVec.nil =
      (ErdosPartition.part4Value : β) := by
  rw [realize_part4Sentence_expanded]
  apply le_antisymm
  · apply iSup_le
    intro α
    apply iSup_le
    intro δ
    exact partitionValue_congr
      (ErdosOmegaTwo.omegaOne_property_unique inf_le_left)
      (ErdosOmegaTwo.omegaTwo_property_unique inf_le_left (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right)
  · apply le_iSup_of_le (ErdosOmegaTwo.omegaOne : bSet β)
    apply le_iSup_of_le (ErdosOmegaTwo.omegaTwo : bSet β)
    exact le_inf ErdosOmegaTwo.omegaOne_property
      (le_inf ErdosOmegaTwo.omegaTwo_property le_rfl)

theorem forces_part4Sentence_iff {Γ : β} :
    (Γ ⊩[V β] part4Sentence) ↔ Γ ≤ (ErdosPartition.part4Value : β) := by
  change Γ ≤ boolean_realize_bounded_formula (S := V β) DVec.nil part4Sentence DVec.nil ↔ _
  rw [realize_part4Sentence]

end Erdos1172Part4InternalPartitionSentence
