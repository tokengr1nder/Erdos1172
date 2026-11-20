/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalHartogsInitial
public import Erdos1172.Part4InternalCardinalLanguage

@[expose] public section

/-!
Two concrete iterations of the internal Boolean-valued Hartogs construction.
These names satisfy the least-noninjecting-ordinal specifications over omega
and over its first Hartogs ordinal, respectively. No equality with a checked
ground-model omega-two, preservation theorem, GCH, or dense ideal is asserted.
-/

open Fol bSet

universe u

namespace bSet.ErdosOmegaTwo

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The concrete internal first uncountable ordinal name. -/
noncomputable def omegaOne : bSet 𝔹 := ErdosHartogs.hartogs (κ := bSet.omega)

/-- The concrete successor Hartogs ordinal over the internal omega-one name. -/
noncomputable def omegaTwo : bSet 𝔹 := ErdosHartogs.hartogs (κ := omegaOne)

theorem one_injects_omega : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) bSet.omega := by
  apply injects_into_of_subset
  exact of_nat_subset_omega (n := 1)

theorem omegaOne_Ord {Γ : 𝔹} : Γ ≤ Ord (omegaOne : bSet 𝔹) :=
  ErdosHartogs.hartogs_Ord (κ := bSet.omega) one_injects_omega

theorem omegaOne_spec {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.leastNoninjectingOrdinal bSet.omega (omegaOne : bSet 𝔹) :=
  ErdosHartogs.hartogs_spec (κ := bSet.omega) one_injects_omega

theorem omegaOne_not_injects {Γ : 𝔹} :
    Γ ≤ (injects_into (omegaOne : bSet 𝔹) bSet.omega)ᶜ :=
  ErdosHartogs.hartogs_not_le_omega (κ := bSet.omega) one_injects_omega

theorem one_mem_omegaOne : (⊤ : 𝔹) ≤ (1 : bSet 𝔹) ∈ᴮ omegaOne := by
  apply (ErdosHartogs.mem_hartogs_iff₀ (κ := bSet.omega)).mpr
  exact le_sup_of_le_left (le_sup_of_le_right bv_refl)

theorem one_injects_omegaOne : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) omegaOne := by
  apply injects_into_of_subset
  exact subset_of_mem_transitive (omegaOne_Ord.trans inf_le_right) one_mem_omegaOne

theorem omegaTwo_Ord {Γ : 𝔹} : Γ ≤ Ord (omegaTwo : bSet 𝔹) :=
  ErdosHartogs.hartogs_Ord (κ := omegaOne) one_injects_omegaOne

theorem omegaTwo_spec {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.leastNoninjectingOrdinal omegaOne (omegaTwo : bSet 𝔹) :=
  ErdosHartogs.hartogs_spec (κ := omegaOne) one_injects_omegaOne

theorem omegaTwo_not_injects {Γ : 𝔹} :
    Γ ≤ (injects_into (omegaTwo : bSet 𝔹) omegaOne)ᶜ :=
  ErdosHartogs.hartogs_not_le_omega (κ := omegaOne) one_injects_omegaOne

theorem omegaOne_initial {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.initialOrdinal (omegaOne : bSet 𝔹) :=
  ErdosHartogs.hartogs_initial (κ := bSet.omega) one_injects_omega

theorem omegaTwo_initial {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.initialOrdinal (omegaTwo : bSet 𝔹) :=
  ErdosHartogs.hartogs_initial (κ := omegaOne) one_injects_omegaOne

theorem omega_mem_omegaOne {Γ : 𝔹} :
    Γ ≤ (bSet.omega : bSet 𝔹) ∈ᴮ omegaOne :=
  ErdosHartogs.base_mem_hartogs (κ := bSet.omega) one_injects_omega Ord_omega

theorem omegaOne_mem_omegaTwo {Γ : 𝔹} :
    Γ ≤ (omegaOne : bSet 𝔹) ∈ᴮ omegaTwo :=
  ErdosHartogs.base_mem_hartogs (κ := omegaOne) one_injects_omegaOne omegaOne_Ord

theorem omegaTwo_le_of_initial_above {Γ : 𝔹} {α : bSet 𝔹}
    (Hinitial : Γ ≤ ErdosHartogs.initialOrdinal α) (Habove : Γ ≤ omegaOne ∈ᴮ α) :
    Γ ≤ omegaTwo ⊆ᴮ α :=
  ErdosHartogs.hartogs_le_of_initial_above (κ := omegaOne)
    one_injects_omegaOne Hinitial Habove

theorem omegaOne_member_injects {Γ : 𝔹} {η : bSet 𝔹}
    (Hmem : Γ ≤ η ∈ᴮ omegaOne) : Γ ≤ injects_into η bSet.omega := by
  apply injects_into_of_injection_into
  exact (ErdosHartogs.mem_hartogs_iff (κ := bSet.omega) one_injects_omega
    (ErdosHartogs.Ord_of_mem_hartogs (κ := bSet.omega) Hmem)).mp Hmem

theorem omegaTwo_member_injects {Γ : 𝔹} {η : bSet 𝔹}
    (Hmem : Γ ≤ η ∈ᴮ omegaTwo) : Γ ≤ injects_into η omegaOne := by
  apply injects_into_of_injection_into
  exact (ErdosHartogs.mem_hartogs_iff (κ := omegaOne) one_injects_omegaOne
    (ErdosHartogs.Ord_of_mem_hartogs (κ := omegaOne) Hmem)).mp Hmem

section ModelLanguage

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

open Erdos1172Part4InternalCardinalLanguage

/-- The actual omega-one name satisfies the first-order Hartogs formula over omega. -/
theorem omegaOne_fol_spec : (⊤ : β) ≤
    boolean_realize_bounded_formula (S := V β)
      (DVec.cons bSet.omega (DVec.cons (omegaOne : bSet β) DVec.nil))
      least_noninjecting_ordinal_f DVec.nil := by
  rw [realize_least_noninjecting_ordinal_f
    (κ := (bSet.omega : bSet β)) (α := (omegaOne : bSet β))]
  refine le_inf omegaOne_Ord (le_inf omegaOne_not_injects ?_)
  apply le_iInf
  intro γ
  rw [← _root_.deduction]
  exact omegaOne_member_injects inf_le_right

/-- The actual omega-two name satisfies the first-order Hartogs formula over omega-one. -/
theorem omegaTwo_fol_spec : (⊤ : β) ≤
    boolean_realize_bounded_formula (S := V β)
      (DVec.cons (omegaOne : bSet β) (DVec.cons (omegaTwo : bSet β) DVec.nil))
      least_noninjecting_ordinal_f DVec.nil := by
  rw [realize_least_noninjecting_ordinal_f
    (κ := (omegaOne : bSet β)) (α := (omegaTwo : bSet β))]
  refine le_inf omegaTwo_Ord (le_inf omegaTwo_not_injects ?_)
  apply le_iInf
  intro γ
  rw [← _root_.deduction]
  exact omegaTwo_member_injects inf_le_right

/-- The closed sentence `∃ α ∃ δ, Hartogs(ω, α) ∧ Hartogs(α, δ)`.
The two existential variables are stored as `[δ, α]` in the inner environment. -/
def twoHartogsSentence : sentence L_ZFC :=
  bd_ex (bd_ex (bd_and
    ((subst0_bounded_formula least_noninjecting_ordinal_f
      (omega' : bounded_term L_ZFC 1)) ↑ᶠᵇ' 1 # 0)
    (subst0_bounded_formula
      (least_noninjecting_ordinal_f.cast (by omega) : bounded_formula L_ZFC 3)
      (bd_var ⟨1, by omega⟩))))

/-- The explicit internal omega-one and omega-two names witness the closed sentence. -/
theorem V_models_twoHartogsSentence : ⊤ ⊩[V β] twoHartogsSentence := by
  have hfirst :
      boolean_realize_bounded_formula (S := V β)
        (DVec.cons (omegaTwo : bSet β) (DVec.cons (omegaOne : bSet β) DVec.nil))
        ((subst0_bounded_formula least_noninjecting_ordinal_f
          (omega' : bounded_term L_ZFC 1)) ↑ᶠᵇ' 1 # 0) DVec.nil =
      boolean_realize_bounded_formula (S := V β)
        (DVec.cons bSet.omega (DVec.cons (omegaOne : bSet β) DVec.nil))
        least_noninjecting_ordinal_f DVec.nil := by
    exact (boolean_realize_bounded_formula_insert_lift (S := V β)
      (DVec.cons (omegaOne : bSet β) DVec.nil) (omegaTwo : bSet β) 0 (by omega)
      (subst0_bounded_formula least_noninjecting_ordinal_f
        (omega' : bounded_term L_ZFC 1)) DVec.nil).trans
      (boolean_realize_subst_formula0 (V β) least_noninjecting_ordinal_f
        (omega' : bounded_term L_ZFC 1) (DVec.cons (omegaOne : bSet β) DVec.nil))
  have hsecond :
      boolean_realize_bounded_formula (S := V β)
        (DVec.cons (omegaTwo : bSet β) (DVec.cons (omegaOne : bSet β) DVec.nil))
        (subst0_bounded_formula
          (least_noninjecting_ordinal_f.cast (by omega) : bounded_formula L_ZFC 3)
          (bd_var ⟨1, by omega⟩)) DVec.nil =
      boolean_realize_bounded_formula (S := V β)
        (DVec.cons (omegaOne : bSet β) (DVec.cons (omegaTwo : bSet β) DVec.nil))
        least_noninjecting_ordinal_f DVec.nil := by
    rw [boolean_realize_subst_formula0 (V β)
      (least_noninjecting_ordinal_f.cast (by omega) : bounded_formula L_ZFC 3)
      (bd_var ⟨1, by omega⟩)
      (DVec.cons (omegaTwo : bSet β) (DVec.cons (omegaOne : bSet β) DVec.nil))]
    exact boolean_realize_cast_bounded_formula (S := V β) (f := least_noninjecting_ordinal_f)
  change ⊤ ≤ boolean_realize_bounded_formula (S := V β) DVec.nil twoHartogsSentence DVec.nil
  simp only [twoHartogsSentence, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_and]
  apply le_iSup_of_le (omegaOne : bSet β)
  apply le_iSup_of_le (omegaTwo : bSet β)
  exact le_inf (omegaOne_fol_spec.trans hfirst.symm.le) (omegaTwo_fol_spec.trans hsecond.symm.le)

end ModelLanguage

end bSet.ErdosOmegaTwo
