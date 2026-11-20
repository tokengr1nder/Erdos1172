/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFullGCH
public import Erdos1172.Part4InternalBinaryTermInstantiation

@[expose] public section

/-!
# A closed first-order sentence for full internal GCH

Every arbitrary internal name kappa admitting an injection from omega
has a Hartogs ordinal delta into which its full internal powerset
injects. The universal quantifier ranges over all Boolean-valued names,
including mixed names. There are no constants for ground cardinals and
no replacement of full GCH by its omega instance, CH.

This module proves exact realization, not the existence of a model in
which the sentence holds.
-/

set_option autoImplicit false

open Fol bSet
open Erdos1172Part4InternalPartitionLanguage
open Erdos1172Part4InternalBinaryTermInstantiation

namespace Erdos1172Part4InternalFullGCHSentence

variable {n : ℕ}

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

theorem realize_gchAtFormula (v : DVec (bSet β) n) (κ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (gchAtFormula κ) DVec.nil =
      ErdosFullGCH.gchAt (termValue v κ) := by
  unfold gchAtFormula ErdosFullGCH.gchAt
  erw [boolean_realize_bounded_formula_ex]
  apply iSup_congr
  intro δ
  change bSet β at δ
  erw [boolean_realize_bounded_formula_and]
  erw [realize_hartogsFormula, realize_injectionFormula]
  change ErdosHartogs.hartogsProperty
      (boolean_realize_bounded_term (S := V β) (DVec.cons δ v) (liftTerm κ 1) DVec.nil) δ ⊓
    injects_into
      (bv_powerset (boolean_realize_bounded_term (S := V β)
        (DVec.cons δ v) (liftTerm κ 1) DVec.nil)) δ = _
  erw [realize_lift1 v δ κ]

theorem realize_fullGCHSentence :
    boolean_realize_bounded_formula (S := V β) DVec.nil fullGCHSentence DVec.nil =
      (ErdosFullGCH.fullGCHValue : β) := by
  change (⨅ κ : bSet β, _root_.imp
    (boolean_realize_bounded_formula (S := V β) (DVec.cons κ DVec.nil)
      (injectionFormula omega' (bd_var ⟨0, by omega⟩)) DVec.nil)
    (boolean_realize_bounded_formula (S := V β) (DVec.cons κ DVec.nil)
      (gchAtFormula (bd_var ⟨0, by omega⟩)) DVec.nil)) = _
  unfold ErdosFullGCH.fullGCHValue
  apply iInf_congr
  intro κ
  erw [realize_injectionFormula, realize_gchAtFormula]
  rfl

theorem forces_fullGCHSentence_iff {Γ : β} :
    (Γ ⊩[V β] fullGCHSentence) ↔ Γ ≤ (ErdosFullGCH.fullGCHValue : β) := by
  change Γ ≤ boolean_realize_bounded_formula (S := V β)
    DVec.nil fullGCHSentence DVec.nil ↔ _
  rw [realize_fullGCHSentence]

end Erdos1172Part4InternalFullGCHSentence
