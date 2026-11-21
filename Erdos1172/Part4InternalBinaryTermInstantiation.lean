/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionLanguage
public import Erdos1172.Part4InternalHartogsUniqueness

@[expose] public section

/-!
# Exact two-slot formula instantiation by arbitrary bounded terms

The outer substitution installs the second slot. The inner substitution
installs the first slot, lifted past the second. Thus the original formula
sees exactly `[first, second]`, not a reversed or ground-name environment.
-/

set_option autoImplicit false

open Fol bSet
open Erdos1172Part4InternalPartitionLanguage
open Erdos1172Part4InternalCardinalLanguage

namespace Erdos1172Part4InternalBinaryTermInstantiation

variable {n : ℕ}

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

theorem realize_binaryTermFormula (v : DVec (bSet β) n)
    (f : bounded_formula L_ZFC 2) (first second : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v
      (binaryTermFormula f first second) DVec.nil =
      boolean_realize_bounded_formula (S := V β)
        (DVec.cons (termValue v first) (DVec.cons (termValue v second) DVec.nil)) f DVec.nil := by
  unfold binaryTermFormula
  rw [boolean_realize_subst_formula0 (V β) _ second v]
  rw [boolean_realize_subst_formula0 (V β)
    (f.cast (by omega) : bounded_formula L_ZFC (n + 2))
    (liftTerm first 1) (DVec.cons (termValue v second) v)]
  erw [realize_lift1 v (termValue v second) first]
  rw [boolean_realize_cast_bounded_formula (S := V β) (f := f)]
  have Htrunc (a b : bSet β) {m : ℕ} (w : DVec (bSet β) m) {h : 2 ≤ m + 2} :
      DVec.trunc 2 h (DVec.cons a (DVec.cons b w)) = DVec.cons a (DVec.cons b DVec.nil) := by
    simp only [DVec.trunc, DVec.trunc_0_n]
  exact congrArg (fun w : DVec (V β) 2 =>
    boolean_realize_bounded_formula (S := V β) w f DVec.nil)
    (Htrunc (termValue v first) (termValue v second) v)

theorem realize_injectionFormula (v : DVec (bSet β) n)
    (source target : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v
      (injectionFormula source target) DVec.nil =
      injects_into (termValue v source) (termValue v target) :=
  (realize_binaryTermFormula v injects_into_f target source).trans realize_injects_into

theorem realize_hartogsFormula (v : DVec (bSet β) n)
    (base ordinal : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v
      (hartogsFormula base ordinal) DVec.nil =
      ErdosHartogs.hartogsProperty (termValue v base) (termValue v ordinal) :=
  (realize_binaryTermFormula v least_noninjecting_ordinal_f base ordinal).trans
    realize_least_noninjecting_ordinal_f

end Erdos1172Part4InternalBinaryTermInstantiation
