/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionSemantics

@[expose] public section

/-!
Term-parameter first-order formulas for the internal two-block partition
relation. Valuations and quantifiers range over all Boolean-valued names.
The final color choice is a Boolean join, not an external existential.
No partition value is asserted to be top in this language/interpretation file.
-/

open Fol bSet

namespace Erdos1172Part4InternalPartitionLanguage

variable {n : ℕ}

section RealizationHelpers

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

noncomputable abbrev termValue (v : DVec (bSet β) n) (t : bounded_term L_ZFC n) : bSet β :=
  boolean_realize_bounded_term (S := V β) v t DVec.nil

@[simp] theorem realize_mem (v : DVec (bSet β) n) (s t : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (mem' s t) DVec.nil =
      termValue v s ∈ᴮ termValue v t := rfl

@[simp] theorem realize_pair (v : DVec (bSet β) n) (s t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term (S := V β) v (pair' s t) DVec.nil =
      pair (termValue v s) (termValue v t) := rfl

theorem realize_liftTerm {k : ℕ} (v : DVec (bSet β) n)
    (xs : DVec (bSet β) k) (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term (S := V β) (xs.append v) (liftTerm t k) DVec.nil =
      termValue v t := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change boolean_realize_bounded_term (S := V β) (DVec.cons a (xs.append v))
      ((liftTerm t _) ↑ᵇ 1) DVec.nil = _
    exact (boolean_realize_bounded_term_subst_lift (S := V β)
      (xs.append v) a (liftTerm t _) DVec.nil).trans ih

@[simp] theorem realize_lift1 (v : DVec (bSet β) n) (a : bSet β)
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term (S := V β) (DVec.cons a v) (liftTerm t 1) DVec.nil =
      termValue v t :=
  realize_liftTerm v (DVec.cons a DVec.nil) t

@[simp] theorem realize_lift2 (v : DVec (bSet β) n) (a b : bSet β)
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term (S := V β) (DVec.cons a (DVec.cons b v))
      (liftTerm t 2) DVec.nil = termValue v t :=
  realize_liftTerm v (DVec.cons a (DVec.cons b DVec.nil)) t

@[simp] theorem realize_lift4 (v : DVec (bSet β) n) (a b c d : bSet β)
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term (S := V β)
      (DVec.cons a (DVec.cons b (DVec.cons c (DVec.cons d v))))
      (liftTerm t 4) DVec.nil = termValue v t :=
  realize_liftTerm v (DVec.cons a (DVec.cons b (DVec.cons c (DVec.cons d DVec.nil)))) t

end RealizationHelpers

section Realizations

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

@[simp] theorem realize_singleValuedFormula (v : DVec (bSet β) n) (f : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (singleValuedFormula f) DVec.nil =
      is_func (termValue v f) := by
  simp only [singleValuedFormula, is_func, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and (S := V β)]
  apply iInf_congr; intro w₁
  change bSet β at w₁
  apply iInf_congr; intro w₂
  change bSet β at w₂
  apply iInf_congr; intro z₁
  change bSet β at z₁
  apply iInf_congr; intro z₂
  change bSet β at z₂
  change _root_.imp
    ((pair w₁ z₁ ∈ᴮ termValue (DVec.cons z₂ (DVec.cons z₁ (DVec.cons w₂ (DVec.cons w₁ v))))
        (liftTerm f 4)) ⊓
      (pair w₂ z₂ ∈ᴮ termValue (DVec.cons z₂ (DVec.cons z₁ (DVec.cons w₂ (DVec.cons w₁ v))))
        (liftTerm f 4)))
    (_root_.imp (w₁ =ᴮ w₂) (z₁ =ᴮ z₂)) = _
  dsimp only [termValue]
  erw [realize_lift4 v z₂ z₁ w₂ w₁ f]

@[simp] theorem realize_totalOnFormula (v : DVec (bSet β) n) (A κ f : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (totalOnFormula A κ f) DVec.nil =
      is_total (termValue v A) (termValue v κ) (termValue v f) := by
  unfold totalOnFormula is_total
  apply iInf_congr
  intro i
  change bSet β at i
  change _root_.imp (i ∈ᴮ termValue (DVec.cons i v) (liftTerm A 1))
    (boolean_realize_bounded_formula (S := V β) (DVec.cons i v)
      (bd_ex (bd_and
        (mem' (bd_var ⟨0, by omega⟩) (liftTerm κ 2))
        (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (liftTerm f 2))))
      DVec.nil) = _
  dsimp only [termValue]
  erw [realize_lift1 v i A]
  apply congrArg (_root_.imp (i ∈ᴮ termValue v A))
  erw [boolean_realize_bounded_formula_ex (S := V β) (v := DVec.cons i v)
    (f := bd_and (mem' (bd_var ⟨0, by omega⟩) (liftTerm κ 2))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (liftTerm f 2)))]
  apply iSup_congr
  intro x
  change bSet β at x
  erw [boolean_realize_bounded_formula_and (S := V β) (v := DVec.cons x (DVec.cons i v))
    (f := mem' (bd_var ⟨0, by omega⟩) (liftTerm κ 2))
    (g := mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (liftTerm f 2))]
  change (x ∈ᴮ termValue (DVec.cons x (DVec.cons i v)) (liftTerm κ 2)) ⊓
    (pair i x ∈ᴮ termValue (DVec.cons x (DVec.cons i v)) (liftTerm f 2)) = _
  dsimp only [termValue]
  erw [realize_lift2 v x i κ, realize_lift2 v x i f]

@[simp] theorem realize_functionOnFormula (v : DVec (bSet β) n) (A κ f : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (functionOnFormula A κ f) DVec.nil =
      is_func' (termValue v A) (termValue v κ) (termValue v f) := by
  unfold functionOnFormula
  erw [boolean_realize_bounded_formula_and (S := V β) (v := v)
    (f := singleValuedFormula f) (g := totalOnFormula A κ f)]
  exact congrArg₂ (fun a b : β => a ⊓ b)
    (realize_singleValuedFormula v f) (realize_totalOnFormula v A κ f)

@[simp] theorem realize_rangeMemFormula (v : DVec (bSet β) n) (A f x : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (rangeMemFormula A f x) DVec.nil =
      bSet.ErdosPartition.rangeMem (termValue v A) (termValue v f) (termValue v x) := by
  unfold rangeMemFormula bSet.ErdosPartition.rangeMem
  erw [boolean_realize_bounded_formula_ex (S := V β) (v := v)
    (f := bd_and (mem' (bd_var ⟨0, by omega⟩) (liftTerm A 1))
      (mem' (pair' (bd_var ⟨0, by omega⟩) (liftTerm x 1)) (liftTerm f 1)))]
  apply iSup_congr
  intro i
  change bSet β at i
  erw [boolean_realize_bounded_formula_and (S := V β) (v := DVec.cons i v)
    (f := mem' (bd_var ⟨0, by omega⟩) (liftTerm A 1))
    (g := mem' (pair' (bd_var ⟨0, by omega⟩) (liftTerm x 1)) (liftTerm f 1))]
  change (i ∈ᴮ termValue (DVec.cons i v) (liftTerm A 1)) ⊓
    (pair i (termValue (DVec.cons i v) (liftTerm x 1)) ∈ᴮ
      termValue (DVec.cons i v) (liftTerm f 1)) = _
  dsimp only [termValue]
  erw [realize_lift1 v i A, realize_lift1 v i x, realize_lift1 v i f]

@[simp] theorem realize_increasingFormula (v : DVec (bSet β) n) (A f : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (increasingFormula A f) DVec.nil =
      bSet.ErdosPartition.increasingOn (termValue v A) (termValue v f) := by
  simp only [increasingFormula, bSet.ErdosPartition.increasingOn,
    boolean_realize_bounded_formula, boolean_realize_bounded_formula_and (S := V β)]
  apply iInf_congr; intro i
  change bSet β at i
  apply iInf_congr; intro j
  change bSet β at j
  apply iInf_congr; intro x
  change bSet β at x
  apply iInf_congr; intro y
  change bSet β at y
  change _root_.imp
    (((i ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm A 4) ⊓
       j ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm A 4)) ⊓
      i ∈ᴮ j) ⊓
     (pair i x ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm f 4) ⊓
      pair j y ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm f 4)))
    (x ∈ᴮ y) = _
  dsimp only [termValue]
  erw [realize_lift4 v y x j i A, realize_lift4 v y x j i f]

@[simp] theorem realize_separatedFormula (v : DVec (bSet β) n) (A B f g : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (separatedFormula A B f g) DVec.nil =
      bSet.ErdosPartition.separatedRanges (termValue v A) (termValue v B)
        (termValue v f) (termValue v g) := by
  simp only [separatedFormula, bSet.ErdosPartition.separatedRanges,
    boolean_realize_bounded_formula, boolean_realize_bounded_formula_and (S := V β)]
  apply iInf_congr; intro i
  change bSet β at i
  apply iInf_congr; intro j
  change bSet β at j
  apply iInf_congr; intro x
  change bSet β at x
  apply iInf_congr; intro y
  change bSet β at y
  change _root_.imp
    ((i ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm A 4) ⊓
      j ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm B 4)) ⊓
     (pair i x ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm f 4) ⊓
      pair j y ∈ᴮ termValue (DVec.cons y (DVec.cons x (DVec.cons j (DVec.cons i v)))) (liftTerm g 4)))
    (x ∈ᴮ y) = _
  dsimp only [termValue]
  erw [realize_lift4 v y x j i A, realize_lift4 v y x j i B,
    realize_lift4 v y x j i f, realize_lift4 v y x j i g]

@[simp] theorem realize_homogeneousFormula (v : DVec (bSet β) n) (color : Bool)
    (R A B f g : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (homogeneousFormula color R A B f g) DVec.nil =
      bSet.ErdosPartition.homogeneousUnion color (termValue v R) (termValue v A)
        (termValue v B) (termValue v f) (termValue v g) := by
  cases color <;>
    simp only [homogeneousFormula, bSet.ErdosPartition.homogeneousUnion,
      Bool.false_eq_true, ↓reduceIte, boolean_realize_bounded_formula]
  all_goals
    apply iInf_congr; intro x
    change bSet β at x
    apply iInf_congr; intro y
    change bSet β at y
    simp only [boolean_realize_bounded_formula_and (S := V β) (v := DVec.cons y (DVec.cons x v)),
      boolean_realize_bounded_formula_or (S := V β) (v := DVec.cons y (DVec.cons x v)),
      boolean_realize_bounded_formula_not (S := V β) (v := DVec.cons y (DVec.cons x v))]
    erw [realize_rangeMemFormula (DVec.cons y (DVec.cons x v))
        (liftTerm A 2) (liftTerm f 2) (bd_var ⟨1, by omega⟩),
      realize_rangeMemFormula (DVec.cons y (DVec.cons x v))
        (liftTerm B 2) (liftTerm g 2) (bd_var ⟨1, by omega⟩),
      realize_rangeMemFormula (DVec.cons y (DVec.cons x v))
        (liftTerm A 2) (liftTerm f 2) (bd_var ⟨0, by omega⟩),
      realize_rangeMemFormula (DVec.cons y (DVec.cons x v))
        (liftTerm B 2) (liftTerm g 2) (bd_var ⟨0, by omega⟩)]
    erw [realize_mem (DVec.cons y (DVec.cons x v))
      (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (liftTerm R 2)]
    dsimp only [termValue]
    erw [realize_pair (DVec.cons y (DVec.cons x v)) (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)]
    erw [realize_lift2 v y x A, realize_lift2 v y x B,
      realize_lift2 v y x f, realize_lift2 v y x g, realize_lift2 v y x R]
    rfl

@[simp] theorem realize_twoBlockWitnessFormula (v : DVec (bSet β) n) (color : Bool)
    (R A B κ f g : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (twoBlockWitnessFormula color R A B κ f g)
      DVec.nil = bSet.ErdosPartition.twoBlockWitness color
        (termValue v R) (termValue v A) (termValue v B) (termValue v κ)
        (termValue v f) (termValue v g) := by
  simp only [twoBlockWitnessFormula, bSet.ErdosPartition.twoBlockWitness,
    boolean_realize_bounded_formula_and (S := V β) (v := v),
    realize_functionOnFormula v A κ f, realize_functionOnFormula v B κ g,
    realize_increasingFormula v A f, realize_increasingFormula v B g,
    realize_separatedFormula v A B f g, realize_homogeneousFormula v color R A B f g]

@[simp] theorem realize_hasTwoBlockFormula (v : DVec (bSet β) n) (color : Bool)
    (R A B κ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (hasTwoBlockFormula color R A B κ) DVec.nil =
      bSet.ErdosPartition.hasTwoBlock color (termValue v R) (termValue v A)
        (termValue v B) (termValue v κ) := by
  let body : bounded_formula L_ZFC (n + 2) := twoBlockWitnessFormula color
    (liftTerm R 2) (liftTerm A 2) (liftTerm B 2) (liftTerm κ 2)
    (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)
  change boolean_realize_bounded_formula (S := V β) v (bd_ex (bd_ex body)) DVec.nil = _
  erw [boolean_realize_bounded_formula_ex (S := V β) (v := v) (f := bd_ex body)]
  unfold bSet.ErdosPartition.hasTwoBlock
  apply iSup_congr
  intro f
  change bSet β at f
  erw [boolean_realize_bounded_formula_ex (S := V β) (v := DVec.cons f v) (f := body)]
  apply iSup_congr
  intro g
  change bSet β at g
  change boolean_realize_bounded_formula (S := V β) (DVec.cons g (DVec.cons f v))
    (twoBlockWitnessFormula color (liftTerm R 2) (liftTerm A 2) (liftTerm B 2) (liftTerm κ 2)
      (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) DVec.nil = _
  erw [realize_twoBlockWitnessFormula (DVec.cons g (DVec.cons f v)) color
    (liftTerm R 2) (liftTerm A 2) (liftTerm B 2) (liftTerm κ 2)
    (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)]
  dsimp only [termValue]
  erw [realize_lift2 v g f R, realize_lift2 v g f A, realize_lift2 v g f B, realize_lift2 v g f κ]
  rfl

@[simp] theorem realize_partitionFormula (v : DVec (bSet β) n) (κ A B : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula (S := V β) v (partitionFormula κ A B) DVec.nil =
      bSet.ErdosPartition.partitionValue (termValue v κ) (termValue v A) (termValue v B) := by
  unfold partitionFormula bSet.ErdosPartition.partitionValue
  apply iInf_congr
  intro R
  change bSet β at R
  erw [boolean_realize_bounded_formula_or (S := V β) (v := DVec.cons R v)
    (f := hasTwoBlockFormula false (bd_var ⟨0, by omega⟩)
      (liftTerm A 1) (liftTerm B 1) (liftTerm κ 1))
    (g := hasTwoBlockFormula true (bd_var ⟨0, by omega⟩)
      (liftTerm A 1) (liftTerm B 1) (liftTerm κ 1))]
  erw [realize_hasTwoBlockFormula (DVec.cons R v) false (bd_var ⟨0, by omega⟩)
      (liftTerm A 1) (liftTerm B 1) (liftTerm κ 1),
    realize_hasTwoBlockFormula (DVec.cons R v) true (bd_var ⟨0, by omega⟩)
      (liftTerm A 1) (liftTerm B 1) (liftTerm κ 1)]
  dsimp only [termValue]
  erw [realize_lift1 v R A, realize_lift1 v R B, realize_lift1 v R κ]
  rfl

end Realizations

end Erdos1172Part4InternalPartitionLanguage
