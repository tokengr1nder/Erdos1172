/-
Local Lean 4.33.1 compatibility changes for E1172, 2026-09-19.
Theorem statements and mathematical definitions are preserved.
See ../PROVENANCE.md for the pinned upstream source and modifications.
-/
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bfol.lean lines 1-450:
   Boolean-valued first-order logic — bStructure + early semantics. -/
module

public import Flypitch4.Fol
public import Mathlib.Order.CompleteBooleanAlgebra

@[expose] public section

open DVec

namespace Fol

section bfol

/-! ## bStructure — boolean-valued L-structure -/

/-- An L-Structure valued in a complete boolean algebra β.
    Analogous to `Structure L` from Fol.lean, but interpretations of relations
    return values in β rather than Prop. -/
structure bStructure (L : Language.{u}) (β : Type v) [CompleteBooleanAlgebra β] where
  carrier : Type u
  fun_map : ∀ {n}, L.functions n → DVec carrier n → carrier
  rel_map : ∀ {n}, L.relations n → DVec carrier n → β
  /-- Boolean equality on the carrier -/
  eq : carrier → carrier → β
  eq_refl : ∀ x, eq x x = ⊤
  eq_symm : ∀ x y, eq x y = eq y x
  eq_trans : ∀ {x} (y : carrier) {z}, eq x y ⊓ eq y z ≤ eq x z
  fun_congr : ∀ {n} (f : L.functions n) (x y : DVec carrier n),
    (DVec.map2 (eq) x y).fInf ≤ eq (fun_map f x) (fun_map f y)
  rel_congr : ∀ {n} (R : L.relations n) (x y : DVec carrier n),
    (DVec.map2 (eq) x y).fInf ⊓ rel_map R x ≤ rel_map R y

variable {L : Language.{u}} {β : Type v} [CompleteBooleanAlgebra β]

instance : CoeSort (bStructure L β) (Type u) := ⟨bStructure.carrier⟩

attribute [simp] bStructure.eq_refl

variable {S : bStructure L β}

@[simp] lemma eq_drefl : ∀ {n} (x : DVec S n),
    (DVec.map2 S.eq x x).fInf = ⊤
  | _, DVec.nil => rfl
  | _, DVec.cons x xs => by
      simp only [DVec.map2, DVec.fInf_cons, S.eq_refl, eq_drefl xs, inf_top_eq]

lemma eq_dsymm : ∀ {n} (x y : DVec S n),
    (DVec.map2 S.eq x y).fInf = (DVec.map2 S.eq y x).fInf
  | _, DVec.nil, DVec.nil => rfl
  | _, DVec.cons x xs, DVec.cons y ys => by
      simp [S.eq_symm x y, eq_dsymm xs ys]

lemma subst_realize_congr1 (v v' : ℕ → S) (x : S) (m : ℕ) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    ⨅ k : ℕ, S.eq (subst_realize v x m k) (subst_realize v' x m k) := by
  rw [le_iInf_iff]
  intro k
  rcases Nat.lt_trichotomy k m with h | h | h
  · simp [subst_realize, h]; exact iInf_le _ k
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h]; exact iInf_le _ (k - 1)

lemma subst_realize_congr2 (v : ℕ → S) (x y : S) (m : ℕ) :
    S.eq x y ≤ ⨅ k : ℕ, S.eq (subst_realize v x m k) (subst_realize v y m k) := by
  rw [le_iInf_iff]
  intro k
  rcases Nat.lt_trichotomy k m with h | h | h
  · simp [subst_realize, h]
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h]

/-! ## boolean_realize_term -/

@[simp] def boolean_realize_term (v : ℕ → S) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l), S.carrier
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => S.fun_map f xs
  | _, preterm.app t₁ t₂, xs =>
      boolean_realize_term v t₁ (DVec.cons (boolean_realize_term v t₂ DVec.nil) xs)

lemma boolean_realize_term_congr' {v v' : ℕ → S} (h : ∀ n, v n = v' n) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l),
    boolean_realize_term v t xs = boolean_realize_term v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [boolean_realize_term]
      rw [boolean_realize_term_congr' h t₂, boolean_realize_term_congr' h t₁]

lemma boolean_realize_term_subst (v : ℕ → S) :
    ∀ {l} (m : ℕ) (t : @preterm L l) (s : term L) (xs : DVec S l),
    boolean_realize_term
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) t xs =
    boolean_realize_term v (subst_term t s m) xs
  | _, m, preterm.var k, s, _ => by
      simp only [boolean_realize_term, subst_term, subst_realize_lt, subst_realize_gt,
                 subst_realize_var_eq]
      rcases Nat.lt_trichotomy k m with h | h | h
      · simp [h, Nat.lt_asymm h]
      · subst h; simp
      · simp [h, Nat.lt_asymm h]
  | _, _, preterm.func _, _, _ => rfl
  | _, m, preterm.app t₁ t₂, s, xs => by
      simp only [boolean_realize_term, subst_term]
      rw [boolean_realize_term_subst v m t₂ s DVec.nil,
          boolean_realize_term_subst v m t₁ s]

lemma boolean_realize_term_subst_lift (v : ℕ → S) (x : S) (m : ℕ) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l),
    boolean_realize_term (subst_realize v x m) (lift_term_at t 1 m) xs =
    boolean_realize_term v t xs
  | _, preterm.var k, DVec.nil => by
      simp only [boolean_realize_term, lift_term_at]
      by_cases h : m ≤ k
      · have hmk1 : m < k + 1 := Nat.lt_succ_of_le h
        simp only [if_pos h, subst_realize_gt _ _ hmk1, Nat.add_sub_cancel]
      · have hkm : k < m := Nat.lt_of_not_le h
        simp only [if_neg h, boolean_realize_term, subst_realize_lt _ _ hkm]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [boolean_realize_term, lift_term_at]
      rw [boolean_realize_term_subst_lift v x m t₂ DVec.nil,
          boolean_realize_term_subst_lift v x m t₁]

lemma boolean_realize_term_congr_gen (v v' : ℕ → S) :
    ∀ {l} (t : @preterm L l) (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ≤
      S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs')
  | _, preterm.var k, _, _ => le_trans inf_le_left (iInf_le _ k)
  | _, preterm.func f, xs, xs' => le_trans inf_le_right (S.fun_congr f xs xs')
  | _, preterm.app t₁ t₂, xs, xs' => by
      simp only [boolean_realize_term]
      refine le_trans ?_ (boolean_realize_term_congr_gen v v' t₁
        (DVec.cons (boolean_realize_term v t₂ DVec.nil) xs)
        (DVec.cons (boolean_realize_term v' t₂ DVec.nil) xs'))
      simp only [DVec.map2, DVec.fInf_cons]
      apply le_inf
      · exact inf_le_left
      · apply le_inf
        · have h2 := boolean_realize_term_congr_gen v v' t₂ DVec.nil DVec.nil
          simp only [DVec.map2, DVec.fInf_nil, inf_top_eq] at h2
          exact le_trans inf_le_left h2
        · exact inf_le_right

lemma boolean_realize_term_congr_iInf (v v' : ℕ → S) {l} (t : @preterm L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs) := by
  have h := boolean_realize_term_congr_gen v v' t xs xs
  simp only [eq_drefl, inf_top_eq] at h
  exact h

/-! ## boolean_realize_formula -/

@[simp] def boolean_realize_formula : ∀ {l}, (ℕ → S) → @preformula L l → DVec S l → β
  | _, v, preformula.falsum, _ => ⊥
  | _, v, preformula.equal t₁ t₂, _ =>
      S.eq (boolean_realize_term v t₁ DVec.nil) (boolean_realize_term v t₂ DVec.nil)
  | _, v, preformula.rel R, xs => S.rel_map R xs
  | _, v, preformula.apprel f t, xs =>
      boolean_realize_formula v f (DVec.cons (boolean_realize_term v t DVec.nil) xs)
  | _, v, preformula.imp f₁ f₂, xs =>
      imp (boolean_realize_formula v f₁ xs) (boolean_realize_formula v f₂ xs)
  | _, v, preformula.all f, xs =>
      ⨅ x : S, boolean_realize_formula (subst_realize v x 0) f xs

lemma boolean_realize_formula_congr' : ∀ {l} {v v' : ℕ → S} (h : ∀ n, v n = v' n)
    (f : @preformula L l) (xs : DVec S l),
    boolean_realize_formula v f xs = boolean_realize_formula v' f xs
  | _, _, _, h, preformula.falsum, _ => rfl
  | _, _, _, h, preformula.equal t₁ t₂, _ => by
      simp only [boolean_realize_formula, boolean_realize_term_congr' h]
  | _, _, _, h, preformula.rel R, _ => rfl
  | _, v, v', h, preformula.apprel f t, xs => by
      simp only [boolean_realize_formula, boolean_realize_term_congr' h]
      exact boolean_realize_formula_congr' h f _
  | _, v, v', h, preformula.imp f₁ f₂, xs => by
      simp only [boolean_realize_formula]
      congr 1
      · exact boolean_realize_formula_congr' h f₁ xs
      · exact boolean_realize_formula_congr' h f₂ xs
  | _, v, v', h, preformula.all f, xs => by
      simp only [boolean_realize_formula]
      congr 1; funext x
      exact boolean_realize_formula_congr' (fun k => subst_realize_congr h x 0 k) f xs

lemma boolean_realize_formula_subst : ∀ {l} (v : ℕ → S) (m : ℕ) (f : @preformula L l)
    (s : term L) (xs : DVec S l),
    boolean_realize_formula
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) f xs =
    boolean_realize_formula v (subst_formula f s m) xs
  | _, v, m, preformula.falsum, s, xs => rfl
  | _, v, m, preformula.equal t₁ t₂, s, xs => by
      simp [boolean_realize_term_subst]
  | _, v, m, preformula.rel R, s, xs => rfl
  | _, v, m, preformula.apprel f t, s, xs => by
      simp only [boolean_realize_formula, subst_formula, boolean_realize_term_subst]
      rw [boolean_realize_formula_subst v m f s]
  | _, v, m, preformula.imp f₁ f₂, s, xs => by
      simp only [boolean_realize_formula, subst_formula]
      congr 1
      · rw [boolean_realize_formula_subst v m f₁ s xs]
      · rw [boolean_realize_formula_subst v m f₂ s xs]
  | _, v, m, preformula.all f, s, xs => by
      simp only [boolean_realize_formula, subst_formula]
      congr 1; funext x
      rw [← boolean_realize_formula_subst (subst_realize v x 0) (m + 1) f s xs]
      apply boolean_realize_formula_congr'
      intro k
      rw [subst_realize2_0, ← boolean_realize_term_subst_lift v x 0, lift_term_def, lift_term2]

lemma boolean_realize_formula_subst0 {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    boolean_realize_formula (subst_realize v (boolean_realize_term v s DVec.nil) 0) f xs =
    boolean_realize_formula v (subst_formula f s 0) xs := by
  have h := boolean_realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs

lemma boolean_realize_formula_subst_lift : ∀ {l} (v : ℕ → S) (x : S) (m : ℕ)
    (f : @preformula L l) (xs : DVec S l),
    boolean_realize_formula (subst_realize v x m) (lift_formula_at f 1 m) xs =
    boolean_realize_formula v f xs
  | _, v, x, m, preformula.falsum, xs => rfl
  | _, v, x, m, preformula.equal t₁ t₂, xs => by
      simp [boolean_realize_term_subst_lift]
  | _, v, x, m, preformula.rel R, xs => rfl
  | _, v, x, m, preformula.apprel f t, xs => by
      simp only [boolean_realize_formula, lift_formula_at, boolean_realize_term_subst_lift]
      rw [boolean_realize_formula_subst_lift v x m f]
  | _, v, x, m, preformula.imp f₁ f₂, xs => by
      simp only [boolean_realize_formula, lift_formula_at]
      congr 1
      · exact boolean_realize_formula_subst_lift v x m f₁ xs
      · exact boolean_realize_formula_subst_lift v x m f₂ xs
  | _, v, x, m, preformula.all f, xs => by
      simp only [boolean_realize_formula, lift_formula_at]
      congr 1; funext x'
      rw [boolean_realize_formula_congr' (subst_realize2_0 v x' x m) (lift_formula_at f 1 (m + 1)) xs]
      exact boolean_realize_formula_subst_lift (subst_realize v x' 0) x (m + 1) f xs

lemma boolean_realize_formula_congr_gen : ∀ (v v' : ℕ → S) {l} (f : @preformula L l)
    (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
    boolean_realize_formula v f xs ≤ boolean_realize_formula v' f xs'
  | v, v', _, preformula.falsum, _, _ => inf_le_right
  | v, v', _, preformula.equal t₁ t₂, DVec.nil, DVec.nil => by
      simp only [boolean_realize_formula, DVec.map2, DVec.fInf_nil, inf_top_eq]
      -- Goal: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v' t₁)(brt v' t₂)
      refine le_trans ?_ (S.eq_trans (boolean_realize_term v t₂ DVec.nil))
      apply le_inf
      · -- Need: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v' t₁)(brt v t₂)
        refine le_trans ?_ (S.eq_trans (boolean_realize_term v t₁ DVec.nil))
        apply le_inf
        · -- Need: I ⊓ ... ≤ S.eq(brt v' t₁)(brt v t₁)
          -- = S.eq(brt v t₁)(brt v' t₁) by symm, and I ≤ that by congr_iInf
          rw [S.eq_symm (boolean_realize_term v' t₁ DVec.nil) (boolean_realize_term v t₁ DVec.nil)]
          exact le_trans inf_le_left (boolean_realize_term_congr_iInf v v' t₁ DVec.nil)
        · exact inf_le_right  -- I ⊓ S.eq... ≤ S.eq(brt v t₁)(brt v t₂)
      · -- Need: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v t₂)(brt v' t₂)
        exact le_trans inf_le_left (boolean_realize_term_congr_iInf v v' t₂ DVec.nil)
  | v, v', _, preformula.rel R, xs, xs' => by
      simp only [boolean_realize_formula]
      exact le_trans (inf_le_inf inf_le_right le_rfl) (S.rel_congr R xs xs')
  | v, v', _, preformula.apprel f t, xs, xs' => by
      simp only [boolean_realize_formula]
      refine le_trans ?_ (boolean_realize_formula_congr_gen v v' f
        (DVec.cons (boolean_realize_term v t DVec.nil) xs)
        (DVec.cons (boolean_realize_term v' t DVec.nil) xs'))
      simp only [DVec.map2, DVec.fInf_cons]
      -- Need: I ⊓ xs_eq ⊓ brf v f (brt v t :: xs) ≤
      --         I ⊓ (S.eq(brt v t)(brt v' t) ⊓ xs_eq) ⊓ brf v f (brt v t :: xs)
      -- brf does not change; so need to weaken I ⊓ xs_eq to I ⊓ (S.eq ⊓ xs_eq)
      apply le_inf
      · -- I ⊓ xs_eq ⊓ brf ≤ I ⊓ (S.eq ⊓ xs_eq)
        apply le_inf
        · exact le_trans inf_le_left inf_le_left  -- ≤ I
        · apply le_inf
          · -- ≤ S.eq(brt v t)(brt v' t)
            exact le_trans (le_trans inf_le_left inf_le_left)
              (boolean_realize_term_congr_iInf v v' t DVec.nil)
          · exact le_trans inf_le_left inf_le_right  -- ≤ xs_eq
      · exact inf_le_right  -- ≤ brf v f (brt v t :: xs)
  | v, v', _, preformula.imp f₁ f₂, xs, xs' => by
      simp only [boolean_realize_formula, imp, inf_sup_left]
      apply sup_le_sup
      · -- Need: I ⊓ xs_eq ⊓ b_f₁ᶜ ≤ b_f₁'ᶜ
        apply le_neg_of_inf_eq_bot
        -- From IH with v↔v', xs↔xs': I' ⊓ xs_eq' ⊓ b_f₁' ≤ b_f₁
        -- I' = (⨅ k, S.eq (v' k) (v k)) = I  (by eq_symm)
        -- xs_eq' = (xs'.map2 S.eq xs).fInf = xs_eq  (by eq_dsymm)
        have key := boolean_realize_formula_congr_gen v' v f₁ xs' xs
        rw [show (⨅ k : ℕ, S.eq (v' k) (v k)) = (⨅ k : ℕ, S.eq (v k) (v' k)) from
              iInf_congr fun k => S.eq_symm _ _,
            ← eq_dsymm xs xs'] at key
        have bot := sub_eq_bot_of_le key
        -- bot: b_f₁ᶜ ⊓ (I ⊓ xs_eq ⊓ b_f₁') = ⊥
        -- Need: b_f₁' ⊓ (I ⊓ xs_eq ⊓ b_f₁ᶜ) = ⊥
        -- These are equal by commutativity and associativity of ⊓
        have : boolean_realize_formula v' f₁ xs' ⊓
               ((⨅ k, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
               (boolean_realize_formula v f₁ xs)ᶜ) =
               (boolean_realize_formula v f₁ xs)ᶜ ⊓
               ((⨅ k, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
               boolean_realize_formula v' f₁ xs') := by ac_rfl
        rw [this]; exact bot
      · exact boolean_realize_formula_congr_gen v v' f₂ xs xs'
  | v, v', _, preformula.all f, DVec.nil, DVec.nil => by
      simp only [boolean_realize_formula, DVec.map2, DVec.fInf_nil, inf_top_eq]
      rw [le_iInf_iff]
      intro x
      refine le_trans ?_ (boolean_realize_formula_congr_gen (subst_realize v x 0)
        (subst_realize v' x 0) f DVec.nil DVec.nil)
      simp only [DVec.map2, DVec.fInf_nil, inf_top_eq]
      apply le_inf
      · exact le_trans inf_le_left (subst_realize_congr1 v v' x 0)
      · exact le_trans inf_le_right (iInf_le _ x)

lemma boolean_realize_formula_congr (v v' : ℕ → S) {l} (f : @preformula L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ boolean_realize_formula v f xs ≤
    boolean_realize_formula v' f xs := by
  have key := boolean_realize_formula_congr_gen v v' f xs xs
  have hd : (DVec.map2 S.eq xs xs).fInf = ⊤ := eq_drefl xs
  rw [hd, inf_top_eq] at key
  exact le_trans (le_inf le_rfl le_top) (by rw [inf_top_eq]; exact key)

lemma boolean_realize_formula_subst_congr (v : ℕ → S) (s s' : term L) :
    ∀ {m l} (f : @preformula L l) (xs : DVec S l),
    S.eq (boolean_realize_term v (lift_term s m) DVec.nil)
         (boolean_realize_term v (lift_term s' m) DVec.nil) ⊓
    boolean_realize_formula v (subst_formula f s m) xs ≤
    boolean_realize_formula v (subst_formula f s' m) xs := by
  intro m l f xs
  rw [← boolean_realize_formula_subst v m f s xs,
      ← boolean_realize_formula_subst v m f s' xs]
  refine le_trans ?_
    (boolean_realize_formula_congr
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m)
      (subst_realize v (boolean_realize_term v (lift_term s' m) DVec.nil) m) f xs)
  apply inf_le_inf_right
  exact subst_realize_congr2 v _ _ m

lemma boolean_realize_formula_subst_congr0 (v : ℕ → S) (s s' : term L) {l} (f : @preformula L l)
    (xs : DVec S l) :
    S.eq (boolean_realize_term v s DVec.nil) (boolean_realize_term v s' DVec.nil) ⊓
    boolean_realize_formula v (subst_formula f s 0) xs ≤
    boolean_realize_formula v (subst_formula f s' 0) xs := by
  have h := boolean_realize_formula_subst_congr v s s' (m := 0) f xs
  simp only [lift_term_zero] at h
  exact h

@[simp] lemma boolean_realize_formula_not (v : ℕ → S) (f : formula L) :
    boolean_realize_formula v (not' f) DVec.nil = (boolean_realize_formula v f DVec.nil)ᶜ := by
  simp [not', boolean_realize_formula, imp]

/-! ## Satisfiability — boolean_realize_formula_glb, bstatisfied -/

def boolean_realize_formula_glb (S : bStructure L β) (f : formula L) : β :=
  ⨅ v : ℕ → S, boolean_realize_formula v f DVec.nil

notation "⟦" f "⟧[" S "]ᵤ" => Fol.boolean_realize_formula_glb S f

variable (β) in
def bstatisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : bStructure L β) (v : ℕ → S),
    (⨅ f' ∈ T, boolean_realize_formula v (f' : formula L) DVec.nil) ≤
    boolean_realize_formula v f DVec.nil

notation:51 T " ⊨ᵤ[" β "] " f => Fol.bstatisfied β T f

def bstatisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ᵤ[β] f :=
  fun S v => le_trans (iInf_le _ f) (iInf_le _ hf)

/-! ## boolean_formula_soundness -/

/-- Soundness for boolean-valued semantics: if Γ ⊢ A, then Γ ⊨ᵤ[β] A. -/
lemma boolean_formula_soundness {Γ : Set (formula L)} {A : formula L}
    (H : Γ ⊢ A) : Γ ⊨ᵤ[β] A := by
  induction H with
  | axm h => exact bstatisfied_of_mem h
  | impI _ ih =>
    intro S v
    simp only [boolean_realize_formula]
    rw [deduction_simp]
    refine le_trans ?_ (ih S v)
    rw [inf_comm, iInf_insert]
  | impE A _ _ ih₁ ih₂ =>
    intro S v
    have h1 := ih₁ S v
    have h2 := ih₂ S v
    simp only [boolean_realize_formula] at h1
    exact le_trans (le_inf h1 h2) (imp_inf_le _ _)
  | falsumE _ ih =>
    intro S v
    apply le_of_sub_eq_bot
    apply bot_unique
    refine le_trans ?_ (ih S v)
    rw [iInf_insert, boolean_realize_formula_not]
  | allI _ ih =>
    intro S v
    simp only [boolean_realize_formula]
    rw [le_iInf_iff]
    intro x
    refine le_trans ?_ (ih S _)
    apply le_iInf
    intro f
    apply le_iInf
    rintro ⟨f', hf', rfl⟩
    rw [boolean_realize_formula_subst_lift]
    exact le_trans (iInf_le _ f') (iInf_le _ hf')
  | allE₂ A t _ ih =>
    intro S v
    rw [← boolean_realize_formula_subst0]
    exact le_trans (ih S v) (iInf_le _ _)
  | ref Γ t =>
    intro S v
    simp [boolean_realize_formula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro S v
    refine le_trans ?_ (boolean_realize_formula_subst_congr0 v s t f DVec.nil)
    exact le_inf (ih₁ S v) (ih₂ S v)

/-! ## boolean_realize_bounded_term -/

@[simp] def boolean_realize_bounded_term {n} (v : DVec S n) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l), S.carrier
  | _, bd_var k, _ => v.nth k.1 k.2
  | _, bd_func f, xs => S.fun_map f xs
  | _, bd_app t₁ t₂, xs =>
      boolean_realize_bounded_term v t₁
        (DVec.cons (boolean_realize_bounded_term v t₂ DVec.nil) xs)

lemma boolean_realize_bounded_term_eq {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₂ k = v₁.nth k hk) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
    boolean_realize_term v₂ t.fst xs = boolean_realize_bounded_term v₁ t xs
  | _, bd_var k, _ => hv k.1 k.2
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs => by
      simp only [boolean_realize_term, boolean_realize_bounded_term, bounded_preterm.fst]
      rw [boolean_realize_bounded_term_eq hv t₂ DVec.nil,
          boolean_realize_bounded_term_eq hv t₁]

lemma boolean_realize_bounded_term_irrel' {n n'} {v₁ : DVec S n} {v₂ : DVec S n'}
    (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
    {l} (t : bounded_preterm L n l) (t' : bounded_preterm L n' l)
    (ht : t.fst = t'.fst) (xs : DVec S l) :
    boolean_realize_bounded_term v₁ t xs = boolean_realize_bounded_term v₂ t' xs := by
  induction t generalizing n' with
  | bd_var k =>
    cases t' with
    | bd_var k' =>
      simp only [bounded_preterm.fst, preterm.var.injEq] at ht
      simp only [boolean_realize_bounded_term]
      have hk : k.1 = k'.1 := ht
      calc v₁.nth k.1 k.2 = v₂.nth k.1 (hk ▸ k'.2) := h k.1 k.2 (hk ▸ k'.2)
        _ = v₂.nth k'.1 k'.2 := by congr 1
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_func f =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func f' =>
      simp only [bounded_preterm.fst, preterm.func.injEq] at ht
      simp [boolean_realize_bounded_term, ht]
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_app t₁ t₂ iht ihs =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app t₁' t₂' =>
      simp only [bounded_preterm.fst, preterm.app.injEq] at ht
      simp only [boolean_realize_bounded_term]
      rw [ihs h t₂' ht.2 DVec.nil, iht h t₁' ht.1]

lemma boolean_realize_bounded_term_subst_lift' {n} (v : DVec S n) (x : S) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
    boolean_realize_bounded_term (DVec.cons x v) (t ↑ᵇ 1) xs =
    boolean_realize_bounded_term v t xs
  | _, bd_var k, _ => by
      simp only [boolean_realize_bounded_term, lift_bounded_term, lift_bounded_term_at,
                 Nat.zero_le, if_true]
      simp [DVec.nth]
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs => by
      simp only [boolean_realize_bounded_term, lift_bounded_term, lift_bounded_term_at]
      rw [boolean_realize_bounded_term_subst_lift' v x t₂ DVec.nil,
          boolean_realize_bounded_term_subst_lift' v x t₁]

@[simp] lemma boolean_realize_bounded_term_subst_lift {n} (v : DVec S n) (x : S)
    {l} (t : bounded_preterm L n l) (xs : DVec S l) :
    boolean_realize_bounded_term (DVec.cons x v) (t ↑ᵇ 1) xs =
    boolean_realize_bounded_term v t xs :=
  boolean_realize_bounded_term_subst_lift' v x t xs

/-! ## boolean_realize_bounded_formula -/

@[simp] def boolean_realize_bounded_formula :
    ∀ {n l} (v : DVec S n) (f : bounded_preformula L n l) (xs : DVec S l), β
  | _, _, v, bd_falsum, _ => ⊥
  | _, _, v, bd_equal t₁ t₂, _ =>
      S.eq (boolean_realize_bounded_term v t₁ DVec.nil)
           (boolean_realize_bounded_term v t₂ DVec.nil)
  | _, _, _, bd_rel R, xs => S.rel_map R xs
  | _, _, v, bd_apprel f t, xs =>
      boolean_realize_bounded_formula v f
        (DVec.cons (boolean_realize_bounded_term v t DVec.nil) xs)
  | _, _, v, bd_imp f₁ f₂, xs =>
      imp (boolean_realize_bounded_formula v f₁ xs)
          (boolean_realize_bounded_formula v f₂ xs)
  | _, _, v, bd_all f, xs =>
      ⨅ x : S, boolean_realize_bounded_formula (DVec.cons x v) f xs

/-! ## boolean_realize_sentence — src/bfol.lean:456-459 -/

@[reducible] def boolean_realize_sentence (S : bStructure L β) (f : sentence L) : β :=
  boolean_realize_bounded_formula (DVec.nil : DVec S 0) f DVec.nil

notation "⟦" f "⟧[" S "]" => Fol.boolean_realize_sentence S f

/-! ## boolean_realize_bounded_formula_eq — src/bfol.lean:461-475 -/

lemma boolean_realize_bounded_formula_eq : ∀ {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₂ k = v₁.nth k hk) {l} (t : bounded_preformula L n l)
    (xs : DVec S l), boolean_realize_formula v₂ t.fst xs = boolean_realize_bounded_formula v₁ t xs
  | _, v₁, v₂, hv, _, bd_falsum, _ => rfl
  | _, v₁, v₂, hv, _, bd_equal t₁ t₂, _ => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      congr 1 <;> apply boolean_realize_bounded_term_eq hv
  | _, v₁, v₂, hv, _, bd_rel R, _ => rfl
  | _, v₁, v₂, hv, _, bd_apprel f t, xs => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_term_eq hv t DVec.nil]
      exact boolean_realize_bounded_formula_eq hv f _
  | _, v₁, v₂, hv, _, bd_imp f₁ f₂, xs => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_formula_eq hv, boolean_realize_bounded_formula_eq hv]
  | _, v₁, v₂, hv, _, bd_all f, xs => by
      simp only [bounded_preformula.fst, boolean_realize_formula, boolean_realize_bounded_formula]
      congr 1
      ext x
      apply boolean_realize_bounded_formula_eq
      intro k hk
      cases k with
      | zero => rfl
      | succ k => exact hv k (Nat.lt_of_succ_lt_succ hk)

lemma boolean_realize_bounded_formula_eq' {n} {v₁ : DVec S n} (x : S)
    {l} (t : bounded_preformula L n l) (xs : DVec S l) :
    boolean_realize_bounded_formula v₁ t xs =
    boolean_realize_formula (fun k => if h : k < n then v₁.nth k h else x) t.fst xs := by
  symm
  apply boolean_realize_bounded_formula_eq
  intro k hk
  rw [dif_pos hk]

lemma boolean_realize_bounded_term_eq' {n} {v₁ : DVec S n} (x : S)
    {l} (t : bounded_preterm L n l) (xs : DVec S l) :
    boolean_realize_bounded_term v₁ t xs =
    boolean_realize_term (fun k => if h : k < n then v₁.nth k h else x) t.fst xs := by
  symm
  apply boolean_realize_bounded_term_eq
  intro k hk
  rw [dif_pos hk]

/-! ## boolean_realize_bounded_formula_congr — src/bfol.lean:489-503 -/

lemma boolean_realize_bounded_formula_congr {n l} (H_nonempty : Nonempty S)
    (v₁ v₂ : DVec S n) (f : bounded_preformula L n l) (xs : DVec S l) :
    ((⨅ m : Fin n, S.eq (v₁.nth m.1 m.2) (v₂.nth m.1 m.2)) ⊓
     boolean_realize_bounded_formula v₁ f xs : β) ≤
    boolean_realize_bounded_formula v₂ f xs := by
  obtain ⟨x⟩ := H_nonempty
  rw [boolean_realize_bounded_formula_eq' (v₁ := v₁) x f xs,
      boolean_realize_bounded_formula_eq' (v₁ := v₂) x f xs]
  let φ₁ := fun k => if h : k < n then v₁.nth k h else x
  let φ₂ := fun k => if h : k < n then v₂.nth k h else x
  have key := boolean_realize_formula_congr φ₁ φ₂ f.fst xs
  refine le_trans ?_ key
  apply inf_le_inf_right
  rw [le_iInf_iff]
  intro k
  by_cases hk : k < n
  · simp only [φ₁, φ₂, dif_pos hk]
    exact iInf_le _ (⟨k, hk⟩ : Fin n)
  · simp only [φ₁, φ₂, dif_neg hk, S.eq_refl]
    exact le_top

/-! ## boolean_realize_bounded_formula_irrel' — src/bfol.lean:513-528 -/

lemma boolean_realize_bounded_formula_irrel' {n n'} {v₁ : DVec S n} {v₂ : DVec S n'}
    (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
    {l} (f : bounded_preformula L n l) (f' : bounded_preformula L n' l)
    (hf : f.fst = f'.fst) (xs : DVec S l) :
    boolean_realize_bounded_formula v₁ f xs = boolean_realize_bounded_formula v₂ f' xs := by
  induction f generalizing n' with
  | bd_falsum =>
    cases f' with
    | bd_falsum => rfl
    | _ => simp [bounded_preformula.fst] at hf
  | bd_equal t₁ t₂ =>
    cases f' with
    | bd_equal t₁' t₂' =>
      simp only [bounded_preformula.fst, preformula.equal.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_term_irrel' h t₁ t₁' hf.1,
          boolean_realize_bounded_term_irrel' h t₂ t₂' hf.2]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_rel R =>
    cases f' with
    | bd_rel R' =>
      simp only [bounded_preformula.fst, preformula.rel.injEq] at hf
      simp [boolean_realize_bounded_formula, hf]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_apprel f t ihf =>
    cases f' with
    | bd_apprel f' t' =>
      simp only [bounded_preformula.fst, preformula.apprel.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      rw [boolean_realize_bounded_term_irrel' h t t' hf.2,
          ihf h f' hf.1]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_imp f₁ f₂ ih₁ ih₂ =>
    cases f' with
    | bd_imp f₁' f₂' =>
      simp only [bounded_preformula.fst, preformula.imp.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      rw [ih₁ h f₁' hf.1, ih₂ h f₂' hf.2]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_all f ih =>
    cases f' with
    | bd_all f' =>
      simp only [bounded_preformula.fst, preformula.all.injEq] at hf
      simp only [boolean_realize_bounded_formula]
      congr 1; ext x
      apply ih
      · intro m hm hm'
        cases m with
        | zero => rfl
        | succ m => exact h m (Nat.lt_of_succ_lt_succ hm) (Nat.lt_of_succ_lt_succ hm')
      · exact hf
    | _ => simp [bounded_preformula.fst] at hf

/-! ## boolean_realize_bounded_formula_cast_eq_irrel — src/bfol.lean:536-538 -/

/-! ## basic simp lemmas for boolean_realize_sentence — src/bfol.lean:543-559 -/

@[simp] lemma boolean_realize_sentence_all {f : bounded_formula L 1} :
    ⟦bd_all f⟧[S] = ⨅ x : S, boolean_realize_bounded_formula (DVec.cons x DVec.nil) f DVec.nil :=
  rfl

@[simp] lemma boolean_realize_bounded_formula_not {n} {v : DVec S n}
    {f : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_not f) DVec.nil =
    (boolean_realize_bounded_formula v f DVec.nil)ᶜ := by
  simp [bd_not, imp]

@[simp] lemma boolean_realize_bounded_formula_or {n} {v : DVec S n}
    {f g : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_or f g) DVec.nil =
    boolean_realize_bounded_formula v f DVec.nil ⊔
    boolean_realize_bounded_formula v g DVec.nil := by
  simp [bd_or, bd_not, imp]

@[simp] lemma boolean_realize_bounded_formula_and {n} {v : DVec S n}
    {f g : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_and f g) DVec.nil =
    boolean_realize_bounded_formula v f DVec.nil ⊓
    boolean_realize_bounded_formula v g DVec.nil := by
  simp [bd_and, bd_not, bd_or, imp]

@[simp] lemma boolean_realize_bounded_formula_ex {n} {v : DVec S n}
    {f : bounded_formula L (n + 1)} :
    boolean_realize_bounded_formula v (bd_ex f) DVec.nil =
    ⨆ x : S, boolean_realize_bounded_formula (DVec.cons x v) f DVec.nil := by
  simp [bd_ex, bd_not, bd_all, imp, compl_iInf]

@[simp] lemma boolean_realize_bounded_formula_biimp {n} {v : DVec S n}
    {f g : bounded_formula L n} :
    boolean_realize_bounded_formula v (bd_biimp f g) DVec.nil =
    bihimp (boolean_realize_bounded_formula v f DVec.nil)
           (boolean_realize_bounded_formula v g DVec.nil) := by
  simp only [bd_biimp, boolean_realize_bounded_formula_and, boolean_realize_bounded_formula,
             bihimp, himp_eq, sup_comm, inf_comm, imp]

/-! ## boolean_realize_bounded_formula_bd_apps_rel — src/bfol.lean:596-602 -/

/-! ## boolean_realize_cast_bounded_formula — src/bfol.lean:604-619 -/

@[simp] lemma boolean_realize_cast_bounded_formula {n m} {h : n ≤ m}
    {f : bounded_formula L n} {v : DVec S m} :
    boolean_realize_bounded_formula v (f.cast h) DVec.nil =
    boolean_realize_bounded_formula (v.trunc n h) f DVec.nil := by
  by_cases hn : n = m
  · subst hn; simp
  · have hlt : n < m := Nat.lt_of_le_of_ne h hn
    apply boolean_realize_bounded_formula_irrel'
    · intro k hk _; simp [DVec.trunc_nth]
    · simp [bounded_preformula.cast]

/-! ## boolean_realize_sentence_bd_apps_rel — src/bfol.lean:621-634 -/

lemma boolean_realize_sentence_eq (v : ℕ → S) (f : sentence L) :
    boolean_realize_formula v f.fst DVec.nil = ⟦f⟧[S] :=
  boolean_realize_bounded_formula_eq
    (fun k hk => absurd hk (Nat.not_lt_zero k)) f DVec.nil

/-! ## forced_in, all_forced_in — src/bfol.lean:647-658 -/

def forced_in (x : β) (S : bStructure L β) (f : sentence L) : Prop :=
  x ≤ ⟦f⟧[S]

scoped notation:52 x " ⊩[" S "] " f => Fol.forced_in x S f

def all_forced_in (x : β) (S : bStructure L β) (T : SentTheory L) : Prop :=
  x ≤ ⨅ f ∈ T, ⟦f⟧[S]

scoped notation:52 x " ⊩ₜ[" S "] " T => Fol.all_forced_in x S T

/-! ## forced — src/bfol.lean:674-677 -/

variable (β) in
def forced (T : SentTheory L) (f : sentence L) : Prop :=
  ∀ {{S : bStructure L β}}, Nonempty S → (⨅ g ∈ T, ⟦g⟧[S]) ⊩[S] f

scoped notation:51 T " ⊨[" β "] " f => Fol.forced β T f

/-! ## bsatisfied_of_forced, forced_of_bsatisfied — src/bfol.lean:680-698 -/

def forced_of_bsatisfied {T : SentTheory L} {f : sentence L}
    (H : T.fst ⊨ᵤ[β] f.fst) : T ⊨[β] f := by
  intro S hS
  obtain ⟨s⟩ := hS
  show (⨅ g ∈ T, ⟦g⟧[S]) ≤ ⟦f⟧[S]
  rw [← boolean_realize_sentence_eq (fun _ => s)]
  refine le_trans ?_ (H S (fun _ => s))
  rw [le_iInf_iff]
  intro f'
  rw [le_iInf_iff]
  intro hf'
  rcases hf' with ⟨f'', ⟨hf'', rfl⟩⟩
  rw [boolean_realize_sentence_eq]
  exact le_trans (iInf_le _ f'') (iInf_le _ hf'')

/-! ## bModel — src/bfol.lean:720-721 -/

/-! ## boolean_soundness, unprovable_of_model_neg — src/bfol.lean:730-739 -/

theorem boolean_soundness {T : SentTheory L} {A : sentence L} (H : T ⊢ₛ' A) :
    T ⊨[β] A :=
  forced_of_bsatisfied (boolean_formula_soundness (β := β) (Classical.choice H))

/-! ## boolean_realize_subst_preterm — src/bfol.lean:741-761 -/

/-! ## boolean_realize_sentence_bd_alls — src/bfol.lean:763-778 -/

lemma boolean_realize_sentence_bd_alls {n} {f : bounded_formula L n} :
    boolean_realize_sentence S (bd_alls n f) =
    ⨅ xs : DVec S n, boolean_realize_bounded_formula xs f DVec.nil := by
  induction n with
  | zero =>
    simp only [bd_alls, boolean_realize_sentence]
    apply le_antisymm
    · rw [le_iInf_iff]
      intro xs
      cases xs
      rfl
    · exact iInf_le _ DVec.nil
  | succ n ih =>
    rw [bd_alls, ih]
    apply le_antisymm
    · rw [le_iInf_iff]
      intro xs
      cases xs with
      | cons x xs =>
        refine le_trans (iInf_le _ xs) ?_
        exact iInf_le _ x
    · rw [le_iInf_iff]
      intro xs
      simp only [boolean_realize_bounded_formula, le_iInf_iff]
      intro x
      exact iInf_le _ (DVec.cons x xs)

/-! ## consis_of_exists_bmodel — src/bfol.lean:785-793 -/

/-! ## subst0_bounded_formula_not — src/bfol.lean:799-801 -/

/-! ## subst0_bounded_formula_and — src/bfol.lean:803-805 -/

/-! ## boolean_realize_bounded_formula_insert_lift — src/bfol.lean:854-872 -/

lemma boolean_realize_bounded_formula_insert_lift {n l} (v : DVec S n) (x : S) (m : ℕ) (hm : m ≤ n)
    (f : bounded_preformula L n l) (xs : DVec S l) :
    boolean_realize_bounded_formula (v.insert x m) (f ↑ᶠᵇ' 1 # m) xs =
    boolean_realize_bounded_formula v f xs := by
  -- Reduce to unbounded formula semantics
  rw [boolean_realize_bounded_formula_eq' (v₁ := v.insert x m) x,
      boolean_realize_bounded_formula_eq' (v₁ := v) x]
  simp only [lift_bounded_formula_fst]
  -- Now use boolean_realize_formula_subst_lift
  rw [show (fun k => if h : k < n + 1 then (v.insert x m).nth k h else x) =
          subst_realize (fun k => if h : k < n then v.nth k h else x) x m from by
        funext k
        simp only [subst_realize]
        by_cases hkm : k < m
        · simp only [hkm, if_true]
          have hkn : k < n := Nat.lt_of_lt_of_le hkm hm
          have hkn1 : k < n + 1 := Nat.lt_succ_of_le (Nat.le_of_lt hkn)
          simp only [dif_pos hkn1, dif_pos hkn]
          simp [DVec.insert_nth_lt x v (by exact hkn) hkn1 (by exact hkm)]
        · by_cases hkm' : k = m
          · subst hkm'
            simp [hkm, DVec.insert_nth]
          · have hkm2 : m < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hkm) (Ne.symm hkm')
            simp only [Nat.lt_asymm hkm2, hkm2, if_false, if_true]
            by_cases hkn1 : k < n + 1
            · have hk1 : k - 1 < n := by omega
              simp only [dif_pos hkn1, dif_pos hk1]
              rw [DVec.insert_nth_gt_simp x v hkn1 hkm2]
            · have hk1 : ¬(k - 1 < n) := by omega
              simp only [dif_neg hkn1, dif_neg hk1]]
  exact boolean_realize_formula_subst_lift _ _ _ _ _

/-! ## boolean_realize_formula_insert_lift2 — src/bfol.lean:874-879 -/

@[simp] lemma boolean_realize_formula_insert_lift2 {n} (v : DVec S n) (x y z : S)
    (f : bounded_formula L (n + 2)) :
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y (DVec.cons z v)))
      (f ↑ᶠᵇ' 1 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) f DVec.nil := by
  -- Use boolean_realize_bounded_formula_insert_lift with m=2, v=(x::y::v), x=z
  convert boolean_realize_bounded_formula_insert_lift (DVec.cons x (DVec.cons y v)) z 2
    (by omega) f DVec.nil using 2
  rfl

/-! ## boolean_realize_subst_formula0 — src/bfol.lean:881-897 -/

lemma boolean_realize_subst_formula0 {n} (S : bStructure L β) [Nonempty S]
    (f : bounded_formula L (n + 1)) (t : bounded_term L n) (v : DVec S n) :
    boolean_realize_bounded_formula v (subst0_bounded_formula f t) DVec.nil =
    boolean_realize_bounded_formula
      (DVec.cons (boolean_realize_bounded_term v t DVec.nil) v) f DVec.nil := by
  obtain ⟨y⟩ := ‹Nonempty S›
  -- Reduce both sides to formula semantics via bounded_formula_eq'
  rw [boolean_realize_bounded_formula_eq' (v₁ := v) y,
      boolean_realize_bounded_formula_eq' (v₁ := DVec.cons _ v) y]
  simp only [subst0_bounded_formula_fst]
  -- LHS: boolean_realize_formula (fun k => if h : k < n then v.nth k h else y) (f.fst[t.fst//0]) []
  -- RHS: boolean_realize_formula (fun k => if h : k < n+1 then (brt_v_t :: v).nth k h else y) f.fst []
  -- Use ← boolean_realize_formula_subst0 on LHS:
  -- = boolean_realize_formula (subst_realize φ (brt_v φ t.fst []) 0) f.fst []
  -- where φ = (fun k => if h : k < n then v.nth k h else y)
  -- and brt_v φ t.fst [] = boolean_realize_bounded_term_eq' ... = brt v t []
  rw [← boolean_realize_formula_subst0]
  -- Now LHS = boolean_realize_formula (subst_realize φ (brt φ t.fst []) 0) f.fst []
  -- RHS = boolean_realize_formula (fun k => if h : k < n+1 then (brt_v_t :: v).nth k h else y) f.fst []
  apply boolean_realize_formula_congr'
  intro k
  simp only [subst_realize, boolean_realize_term, DVec.nth]
  -- The bounded term realization
  rw [← boolean_realize_bounded_term_eq' (v₁ := v) y t DVec.nil]
  by_cases hk : k < n + 1
  · simp only [dif_pos hk, DVec.nth]
    cases k with
    | zero => simp [subst_realize, boolean_realize_bounded_term]
    | succ k =>
      have h2k : k < n := Nat.lt_of_succ_lt_succ hk
      simp only [subst_realize, Nat.zero_lt_succ, if_false, Nat.lt_irrefl, if_false]
      simp [dif_pos h2k, DVec.nth]
  · simp only [dif_neg hk, subst_realize]
    have h2k : 0 < k := Nat.pos_of_ne_zero (by omega)
    have h3k : ¬(k - 1 < n) := by omega
    simp [Nat.not_lt.mp hk, h2k, h3k, dif_neg h3k]

end bfol

end Fol
