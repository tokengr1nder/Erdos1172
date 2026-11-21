/-
Local extraction and Lean 4.33.1 proof-compatibility changes for E1172, 2026-09-19.
Original definitions and theorem statements through ZFC_consistent are preserved.
See ../PROVENANCE.md for the pinned source and exact extraction boundary.
-/
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/zfc.lean (552 lines) — Task 22 -/
module

public import Erdos1172.Statement
public import Flypitch4.Bfol
public import Flypitch4.BvmExtras2

@[expose] public section

open Fol bSet

universe u

-- ============================================================
-- The language of ZFC (src/zfc.lean:32-46)
-- ============================================================

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

/-- Interpret L_ZFC function symbols in bSet β. -/
def bSet_model_fun_map : ∀ {n : ℕ}, L_ZFC.functions n → DVec (bSet β) n → bSet β
  | _, ZFC_func.emptyset, _  => bSet.empty
  | _, ZFC_func.pr, DVec.cons x (DVec.cons y DVec.nil) => pair x y
  | _, ZFC_func.ω, _ => bSet.omega
  | _, ZFC_func.P, DVec.cons x DVec.nil => bv_powerset x
  | _, ZFC_func.Union, DVec.cons x DVec.nil => bv_union x

/-- Interpret L_ZFC relation symbols in bSet β. -/
def bSet_model_rel_map : ∀ {n : ℕ}, L_ZFC.relations n → DVec (bSet β) n → β
  | _, ZFC_rel.ε, DVec.cons x (DVec.cons y DVec.nil) => x ∈ᴮ y

variable (β)

/-- The Boolean-valued model V(β) of ZFC. -/
noncomputable def V : bStructure L_ZFC β :=
  { carrier   := bSet β
    fun_map   := bSet_model_fun_map
    rel_map   := bSet_model_rel_map
    eq        := (· =ᴮ ·)
    eq_refl   := fun x => bv_eq_refl x
    eq_symm   := fun x y => bv_eq_symm
    eq_trans  := fun y => bv_eq_trans
    fun_congr := by
      intro n F
      cases F with
      | emptyset =>
        intro x y
        cases x; cases y
        simp [bSet_model_fun_map, DVec.map2, DVec.fInf]
      | ω =>
        intro x y
        cases x; cases y
        simp [bSet_model_fun_map, DVec.map2, DVec.fInf]
      | P =>
        intro x y
        match x, y with
        | DVec.cons a DVec.nil, DVec.cons b DVec.nil =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact bv_powerset_congr le_rfl
      | Union =>
        intro x y
        match x, y with
        | DVec.cons a DVec.nil, DVec.cons b DVec.nil =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact bv_union_congr le_rfl
      | pr =>
        intro x y
        match x, y with
        | DVec.cons a (DVec.cons b DVec.nil), DVec.cons c (DVec.cons d DVec.nil) =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact pair_congr inf_le_left inf_le_right
    rel_congr := by
      intro n R
      cases R with
      | ε =>
        intro x y
        match x, y with
        | DVec.cons a (DVec.cons b DVec.nil), DVec.cons c (DVec.cons d DVec.nil) =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_rel_map]
          -- goal: a =ᴮ c ⊓ b =ᴮ d ⊓ a ∈ᴮ b ≤ c ∈ᴮ d
          exact mem_congr (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right
  }

@[simp] lemma V_forall {C : (V β) → β} : (⨅ (x : V β), C x) = ⨅ (x : bSet β), C x := rfl
@[simp] lemma V_exists {C : (V β) → β} : (⨆ (x : V β), C x) = ⨆ (x : bSet β), C x := rfl
@[simp] lemma V_eq {a b : V β} : (V β).eq a b = a =ᴮ b := rfl

instance V_β_nonempty : Nonempty (V β) := ⟨bSet.empty⟩

variable {β}

-- ============================================================
-- Bounded terms/formulas for L_ZFC (src/zfc.lean:115-140)
-- ============================================================

@[simp] lemma boolean_realize_bounded_formula_mem' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (mem' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ∈ᴮ
    boolean_realize_bounded_term v t₂ DVec.nil := by
  rfl

@[simp] lemma boolean_realize_bounded_term_Union' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (⋃' t) DVec.nil =
    bv_union (boolean_realize_bounded_term v t DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_term_Powerset' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (P' t) DVec.nil =
    bv_powerset (boolean_realize_bounded_term v t DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_term_omega' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ω' DVec.nil = bSet.omega := by
  rfl

@[simp] lemma boolean_realize_bounded_term_emptyset' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ∅' DVec.nil = bSet.empty := by
  rfl

@[simp] lemma boolean_realize_bounded_term_pair' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (pair' t₁ t₂) DVec.nil =
    pair (boolean_realize_bounded_term v t₁ DVec.nil)
         (boolean_realize_bounded_term v t₂ DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_formula_subset' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (subset'' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ⊆ᴮ boolean_realize_bounded_term v t₂ DVec.nil := by
  simp only [subset'', boolean_realize_bounded_formula,
             
             V_forall]
  rw [subset_unfold'
    (x := boolean_realize_bounded_term (S := V β) v t₁ DVec.nil)
    (u := boolean_realize_bounded_term (S := V β) v t₂ DVec.nil)]
  apply iInf_congr
  intro x
  change _root_.imp
    (x ∈ᴮ boolean_realize_bounded_term (S := V β) (DVec.cons x v)
      (t₁ ↑ᵇ' 1 # 0) DVec.nil)
    (x ∈ᴮ boolean_realize_bounded_term (S := V β) (DVec.cons x v)
      (t₂ ↑ᵇ' 1 # 0) DVec.nil) = _
  rw [boolean_realize_bounded_term_subst_lift (S := V β) v x t₁ DVec.nil,
    boolean_realize_bounded_term_subst_lift (S := V β) v x t₂ DVec.nil]

-- ============================================================
-- Ordinal predicates (src/zfc.lean:307-327)
-- ============================================================

@[simp] lemma Ord_f_is_Ord {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) Ord_f DVec.nil = Ord x := by
  simp only [Ord_f, ewo_f, epsilon_trichotomy_f, epsilon_well_founded_f, is_transitive_f,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_or,
             boolean_realize_bounded_formula_ex, 
             
             boolean_realize_bounded_term_emptyset' (β := β),
             boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq]
  unfold bSet.Ord epsilon_well_orders epsilon_trichotomy epsilon_well_founded is_transitive
  change
    (epsilon_trichotomy x ⊓
      ⨅ a : bSet β, _root_.imp (⨅ w : bSet β, _root_.imp (w ∈ᴮ a) (w ∈ᴮ x))
        (_root_.imp (a =ᴮ ∅)ᶜ
          (⨆ y : bSet β, y ∈ᴮ a ⊓ ⨅ z : bSet β, _root_.imp (z ∈ᴮ a) (z ∈ᴮ y)ᶜ))) ⊓
      (⨅ y : bSet β, _root_.imp (y ∈ᴮ x)
        (⨅ w : bSet β, _root_.imp (w ∈ᴮ y) (w ∈ᴮ x))) = _
  apply congrArg₂ (fun a b : β => a ⊓ b)
  · apply congrArg₂ (fun a b : β => a ⊓ b)
    · rfl
    · apply iInf_congr
      intro a
      exact congrArg
        (fun q : β => _root_.imp q
          (_root_.imp (a =ᴮ ∅)ᶜ
            (⨆ y : bSet β, y ∈ᴮ a ⊓ ⨅ z : bSet β, _root_.imp (z ∈ᴮ a) (z ∈ᴮ y)ᶜ)))
        (subset_unfold' (x := a) (u := x)).symm
  · apply iInf_congr
    intro y
    exact congrArg (_root_.imp (y ∈ᴮ x)) (subset_unfold' (x := y) (u := x)).symm

-- ============================================================
-- The ZFC axioms as sentences (src/zfc.lean:179-382)
-- ============================================================

-- axiom of emptyset: ∀ x, x ∉ ∅
lemma bSet_models_emptyset : ⊤ ⊩[V β] axiom_of_emptyset := by
  change ⊤ ≤ _
  simp only [axiom_of_emptyset, boolean_realize_sentence_all,
             boolean_realize_bounded_formula_not, 
             boolean_realize_bounded_term_emptyset' (β := β)]
  exact le_iInf (fun x => empty_spec)

-- axiom of ordered pairs: ∀ x y z w, pair(x,y) = pair(z,w) ↔ x=z ∧ y=w
lemma bSet_models_ordered_pairs : ⊤ ⊩[V β] axiom_of_ordered_pairs := by
  change ⊤ ≤ _
  simp only [axiom_of_ordered_pairs, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_term,
             DVec.nth, V_eq, V_forall]
  apply le_iInf; intro a; apply le_iInf; intro b; apply le_iInf; intro x; apply le_iInf; intro y
  change ⊤ ≤ bihimp (pair a b =ᴮ pair x y) (a =ᴮ x ⊓ b =ᴮ y)
  -- goal: ⊤ ≤ bihimp (pair a b =ᴮ pair x y) (a =ᴮ x ⊓ b =ᴮ y)
  have heq : pair a b =ᴮ pair x y = a =ᴮ x ⊓ b =ᴮ y :=
    le_antisymm (le_inf eq_of_eq_pair_left eq_of_eq_pair_right)
                (pair_congr inf_le_left inf_le_right)
  rw [heq]
  -- Need: ⊤ ≤ bihimp (a =ᴮ x ⊓ b =ᴮ y) (a =ᴮ x ⊓ b =ᴮ y)
  rw [bihimp_self]

-- axiom of extensionality: ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y
lemma bSet_models_extensionality : ⊤ ⊩[V β] axiom_of_extensionality := by
  change ⊤ ≤ _
  simp only [axiom_of_extensionality, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, 
             boolean_realize_bounded_term, DVec.nth, V_forall, V_eq]
  apply le_iInf; intro x; apply le_iInf; intro y
  change ⊤ ≤ _root_.imp (⨅ z : bSet β, bihimp (z ∈ᴮ x) (z ∈ᴮ y)) (x =ᴮ y)
  -- goal: ⊤ ≤ (⨅ z, bihimp (z ∈ x) (z ∈ y)) ⟹ (x =ᴮ y)
  rw [← _root_.deduction]
  -- goal: ⊤ ⊓ (⨅ z, bihimp (z ∈ x) (z ∈ y)) ≤ x =ᴮ y
  rw [top_inf_eq]
  -- goal: ⨅ z, bihimp (z ∈ x) (z ∈ y) ≤ x =ᴮ y
  apply le_trans ?_ (bSet_axiom_of_extensionality x y)
  apply le_iInf; intro z
  apply le_trans (iInf_le _ z)
  -- bihimp A B = (B ⇨ A) ⊓ (A ⇨ B); imp A B = Aᶜ ⊔ B; himp_eq: A ⇨ B = B ⊔ Aᶜ
  apply le_inf
  · exact le_trans inf_le_right (by simp [himp_eq, imp, sup_comm])
  · exact le_trans inf_le_left (by simp [himp_eq, imp, sup_comm])

-- axiom schema of strong collection (src/zfc.lean:208-211)
lemma lift2_helper {n l} (f : bounded_preformula L_ZFC n l) {k} (m : ℕ) :
    (f ↑ᶠᵇ' (k + 2) # m).fst = ((f ↑ᶠᵇ' (k + 1) # m) ↑ᶠᵇ' 1 # m).fst := by
  simp only [lift_bounded_formula_fst]
  rw [lift_formula_at2_medium] <;> omega

lemma B_ext_left_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 1))
    (xs : DVec (V β) n) (x y : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons x xs) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons y xs) ϕ DVec.nil := by
  -- Key: x =ᴮ y = ⨅ m : Fin (n+1), (V β).eq ((x::xs)[m]) ((y::xs)[m])
  -- At m=0: eq(x,y) = x =ᴮ y; at m=succ k: eq(xs[k], xs[k]) = ⊤
  have hkey : x =ᴮ y = ⨅ (m : Fin (n + 1)),
      (V β).eq ((DVec.cons x xs).nth m.1 m.2) ((DVec.cons y xs).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf; intro ⟨m, hm⟩
      simp only [V_eq]
      cases m with
      | zero => simp [DVec.nth]
      | succ k =>
        show x =ᴮ y ≤ xs.nth k (Nat.lt_of_succ_lt_succ hm) =ᴮ xs.nth k (Nat.lt_of_succ_lt_succ hm)
        rw [bv_eq_refl (xs.nth k (Nat.lt_of_succ_lt_succ hm))]
        exact le_top
    · exact iInf_le _ (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  rw [hkey]
  exact boolean_realize_bounded_formula_congr (inferInstance : Nonempty (V β)) _ _ ϕ DVec.nil
lemma B_ext_right_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 2))
    (xs : DVec (V β) n) (x y z : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons z (DVec.cons x xs)) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons z (DVec.cons y xs)) ϕ DVec.nil := by
  -- Key: x =ᴮ y = ⨅ m : Fin (n+2), eq((z::x::xs)[m], (z::y::xs)[m])
  -- At m=0: eq(z,z)=⊤; at m=1: eq(x,y)=x=ᴮy; at m=succ(succ k): eq(xs[k],xs[k])=⊤
  have hkey : x =ᴮ y = ⨅ (m : Fin (n + 2)),
      (V β).eq ((DVec.cons z (DVec.cons x xs)).nth m.1 m.2)
               ((DVec.cons z (DVec.cons y xs)).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf; intro ⟨m, hm⟩
      simp only [V_eq]
      cases m with
      | zero =>
        show x =ᴮ y ≤ z =ᴮ z
        rw [bv_eq_refl (𝔹 := β) z]
        exact le_top
      | succ k =>
        cases k with
        | zero => simp [DVec.nth]
        | succ k' =>
          show x =ᴮ y ≤ xs.nth k' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm)) =ᴮ
               xs.nth k' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm))
          rw [bv_eq_refl (xs.nth k'
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm)))]
          exact le_top
    · exact iInf_le _ (⟨1, by omega⟩ : Fin (n + 2))
  rw [hkey]
  exact boolean_realize_bounded_formula_congr (inferInstance : Nonempty (V β)) _ _ ϕ DVec.nil
private lemma realize_lift2_at2 {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec (V β) n) (x y z₁ z₂ : V β) :
    boolean_realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ v)))) (ϕ ↑ᶠᵇ' 2 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper ϕ (k := 0) 2)]
  rw [boolean_realize_formula_insert_lift2 (DVec.cons z₂ v) x y z₁ (ϕ ↑ᶠᵇ' 1 # 2)]
  exact boolean_realize_formula_insert_lift2 v x y z₂ ϕ

private lemma realize_lift3_at2 {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec (V β) n) (x y z₁ z₂ z₃ : V β) :
    boolean_realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ (DVec.cons z₃ v))))) (ϕ ↑ᶠᵇ' 3 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper ϕ (k := 1) 2)]
  rw [boolean_realize_formula_insert_lift2 (DVec.cons z₂ (DVec.cons z₃ v)) x y z₁ (ϕ ↑ᶠᵇ' 2 # 2)]
  exact realize_lift2_at2 ϕ v x y z₂ z₃

lemma bSet_models_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) :
    ⊤ ⊩[V β] axiom_of_collection ϕ := by
  change ⊤ ≤ _
  simp only [axiom_of_collection, boolean_realize_sentence_bd_alls]
  apply le_iInf
  intro xs
  match xs with
  | DVec.cons u xs' =>
    simp only [boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
               boolean_realize_bounded_formula_ex, 
               DVec.nth, V_forall, V_exists, V_eq,
               boolean_realize_formula_insert_lift2 (S := V β), realize_lift2_at2 (β := β),
               boolean_realize_subst_formula0 (S := V β)]
    have hsubst (v' w' w : bSet β) :
        boolean_realize_bounded_formula (S := V β)
          (DVec.cons w (DVec.cons w' (DVec.cons v' (DVec.cons u xs'))))
          (subst0_bounded_formula (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, by omega⟩)) DVec.nil =
        boolean_realize_bounded_formula (S := V β) (DVec.cons w' (DVec.cons w xs')) ϕ DVec.nil := by
      rw [boolean_realize_subst_formula0 (V β) (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, by omega⟩)
        (DVec.cons w (DVec.cons w' (DVec.cons v' (DVec.cons u xs'))))]
      exact realize_lift3_at2 (β := β) ϕ xs' w' w w' v' u
    -- After simp, goal should be `⊤ ≤ realize (cons u xs') (imp ... (∃ ...))`
    -- with the formula bodies being  ϕ.eval at appropriate env
    -- ψ a b := boolean_realize (b :: a :: xs') ϕ  matches the role of ϕ in bSet_axiom_of_collection
    have hcoll := bSet_axiom_of_collection
        (fun a b : bSet β =>
          boolean_realize_bounded_formula (DVec.cons b (DVec.cons a xs')) ϕ DVec.nil)
        (fun x y z => by
          -- need: x =ᴮ y ⊓ realize (x :: z :: xs') ϕ ≤ realize (y :: z :: xs') ϕ
          -- (ψ z x → ψ z y means varying position 0 of cons-cons)
          exact B_ext_left_realize_bounded_formula ϕ (DVec.cons z xs') x y)
        (fun x y z => by
          -- need: x =ᴮ y ⊓ realize (z :: x :: xs') ϕ ≤ realize (z :: y :: xs') ϕ
          exact B_ext_right_realize_bounded_formula ϕ xs' x y z)
    have hu := hcoll.trans (iInf_le _ u)
    change ⊤ ≤ _root_.imp
      (⨅ x : bSet β, _root_.imp (x ∈ᴮ u)
        (⨆ y : bSet β,
          boolean_realize_bounded_formula (S := V β) (DVec.cons y (DVec.cons x xs')) ϕ DVec.nil))
      (⨆ v' : bSet β,
        (⨅ w : bSet β, _root_.imp (w ∈ᴮ u)
          (⨆ w' : bSet β, w' ∈ᴮ v' ⊓
            boolean_realize_bounded_formula (S := V β)
              (DVec.cons w' (DVec.cons w xs')) ϕ DVec.nil)) ⊓
        (⨅ w' : bSet β, _root_.imp (w' ∈ᴮ v')
          (⨆ w : bSet β, w ∈ᴮ u ⊓
            boolean_realize_bounded_formula (S := V β)
              (DVec.cons w (DVec.cons w' (DVec.cons v' (DVec.cons u xs'))))
              (subst0_bounded_formula (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, by omega⟩)) DVec.nil)))
    simpa only [hsubst] using hu
-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y
lemma bSet_models_union : ⊤ ⊩[V β] axiom_of_union := by
  change ⊤ ≤ _
  simp only [axiom_of_union, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, 
             boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists]
  apply le_iInf; intro u; apply le_iInf; intro x
  change ⊤ ≤ bihimp (x ∈ᴮ bv_union u) (⨆ y : bSet β, y ∈ᴮ u ⊓ x ∈ᴮ y)
  -- goal: ⊤ ≤ bihimp (x ∈ bv_union u) (⨆ y, y ∈ u ⊓ x ∈ y)
  have heq : x ∈ᴮ bv_union u = ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y :=
    le_antisymm ((bv_union_spec_split u (Γ := x ∈ᴮ bv_union u) x).mp le_rfl)
                ((bv_union_spec_split u (Γ := ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) x).mpr le_rfl)
  rw [heq, bihimp_self]
-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z
lemma bSet_models_powerset : ⊤ ⊩[V β] axiom_of_powerset := by
  change ⊤ ≤ _
  simp only [axiom_of_powerset, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, 
             boolean_realize_bounded_term, DVec.nth,
             V_forall]
  apply le_iInf; intro z; apply le_iInf; intro y
  change ⊤ ≤ bihimp (y ∈ᴮ bv_powerset z) (⨅ x : bSet β, _root_.imp (x ∈ᴮ y) (x ∈ᴮ z))
  -- goal: ⊤ ≤ bihimp (y ∈ bv_powerset z) (⨅ x, x ∈ y ⟹ x ∈ z)
  rw [← subset_unfold' (x := y) (u := z)]
  -- goal: ⊤ ≤ bihimp (y ∈ bv_powerset z) (y ⊆ z)
  have heq : y ∈ᴮ bv_powerset z = y ⊆ᴮ z :=
    le_antisymm (bv_powerset_spec.mpr le_rfl) (bv_powerset_spec.mp le_rfl)
  rw [heq, bihimp_self]
-- axiom of infinity (src/zfc.lean:332-347)
lemma bSet_models_infinity : ⊤ ⊩[V β] axiom_of_infinity := by
  change ⊤ ≤ _
  simp only [axiom_of_infinity, 
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, 
             boolean_realize_bounded_formula_mem' (β := β),
             
             boolean_realize_bounded_term_emptyset' (β := β),
             boolean_realize_bounded_term_omega' (β := β),
             boolean_realize_bounded_term, DVec.nth, Ord_f_is_Ord (β := β),
             V_forall, V_exists]
  change ⊤ ≤
    (((∅ : bSet β) ∈ᴮ bSet.omega ⊓
      ⨅ x : bSet β, _root_.imp (x ∈ᴮ bSet.omega)
        (⨆ y : bSet β, y ∈ᴮ bSet.omega ⊓ x ∈ᴮ y)) ⊓
      (⨆ α : bSet β, Ord α ⊓ bSet.omega =ᴮ α)) ⊓
    (⨅ α : bSet β, _root_.imp (Ord α)
      (_root_.imp
        ((∅ : bSet β) ∈ᴮ α ⊓ ⨅ x : bSet β,
          _root_.imp (x ∈ᴮ α) (⨆ y : bSet β, y ∈ᴮ α ⊓ x ∈ᴮ y))
        (⨅ w : bSet β, _root_.imp (w ∈ᴮ bSet.omega) (w ∈ᴮ α))))
  simp only [← subset_unfold' (𝔹 := β)]
  -- Goal: ⊤ ≤ ((∅ ∈ᴮ ω ⊓ ⨅ x, x ∈ᴮ ω ⟹ ⨆ y, y ∈ᴮ ω ⊓ x ∈ᴮ y) ⊓
  --            (⨆ α, Ord α ⊓ ω =ᴮ α)) ⊓
  --           (⨅ α, Ord α ⟹ ((∅ ∈ᴮ α ⊓ ⨅ x, x ∈ᴮ α ⟹ ⨆ y, y ∈ᴮ α ⊓ x ∈ᴮ y) ⟹ ω ⊆ α))
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · -- ∅ ∈ᴮ ω
    exact le_trans bSet_axiom_of_infinity' inf_le_left
  · -- ⨅ x, x ∈ᴮ ω ⟹ ⨆ y, y ∈ᴮ ω ⊓ x ∈ᴮ y
    exact le_trans bSet_axiom_of_infinity' inf_le_right
  · -- ⨆ α, Ord α ⊓ ω =ᴮ α
    apply le_iSup_of_le bSet.omega
    exact le_inf (Ord_omega (𝔹 := β)) (bv_eq_refl (𝔹 := β) bSet.omega).symm.le
  · -- ⨅ α, Ord α ⟹ (is_limit α ⟹ ω ⊆ α)
    -- This is omega_least_is_limit
    -- is_limit α = ∅ ∈ᴮ α ⊓ ⨅ x, x ∈ᴮ α ⟹ ⨆ y, y ∈ᴮ α ⊓ x ∈ᴮ y
    -- The goal matches omega_least_is_limit directly
    exact omega_least_is_limit (𝔹 := β) (Γ := ⊤)
-- axiom of regularity: ∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y
lemma bSet_models_regularity : ⊤ ⊩[V β] axiom_of_regularity := by
  change ⊤ ≤ _
  simp only [axiom_of_regularity, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             
             boolean_realize_bounded_term_emptyset' (β := β),
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_formula_and, boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists]
  apply le_iInf; intro x
  rw [← _root_.deduction]
  -- goal: ⊤ ⊓ (x =ᴮ ∅)ᶜ ≤ ⨆ y, y ∈ x ⊓ (⨅ z, z ∈ x ⟹ (z ∈ y)ᶜ)
  rw [top_inf_eq]
  -- goal: (x =ᴮ ∅)ᶜ ≤ ⨆ y, y ∈ x ⊓ (⨅ z, z ∈ x ⟹ (z ∈ y)ᶜ)
  exact bSet_axiom_of_regularity x le_rfl
-- Zorn's lemma (src/zfc.lean:363-376)
lemma bSet_models_Zorn : ⊤ ⊩[V β] zorns_lemma := by
  change ⊤ ≤ _
  simp only [zorns_lemma, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_or,
             
             
             boolean_realize_bounded_term_emptyset' (β := β),
             
             boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq]
  change ⊤ ≤ ⨅ X : bSet β, _root_.imp (X =ᴮ ∅)ᶜ
    (_root_.imp (⨅ y : bSet β,
      _root_.imp ((⨅ a : bSet β, _root_.imp (a ∈ᴮ y) (a ∈ᴮ X)) ⊓
        ⨅ w₁ : bSet β, ⨅ w₂ : bSet β,
          _root_.imp (w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y)
            ((⨅ a : bSet β, _root_.imp (a ∈ᴮ w₁) (a ∈ᴮ w₂)) ⊔
              (⨅ a : bSet β, _root_.imp (a ∈ᴮ w₂) (a ∈ᴮ w₁)))) (bv_union y ∈ᴮ X))
      (⨆ c : bSet β, c ∈ᴮ X ⊓
        ⨅ z : bSet β, _root_.imp (z ∈ᴮ X)
          (_root_.imp (⨅ a : bSet β, _root_.imp (a ∈ᴮ c) (a ∈ᴮ z)) (c =ᴮ z))))
  simpa only [subset_unfold' (𝔹 := β)] using (bSet_zorns_lemma' (𝔹 := β) (Γ := ⊤))
-- ============================================================
-- The ZFC theory (src/zfc.lean:378-399)
-- ============================================================

/-- The fundamental theorem of forcing: bSet β models all of ZFC. -/
theorem bSet_models_ZFC : ⊤ ⊩ₜ[V β] ZFC := by
  simp only [all_forced_in]
  apply le_iInf; intro f; apply le_iInf; intro hf
  simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
             Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and] at hf
  rcases hf with (hf | ⟨n, ϕ, rfl⟩)
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bSet_models_emptyset
    · exact bSet_models_ordered_pairs
    · exact bSet_models_extensionality
    · exact bSet_models_union
    · exact bSet_models_powerset
    · exact bSet_models_infinity
    · exact bSet_models_regularity
    · exact bSet_models_Zorn
  · exact bSet_models_collection _

/- This core extraction retains the source ZFC theory and all its proofs.
It omits the subsequent functional-relation formulas and CH forcing endpoints.
Source: ianklatzco/flypitch, commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.
Compatibility work for Erdős 1172 does not assert any dense-ideal or GCH model. -/
