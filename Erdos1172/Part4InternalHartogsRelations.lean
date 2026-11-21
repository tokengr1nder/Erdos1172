/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in vendor/flypitch4/LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude

Extracted from Flypitch4/AlephOne.lean, with the final three
relation-faithfulness lemmas generalized to an arbitrary codomain.
-/
module

public import Flypitch4.BvmExtras2

@[expose] public section

/-!
# Internal relation codes for the Hartogs construction

The declarations are the concrete set/graph operations used by the upstream
internal omega-one construction. Relation faithfulness below does not assume
that the codomain is omega, an ordinal, nonempty, or a checked ground set.
The two source ordinals still require the original `exists_two` hypotheses:
an empty relation code alone does not distinguish zero from one.

This module deliberately does not import `Flypitch4.AlephOne`; the extracted
helper declarations keep their original names in the `bSet` namespace.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def mem_rel (x : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ᴮ x.func pr.2)

-- src/aleph_one.lean:268
lemma mem_mem_rel_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ pair y z ∈ᴮ mem_rel x ↔ (Γ ≤ y ∈ᴮ x ∧ Γ ≤ z ∈ᴮ x ∧ Γ ≤ y ∈ᴮ z) := by
  -- mem_rel x = subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ x.func pr.2)
  unfold mem_rel
  rw [mem_subset.mk_iff]
  simp only [prod_func]
  constructor
  · -- MP: Γ ≤ ⨆ (i,j), pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) → each conclusion
    intro H
    refine ⟨?_, ?_, ?_⟩
    · -- y ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y ∈ x
      have hyi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ y =ᴮ x.func i :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hbi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval i :=
        inf_le_right.trans (inf_le_right.trans inf_le_left)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ y =ᴮ x.func i ⊓ x.bval i := le_inf hyi hbi
        _ ≤ y ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le i
            exact le_inf inf_le_right inf_le_left
    · -- z ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      have hzj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ z =ᴮ x.func j :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hbj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval j :=
        inf_le_right.trans (inf_le_right.trans inf_le_right)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ z =ᴮ x.func j ⊓ x.bval j := le_inf hzj hbj
        _ ≤ z ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le j
            exact le_inf inf_le_right inf_le_left
    · -- y ∈ z
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y∈z
      set T := pair y z =ᴮ pair (x.func i) (x.func j) ⊓
        (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
      have hyi : T ≤ y =ᴮ x.func i := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hzj : T ≤ z =ᴮ x.func j := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hxixj : T ≤ x.func i ∈ᴮ x.func j := inf_le_right.trans inf_le_left
      -- y = xi, xi ∈ xj, xj = z  →  y ∈ z via mem_congr
      exact mem_congr (bv_symm hyi) (bv_symm hzj) hxixj
  · -- MPI: y∈x ∧ z∈x ∧ y∈z → ⨆ ij, ...
    intro ⟨Hy, Hz, Hyz⟩
    rw [mem_unfold] at Hy Hz
    -- Use iSup_inf_iSup to combine the two iSups, then bound elementwise
    apply le_trans (le_inf (le_inf Hy Hz) Hyz)
    -- goal: (⨆ i, bi⊓y=xi) ⊓ (⨆ j, bj⊓z=xj) ⊓ y∈z ≤ ⨆ (k,l), ...
    rw [show (⨆ i : x.type, x.bval i ⊓ y =ᴮ x.func i) ⊓
              (⨆ j : x.type, x.bval j ⊓ z =ᴮ x.func j) =
              ⨆ ij : x.type × x.type, (x.bval ij.1 ⊓ y =ᴮ x.func ij.1) ⊓
                (x.bval ij.2 ⊓ z =ᴮ x.func ij.2) from iSup_inf_iSup]
    rw [inf_comm]
    apply bv_cases_right; intro ⟨i, j⟩
    apply le_iSup_of_le (i, j)
    simp only [prod_bval]
    -- After bv_cases_right intro ⟨i, j⟩ and rw [inf_comm], context is:
    -- y∈z ⊓ ((bi⊓y=xi) ⊓ (bj⊓z=xj)) ≤ pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj))
    -- Extract parts:
    have hbeq_y : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y =ᴮ x.func i := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hbeq_z : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        z =ᴮ x.func j := inf_le_right.trans (inf_le_right.trans inf_le_right)
    have hbval_i : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval i := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hbval_j : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval j := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hyz : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y ∈ᴮ z := inf_le_left
    refine le_inf (pair_eq_pair_iff.mpr ⟨hbeq_y, hbeq_z⟩)
      (le_inf (mem_congr hbeq_y hbeq_z hyz) (le_inf hbval_i hbval_j))

-- src/aleph_one.lean:286
@[simp] lemma B_congr_mem_rel : B_congr (mem_rel : bSet 𝔹 → bSet 𝔹) := by
  intro x y Γ H_eq
  -- Use prod_ext: both subsets of prod x x
  have H_sub_x : Γ ≤ mem_rel x ⊆ᴮ prod x x := subset.mk_subset
  have H_prod_eq : Γ ≤ prod x x =ᴮ prod y y := prod_congr H_eq H_eq
  have H_sub_y : Γ ≤ mem_rel y ⊆ᴮ prod x x :=
    poset_yoneda_inv Γ subst_congr_subset_right (le_inf subset.mk_subset (bv_symm H_prod_eq))
  apply prod_ext H_sub_x H_sub_y
  apply le_iInf; intro v; rw [← deduction]
  apply le_iInf; intro w; rw [← deduction]
  -- ctx: Γ ⊓ v ∈ x ⊓ w ∈ x
  apply le_inf
  · -- pair v w ∈ mem_rel x → pair v w ∈ mem_rel y  (forward direction)
    rw [← deduction]
    -- Goal: Γ ⊓ v ∈ x ⊓ w ∈ x ⊓ pair v w ∈ mem_rel x ≤ pair v w ∈ mem_rel y
    -- Abbreviate the context:
    apply (mem_mem_rel_iff (x := y) (y := v) (z := w)).mpr
    -- Need: ctx ≤ v ∈ y ∧ ctx ≤ w ∈ y ∧ ctx ≤ v ∈ w
    have ctx_le_x_eq_y : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x ≤ x =ᴮ y :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x)
      (x := x) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_x_eq_y hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_x_eq_y hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩
  · -- pair v w ∈ mem_rel y → pair v w ∈ mem_rel x  (backward direction)
    rw [← deduction]
    apply (mem_mem_rel_iff (x := x) (y := v) (z := w)).mpr
    have ctx_le_y_eq_x : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y ≤ y =ᴮ x :=
      bv_symm (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq)))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y)
      (x := y) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_y_eq_x hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_y_eq_x hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩

-- src/aleph_one.lean:297
def prod_map (x y v w : bSet 𝔹) (f g : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun (pr : (prod (prod x v) (prod y w)).type) =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (v.func pr.1.2) (w.func pr.2.2) ∈ᴮ g)

-- src/aleph_one.lean:299
def prod_map_self (x y f : bSet 𝔹) : bSet 𝔹 :=
  prod_map x y x y f f

-- src/aleph_one.lean:302
lemma B_congr_prod_map_self_left_aux {y f x x' : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ x =ᴮ x') :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ prod_map_self x y f ⟹ z ∈ᴮ prod_map_self x' y f := by
  -- Goal: Γ ≤ ⨅ z, z ∈ prod_map_self x y f ⟹ z ∈ prod_map_self x' y f
  -- prod_map_self x y f = subset.mk χ where parent = prod(prod x x)(prod y y)
  -- Strategy: for each z, go through the iSup elements of prod_map_self x y f
  --   and produce corresponding elements for prod_map_self x' y f by reindexing
  apply le_iInf; intro z; rw [← deduction]
  -- ctx: Γ ⊓ z ∈ prod_map_self x y f
  -- unfold both sides
  show Γ ⊓ z ∈ᴮ prod_map_self x y f ≤ z ∈ᴮ prod_map_self x' y f
  -- Extract from iSup in prod_map_self x y f
  have Hmem_iff : Γ ⊓ z ∈ᴮ prod_map_self x y f ≤ z ∈ᴮ prod_map_self x y f := inf_le_right
  rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl] at Hmem_iff
  rw [mem_subset.mk_iff₂] at Hmem_iff
  apply le_trans (le_inf Hmem_iff le_rfl)
  apply bv_cases_left; intro pr
  obtain ⟨⟨i₁, i₂⟩, j₁, j₂⟩ := pr
  dsimp only
  -- ctx: ((x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)) ⊓
  --       (z=ᴮpair(pair xi₁ xi₂)(pair yj₁ yj₂) ⊓ (χ₁⊓χ₂)) ⊓ (Γ ⊓ z∈...)
  -- Need: ctx ≤ z ∈ prod_map_self x' y f
  -- bv_rw' on zeq: reduce to pair(xi₁ xi₂)(yj₁ yj₂) ∈ prod_map_self x' y f
  -- Then provide the witness directly via mem_subset.mk_iff₂.mpr
  -- xi₁ ∈ x' (via bv_rw'' Heq (xi₁∈x)): for the new index i₁', use mem_unfold + bv_cases_left
  -- To avoid index extraction, we stay in the iSup form and use bv_use
  rw [show prod_map_self x' y f = subset.mk (fun pr' : (prod (prod x' x') (prod y y)).type =>
    pair (x'.func pr'.1.1) (y.func pr'.2.1) ∈ᴮ f ⊓ pair (x'.func pr'.1.2) (y.func pr'.2.2) ∈ᴮ f) from rfl,
    mem_subset.mk_iff₂]
  -- Goal: ctx ≤ ⨆ pr', bval'(pr') ⊓ (z=ᴮfunc'(pr') ⊓ χ'(pr'))
  -- Ctx structure: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (zeq ⊓ (χ1⊓χ2)) ⊓ (Γ ⊓ z∈...)
  -- xi₁ ∈ x' (via mem_congr) → get i₁' via le_trans + bv_cases_left
  apply le_trans (b := (⨆ i₁' : x'.type, x'.bval i₁' ⊓ x.func i₁ =ᴮ x'.func i₁') ⊓ _)
  · apply le_inf
    · rw [← mem_unfold]
      -- prove ctx ≤ x.func i₁ ∈ᴮ x'
      exact mem_congr bv_refl (inf_le_right.trans (inf_le_left.trans H_eq))
        ((inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))).trans (mem_mk' x i₁))
    · exact le_rfl
  apply bv_cases_left; intro i₁'
  -- ctx1 = (x'.bval i₁' ⊓ xi₁=x'.func i₁') ⊓ ctx
  -- xi₂ ∈ x' → get i₂' via le_trans + bv_cases_left
  apply le_trans (b := (⨆ i₂' : x'.type, x'.bval i₂' ⊓ x.func i₂ =ᴮ x'.func i₂') ⊓ _)
  · apply le_inf
    · rw [← mem_unfold]
      -- prove ctx1 ≤ x.func i₂ ∈ᴮ x'
      exact mem_congr bv_refl (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans H_eq)))
        ((inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))).trans
          (mem_mk' x i₂))
    · exact le_rfl
  apply bv_cases_left; intro i₂'
  -- ctx2 = (x'.bval i₂' ⊓ xi₂=x'.func i₂') ⊓ ctx1
  -- ctx2 structure:
  --   (x'.bval i₂' ⊓ x.func i₂ =ᴮ x'.func i₂') ⊓
  --   ((x'.bval i₁' ⊓ x.func i₁ =ᴮ x'.func i₁') ⊓
  --    (((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (zeq ⊓ (χ1⊓χ2)) ⊓ (Γ ⊓ z∈...)))
  apply bv_use ((i₁', i₂'), j₁, j₂)
  dsimp only
  -- Extractions from ctx2 (after simp):
  --   x'.bval i₁' : ir.il.il
  --   xi₁=x'.func i₁' : ir.il.ir
  --   x'.bval i₂' : il.il
  --   xi₂=x'.func i₂' : il.ir
  --   xb1 : ir.ir.il.il.il
  --   xb2 : ir.ir.il.il.ir
  --   yb1 : ir.ir.il.ir.il
  --   yb2 : ir.ir.il.ir.ir
  --   zeq : ir.ir.ir.il
  --   χ1  : ir.ir.ir.ir.il
  --   χ2  : ir.ir.ir.ir.ir
  apply le_inf
  · -- bval': (x'.bval i₁' ⊓ x'.bval i₂') ⊓ (y.bval j₁ ⊓ y.bval j₂)
    apply le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))))
    · exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))))
  · apply le_inf
    · -- z =ᴮ pair(pair x'.func(i₁') x'.func(i₂'))(pair yj₁ yj₂)
      -- First prove z =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂), then rewrite xi₁ → x'.func i₁'
      apply bv_trans
      · -- zeq: ctx2 ≤ z =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
        exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left)))
      · apply pair_eq_pair_iff.mpr; constructor
        · apply pair_eq_pair_iff.mpr
          -- Hi₁'eq: ir.il.ir, Hi₂'eq: il.ir
          exact ⟨inf_le_right.trans (inf_le_left.trans inf_le_right), inf_le_left.trans inf_le_right⟩
        · apply pair_eq_pair_iff.mpr; exact ⟨bv_refl, bv_refl⟩
    · apply le_inf
      · -- pair x'.func(i₁') yj₁ ∈ f
        exact bv_rw' (ϕ := fun v => pair v (y.func j₁) ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
          (H := bv_symm (inf_le_right.trans (inf_le_left.trans inf_le_right)))
          (H_new := inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))))
      · -- pair x'.func(i₂') yj₂ ∈ f
        exact bv_rw' (ϕ := fun v => pair v (y.func j₂) ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
          (H := bv_symm (inf_le_left.trans inf_le_right))
          (H_new := inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))))

-- src/aleph_one.lean:329
@[simp] lemma B_congr_prod_map_self_left {y f : bSet 𝔹} :
    B_congr (fun x : bSet 𝔹 => prod_map_self x y f) := by
  intro x x' Γ H_eq
  apply mem_ext
  · apply B_congr_prod_map_self_left_aux; exact H_eq
  · apply B_congr_prod_map_self_left_aux; exact bv_symm H_eq

-- src/aleph_one.lean:336
set_option maxHeartbeats 400000 in
lemma mem_prod_map_self_iff {x y f a₁ a₂ b₁ b₂ : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod_map_self x y f ↔
    Γ ≤ a₁ ∈ᴮ x ∧ Γ ≤ a₂ ∈ᴮ x ∧ Γ ≤ b₁ ∈ᴮ y ∧ Γ ≤ b₂ ∈ᴮ y ∧
    Γ ≤ pair a₁ b₁ ∈ᴮ f ∧ Γ ≤ pair a₂ b₂ ∈ᴮ f := by
  constructor
  · -- forward: prove each of the 6 conclusions from H
    intro H
    rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
      pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl] at H
    rw [mem_subset.mk_iff₂] at H
    -- H : Γ ≤ ⨆ pr, bval pr ⊓ (pair_eq pr ⊓ χ pr)
    -- For pr = ((i₁,i₂),(j₁,j₂)):
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
    --   pair_eq = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    --   χ = pair xi₁ yj₁ ∈ f ⊓ pair xi₂ yj₂ ∈ f
    -- Each of the 6 conclusions: Γ ≤ P, proved by le_trans H (iSup_le ...)
    -- Helper: extract component equalities from the body
    -- body : bval ⊓ (peq ⊓ χ)
    -- peq : inf_le_right.trans inf_le_left
    -- after two pair_eq_pair_iff.mp: a₁=xi₁, a₂=xi₂, b₁=yj₁, b₂=yj₂
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    -- bval ⊓ (peq ⊓ (χ₁ ⊓ χ₂)) where
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
    --   peq  = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    --   χ₁   = pair xi₁ yj₁ ∈ f,   χ₂ = pair xi₂ yj₂ ∈ f
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    -- bval ⊓ (peq ⊓ (χ₁ ⊓ χ₂)) where
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)  [inf_le_left]
    --   peq  = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)  [inf_le_right.trans inf_le_left]
    --   χ₁   = pair xi₁ yj₁ ∈ f  [inf_le_right.trans inf_le_right.trans inf_le_left]
    --   χ₂   = pair xi₂ yj₂ ∈ f  [inf_le_right.trans inf_le_right.trans inf_le_right]
    -- All are proved using this tactic:
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)  [inf_le_left]
    --   peq  = pair_eq                [inf_le_right.trans inf_le_left]
    --   χ₁   = pair xi₁ yj₁ ∈ f     [inf_le_right.trans inf_le_right.trans inf_le_left]
    --   χ₂   = pair xi₂ yj₂ ∈ f     [inf_le_right.trans inf_le_right.trans inf_le_right]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    -- body structure: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    -- Chains: peq=ir.il; from peq: pair a₁ a₂ =ᴮ pair xi₁ xi₂ via eq_of_eq_pair_left
    --         from that: a₁=xi₁ via eq_of_eq_pair_left, a₂=xi₂ via eq_of_eq_pair_right
    -- bval: xb1=il.il.il, xb2=il.il.ir, yb1=il.ir.il, yb2=il.ir.ir
    -- χ1=ir.ir.il, χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq extraction: ir.il; bval: xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir
    -- χ1=ir.ir.il; χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq: ir.il; xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir
    -- χ1=ir.ir.il; χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq=ir.il; xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir; χ1=ir.ir.il; χ2=ir.ir.ir
    -- Inline approach: avoid 'have' and use exact with full chains
    -- After simp, body = ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- Use apply-based approach: each step creates a concrete goal, avoiding bidirectional inference
    -- Helper for peq extraction (used repeatedly):
    -- After simp: body ≤ peq ≡ body ≤ pair(pair a₁ a₂)(pair b₁ b₂)=ᴮpair(pair xi₁ xi₂)(pair yj₁ yj₂)
    -- via inf_le_right.trans inf_le_left.
    · -- a₁ ∈ x
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; dsimp only
      apply bv_rw' (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_left.trans inf_le_left)).trans (mem_mk' x i₁))
      apply eq_of_eq_pair_left'; apply eq_of_eq_pair_left'
      exact inf_le_right.trans inf_le_left
    · -- a₂ ∈ x
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; dsimp only
      apply bv_rw' (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_left.trans inf_le_right)).trans (mem_mk' x i₂))
      apply eq_of_eq_pair_right'; apply eq_of_eq_pair_left'
      exact inf_le_right.trans inf_le_left
    · -- b₁ ∈ y
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; dsimp only
      apply bv_rw' (ϕ := fun v => v ∈ᴮ y) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans (mem_mk' y j₁))
      apply eq_of_eq_pair_left'; apply eq_of_eq_pair_right'
      exact inf_le_right.trans inf_le_left
    · -- b₂ ∈ y
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; dsimp only
      apply bv_rw' (ϕ := fun v => v ∈ᴮ y) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_right.trans inf_le_right)).trans (mem_mk' y j₂))
      apply eq_of_eq_pair_right'; apply eq_of_eq_pair_right'
      exact inf_le_right.trans inf_le_left
    · -- pair a₁ b₁ ∈ f: use bv_rw' to rewrite pair a₁ b₁ to pair xi₁ yj₁ (which ∈ f)
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; dsimp only
      apply bv_rw' (ϕ := fun v => v ∈ᴮ f) (h_congr := B_ext_mem_left)
        (H_new := inf_le_right.trans (inf_le_right.trans inf_le_left))
      apply pair_congr
      · apply eq_of_eq_pair_left'; apply eq_of_eq_pair_left'; exact inf_le_right.trans inf_le_left
      · apply eq_of_eq_pair_left'; apply eq_of_eq_pair_right'; exact inf_le_right.trans inf_le_left
    · -- pair a₂ b₂ ∈ f: same but using χ₂
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; dsimp only
      apply bv_rw' (ϕ := fun v => v ∈ᴮ f) (h_congr := B_ext_mem_left)
        (H_new := inf_le_right.trans (inf_le_right.trans inf_le_right))
      apply pair_congr
      · apply eq_of_eq_pair_right'; apply eq_of_eq_pair_left'; exact inf_le_right.trans inf_le_left
      · apply eq_of_eq_pair_right'; apply eq_of_eq_pair_right'; exact inf_le_right.trans inf_le_left
  · -- backward: construct the witness index from the 6 hypotheses
    intro ⟨Ha₁, Ha₂, Hb₁, Hb₂, Hpair₁, Hpair₂⟩
    rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
      pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl]
    rw [mem_subset.mk_iff₂]
    -- Need: Γ ≤ ⨆ pr, bval pr ⊓ (pair_eq pr ⊓ χ pr)
    -- Extract witnesses via mem_unfold and sequential bv_cases_left
    rw [mem_unfold] at Ha₁ Ha₂ Hb₁ Hb₂
    -- LHS0 = (((Ha₁ ⊓ Ha₂) ⊓ Hb₁) ⊓ Hb₂) ⊓ Γ
    apply le_trans (le_inf (le_inf (le_inf (le_inf Ha₁ Ha₂) Hb₁) Hb₂) le_rfl)
    -- Extract i₁ from Ha₁: inf_le_left^3 then inf_le_left
    apply le_trans (le_inf (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))) le_rfl)
    apply bv_cases_left; intro i₁
    -- ctx1 = (x.bval i₁ ⊓ a₁=xi₁) ⊓ LHS0
    -- Extract i₂ from Ha₂ in LHS0: inf_le_right then inf_le_left^3 then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro i₂
    -- ctx2 = (x.bval i₂ ⊓ a₂=xi₂) ⊓ ctx1
    -- Extract j₁ from Hb₁ in LHS0: inf_le_right^2 then inf_le_left^2 then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro j₁
    -- ctx3 = (y.bval j₁ ⊓ b₁=yj₁) ⊓ ctx2
    -- Extract j₂ from Hb₂ in LHS0: inf_le_right^3 then inf_le_left then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro j₂
    -- ctx4 = (y.bval j₂ ⊓ b₂=yj₂) ⊓ ctx3
    -- ctx4 components (left-to-right nesting):
    --   y.bval j₂: inf_le_left.trans inf_le_left
    --   b₂=yj₂:   inf_le_left.trans inf_le_right
    --   y.bval j₁: inf_le_right.trans (inf_le_left.trans inf_le_left)
    --   b₁=yj₁:   inf_le_right.trans (inf_le_left.trans inf_le_right)
    --   x.bval i₂: inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    --   a₂=xi₂:   inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
    --   x.bval i₁: inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    --   a₁=xi₁:   inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    --   Γ:         inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    apply bv_use ((i₁, i₂), j₁, j₂)
    dsimp only
    apply le_inf
    · -- bval: (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
      exact le_inf (le_inf
        (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))))
        (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))))
        (le_inf
          (inf_le_right.trans (inf_le_left.trans inf_le_left))
          (inf_le_left.trans inf_le_left))
    · apply le_inf
      · -- pair equality: pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
        -- ctx4 component accesses: a₁=xi₁ at (.3.left.right), a₂=xi₂ at (.3.right), b₁=yj₁ at (.2.right), b₂=yj₂ at (.1.right)
        -- But mem_unfold gives: a₁ =ᴮ x.func i₁, not x.func i₁ =ᴮ a₁
        -- So we use them directly (no bv_symm needed):
        apply pair_eq_pair_iff.mpr; constructor
        · apply pair_eq_pair_iff.mpr; exact ⟨
            inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))),
            inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))⟩
        · apply pair_eq_pair_iff.mpr; exact ⟨
            inf_le_right.trans (inf_le_left.trans inf_le_right),
            inf_le_left.trans inf_le_right⟩
      · -- χ: pair(xi₁)(yj₁) ∈ f ⊓ pair(xi₂)(yj₂) ∈ f
        -- Γ accessible via inf_le_right^5 from ctx4; then compose with Hpair₁, Hpair₂
        apply le_inf
        · -- pair(xi₁)(yj₁) ∈ f: use mem_congr (pair a₁ b₁ =ᴮ pair xi₁ yj₁) bv_refl (pair a₁ b₁ ∈ f)
          apply mem_congr _ bv_refl
          · -- pair a₁ b₁ ∈ f via Hpair₁
            exact (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
                    (inf_le_right.trans inf_le_right)))).trans Hpair₁
          · -- pair a₁ b₁ =ᴮ pair xi₁ yj₁ via pair_congr and equalities from ctx4
            apply pair_eq_pair_iff.mpr
            exact ⟨inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))),
                   inf_le_right.trans (inf_le_left.trans inf_le_right)⟩
        · -- pair(xi₂)(yj₂) ∈ f
          apply mem_congr _ bv_refl
          · exact (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
                    (inf_le_right.trans inf_le_right)))).trans Hpair₂
          · apply pair_eq_pair_iff.mpr
            exact ⟨inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)),
                   inf_le_left.trans inf_le_right⟩

-- src/aleph_one.lean:379
def induced_epsilon_rel (η : bSet 𝔹) (x : bSet 𝔹) (f : bSet 𝔹) : bSet 𝔹 :=
  image (mem_rel η) (prod x x) (prod_map_self η x f)

-- src/aleph_one.lean:382
lemma eq_pair_of_mem_induced_epsilon_rel {η x f pr : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pr ∈ᴮ induced_epsilon_rel η x f) :
    ∃ a b : bSet 𝔹, Γ ≤ a ∈ᴮ x ∧ Γ ≤ b ∈ᴮ x ∧ Γ ≤ pr =ᴮ pair a b ∧
    Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f := by
  have hmem : Γ ≤ pr ∈ᴮ prod x x := mem_of_mem_subset subset.mk_subset H_mem
  obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp hmem
  exact ⟨v, w, Hv, Hw, H_eq,
    bv_rw' (bv_symm H_eq) (ϕ := fun z => z ∈ᴮ induced_epsilon_rel η x f)
      (h_congr := B_ext_mem_left) (H_new := H_mem)⟩

-- src/aleph_one.lean:391
lemma mem_induced_epsilon_rel_iff {η x f a b : bSet 𝔹} {Γ}
    (_H_func : Γ ≤ is_function η x f) :
    Γ ≤ pair a b ∈ᴮ (induced_epsilon_rel η x f) ↔
    (Γ ≤ a ∈ᴮ x) ∧ (Γ ≤ b ∈ᴮ x) ∧
    (Γ ≤ ⨆ a', a' ∈ᴮ η ⊓ ⨆ b', b' ∈ᴮ η ⊓ (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b')) := by
  -- induced_epsilon_rel η x f = image (mem_rel η) (prod x x) (prod_map_self η x f)
  -- mem_image_iff: pair a b ∈ image S Y F ↔ pair a b ∈ Y ∧ ∃ z, z ∈ S ∧ pair z (pair a b) ∈ F
  -- unfold induced_epsilon_rel to allow mem_image_iff
  show Γ ≤ pair a b ∈ᴮ image (mem_rel η) (prod x x) (prod_map_self η x f) ↔ _
  constructor
  · -- Forward: from pair a b ∈ image (mem_rel η) (prod x x) (prod_map_self η x f)
    intro H
    rw [mem_image_iff] at H
    obtain ⟨H_prod, H_sup⟩ := H
    rw [mem_prod_iff] at H_prod
    obtain ⟨Ha, Hb⟩ := H_prod
    refine ⟨Ha, Hb, ?_⟩
    -- H_sup: Γ ≤ ⨆ z, z ∈ mem_rel η ⊓ pair z (pair a b) ∈ prod_map_self η x f
    -- For each z in iSup, derive the iSup on a', b'
    apply H_sup.trans; apply iSup_le; intro z
    -- goal: (z ∈ mem_rel η ⊓ pair z (pair a b) ∈ prod_map_self η x f) ≤ ⨆ a', ...
    -- Now we have a concrete LHS — no more `_` issues
    have hz_prod : (z ∈ᴮ mem_rel η ⊓ pair z (pair a b) ∈ᴮ prod_map_self η x f) ≤ z ∈ᴮ prod η η :=
      mem_of_mem_subset subset.mk_subset inf_le_left
    obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp hz_prod
    -- provide witnesses a' = v, b' = w
    apply bv_use v; apply le_inf Hv
    apply bv_use w; apply le_inf Hw
    -- need: pair v a ∈ f ⊓ pair w b ∈ f ⊓ v ∈ w
    -- From pair z (pair a b) ∈ prod_map_self η x f (rewrite z = pair v w via H_eq)
    -- Get pair (pair v w) (pair a b) ∈ prod_map_self via bv_rw' on Hz_map
    have Hz_map : (z ∈ᴮ mem_rel η ⊓ pair z (pair a b) ∈ᴮ prod_map_self η x f) ≤
        pair (pair v w) (pair a b) ∈ᴮ prod_map_self η x f := by
      apply bv_rw' (ϕ := fun s => pair s (pair a b) ∈ᴮ prod_map_self η x f)
        (h_congr := B_ext_pair_mem_left) (H_new := inf_le_right)
      exact bv_symm H_eq
    -- Now use mem_prod_map_self_iff (no H_func needed) to extract components
    obtain ⟨_Hv', _Hw', _Ha, _Hb, Hpva, Hwb⟩ := mem_prod_map_self_iff.mp Hz_map
    -- Get v ∈ w from pair v w ∈ mem_rel η (via H_eq rewrite)
    have Hpvw_mem_rel : (z ∈ᴮ mem_rel η ⊓ pair z (pair a b) ∈ᴮ prod_map_self η x f) ≤
        pair v w ∈ᴮ mem_rel η := by
      apply bv_rw' (ϕ := fun s => s ∈ᴮ mem_rel η)
        (h_congr := B_ext_mem_left) (H_new := inf_le_left)
      exact bv_symm H_eq
    obtain ⟨_, _, Hvw⟩ := mem_mem_rel_iff.mp Hpvw_mem_rel
    exact le_inf (le_inf Hpva Hwb) Hvw
  · -- Backward: construct the image membership from the 3 conditions
    intro ⟨Ha, Hb, H_sup⟩
    rw [mem_image_iff]
    refine ⟨mem_prod_iff.mpr ⟨Ha, Hb⟩, ?_⟩
    -- H_sup: Γ ≤ ⨆ a', a'∈η ⊓ ⨆ b', b'∈η ⊓ (pair a' a ∈ f ⊓ pair b' b ∈ f ⊓ a'∈b')
    -- Extract a', b' witnesses
    apply le_trans (le_inf H_sup le_rfl)
    apply bv_cases_left; intro a'
    -- goal: (a'∈η ⊓ ⨆ b', b'∈η ⊓ ...) ⊓ Γ ≤ ⨆ z, z∈mem_rel η ⊓ pair z (pair a b) ∈ prod_map_self η x f
    -- extract ⨆ b' from left: inf_le_left.trans inf_le_right
    apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
    apply bv_cases_left; intro b'
    -- ctx: (b'∈η ⊓ (pair a' a ∈ f ⊓ pair b' b ∈ f ⊓ a'∈b')) ⊓ ((a'∈η ⊓ ⨆ b',..) ⊓ Γ)
    -- Provide z = pair a' b'
    apply bv_use (pair a' b')
    apply le_inf
    · -- pair a' b' ∈ mem_rel η: need a'∈η, b'∈η, a'∈b'
      -- a'∈η: from right part, a'∈η at inf_le_right.trans inf_le_left.trans inf_le_left
      -- b'∈η: from left part at inf_le_left.trans inf_le_left
      -- a'∈b': from left part at inf_le_left.trans inf_le_right.trans inf_le_right
      rw [mem_mem_rel_iff]
      refine ⟨?_, ?_, ?_⟩
      · exact inf_le_right.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans inf_le_left
      · exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    · -- pair (pair a' b') (pair a b) ∈ prod_map_self η x f
      -- a'∈η: inf_le_right.trans inf_le_left.trans inf_le_left
      -- b'∈η: inf_le_left.trans inf_le_left
      -- a∈x: from Ha (outer)
      -- b∈x: from Hb (outer)
      -- pair a' a ∈ f: inf_le_left.trans inf_le_right.trans inf_le_left.trans inf_le_left
      -- pair b' b ∈ f: inf_le_left.trans inf_le_right.trans inf_le_left.trans inf_le_right
      -- pair (pair a' b') (pair a b) ∈ prod_map_self η x f
      -- Use mem_prod_map_self_iff with the ctx's H_func access
      exact mem_prod_map_self_iff.mpr
        ⟨inf_le_right.trans (inf_le_left.trans inf_le_left),
         inf_le_left.trans inf_le_left,
         inf_le_right.trans (inf_le_right.trans Ha),
         inf_le_right.trans (inf_le_right.trans Hb),
         inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)),
         inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))⟩

-- src/aleph_one.lean:425
lemma mem_induced_epsilon_rel_of_mem {η x f a b : bSet 𝔹} {Γ}
    (H_mem₁ : Γ ≤ a ∈ᴮ η) (H_mem₂ : Γ ≤ b ∈ᴮ η) (H_mem : Γ ≤ a ∈ᴮ b)
    (H_func : Γ ≤ is_function η x f) :
    Γ ≤ pair (function_eval H_func a H_mem₁) (function_eval H_func b H_mem₂) ∈ᴮ
      induced_epsilon_rel η x f := by
  rw [mem_induced_epsilon_rel_iff H_func]
  refine ⟨function_eval_mem_codomain, function_eval_mem_codomain, ?_⟩
  apply bv_use a; refine le_inf H_mem₁ ?_
  apply bv_use b; refine le_inf H_mem₂ ?_
  exact le_inf (le_inf function_eval_pair_mem function_eval_pair_mem) H_mem

-- src/aleph_one.lean:437
lemma mem_of_mem_induced_epsilon_rel {η x f a' b' a b : bSet 𝔹} {Γ}
    (H_inj : Γ ≤ is_injective_function η x f)
    (H_mem₁ : Γ ≤ pair a' a ∈ᴮ f) (H_mem₂ : Γ ≤ pair b' b ∈ᴮ f)
    (H_mem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ a' ∈ᴮ b' := by
  rw [mem_induced_epsilon_rel_iff (bv_and_left H_inj)] at H_mem
  obtain ⟨_Ha_mem, _Hb_mem, H⟩ := H_mem
  -- H : Γ ≤ ⨆ a'', a'' ∈ η ⊓ ⨆ b'', b'' ∈ η ⊓ (pair a'' a ∈ f ⊓ pair b'' b ∈ f ⊓ a'' ∈ b'')
  have H_inj' : Γ ≤ is_inj f := is_inj_of_is_injective_function H_inj
  apply le_trans (le_inf H le_rfl)
  apply bv_cases_left; intro a''
  -- goal: (a''∈η ⊓ ⨆ b'', b''∈η ⊓ (...)) ⊓ Γ ≤ a'∈b'
  -- extract ⨆ b'' to left
  apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
  apply bv_cases_left; intro b''
  -- goal: (b''∈η ⊓ ((pair a'' a ∈ f ⊓ pair b'' b ∈ f) ⊓ a''∈b'')) ⊓ ((a''∈η ⊓ ⨆ ..) ⊓ Γ) ≤ a'∈b'
  -- use `apply` to decompose mem_congr, so each subgoal has a concrete type
  apply mem_congr (x₁ := a'') (x₂ := b'')
  · -- prove a'' =ᴮ a' via is_inj: pair a'' a ∈ f and pair a' a ∈ f
    apply eq_of_is_inj_of_eq
    · exact inf_le_right.trans (inf_le_right.trans H_inj')
    · exact bv_refl (x := a)
    · exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    · exact inf_le_right.trans (inf_le_right.trans H_mem₁)
  · -- prove b'' =ᴮ b' via is_inj: pair b'' b ∈ f and pair b' b ∈ f
    apply eq_of_is_inj_of_eq
    · exact inf_le_right.trans (inf_le_right.trans H_inj')
    · exact bv_refl (x := b)
    · exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
    · exact inf_le_right.trans (inf_le_right.trans H_mem₂)
  · -- prove a'' ∈ b''
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- ============================================================
-- src/aleph_one.lean:451-579: remaining well_ordering lemmas
-- ============================================================

-- src/aleph_one.lean:451
lemma induced_epsilon_rel_sub_image_left {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f)
    (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ a ∈ᴮ image η x f := by
  rw [mem_image_iff]; rw [mem_induced_epsilon_rel_iff H_func] at H
  obtain ⟨Ha_mem, _, H_sup⟩ := H
  refine ⟨Ha_mem, le_trans H_sup (iSup_le (fun a' => le_iSup_of_le a'
    (le_inf inf_le_left (le_trans inf_le_right (iSup_le (fun b' =>
      le_trans inf_le_right (inf_le_left.trans inf_le_left)))))))⟩

-- src/aleph_one.lean:461
lemma induced_epsilon_rel_sub_image_right {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f)
    (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ b ∈ᴮ image η x f := by
  rw [mem_image_iff]; rw [mem_induced_epsilon_rel_iff H_func] at H
  obtain ⟨_, Hb_mem, H_sup⟩ := H
  refine ⟨Hb_mem, le_trans H_sup (iSup_le (fun a' => le_trans inf_le_right (iSup_le (fun b' =>
    le_iSup_of_le b' (le_inf inf_le_left (le_trans inf_le_right
      (inf_le_left.trans inf_le_right)))))))⟩

-- src/aleph_one.lean:471
set_option maxHeartbeats 800000 in
lemma image_eq_of_eq_induced_epsilon_rel_aux
    {κ η ρ f g : bSet 𝔹} {Γ}
    (Hη_inj : Γ ≤ is_injective_function η κ f)
    (Hρ_inj : Γ ≤ is_injective_function ρ κ g)
    (H_eq : Γ ≤ induced_epsilon_rel η κ f =ᴮ induced_epsilon_rel ρ κ g)
    (H_exists_two : Γ ≤ exists_two η) :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ image η κ f ⟹ z ∈ᴮ image ρ κ g := by
  apply le_iInf; intro z; rw [← deduction]
  -- ctx: Γ ⊓ z ∈ image η κ f
  -- Get z' ∈ η s.t. pair z' z ∈ f
  have H_func : Γ ⊓ z ∈ᴮ image η κ f ≤ is_function η κ f := inf_le_left.trans (bv_and_left Hη_inj)
  have Hz_mem : Γ ⊓ z ∈ᴮ image η κ f ≤ z ∈ᴮ image η κ f := inf_le_right
  rw [mem_image_iff] at Hz_mem
  obtain ⟨Hz_omega, Hz_sup⟩ := Hz_mem
  -- Hz_sup : ctx ≤ ⨆ z', z' ∈ η ⊓ pair z' z ∈ f
  apply le_trans (le_inf Hz_sup le_rfl)
  apply bv_cases_left; intro z'
  -- ctx1 = (z' ∈ η ⊓ pair z' z ∈ f) ⊓ ctx
  have Hz'_mem_η : (z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f) ≤ z' ∈ᴮ η :=
    inf_le_left.trans inf_le_left
  have Hpz'z_mem : (z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f) ≤ pair z' z ∈ᴮ f :=
    inf_le_left.trans inf_le_right
  -- Get w' from exists_two: z' ∈ η → ∃ w', w' ∈ η ∧ (z' ∈ w' ∨ w' ∈ z')
  have H_et : (z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f) ≤
      ⨆ w', w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z') :=
    le_trans (le_inf (inf_le_right.trans (inf_le_left.trans (H_exists_two.trans (iInf_le _ z'))))
      Hz'_mem_η) bv_imp_elim
  -- H_et : ctx1 ≤ ⨆ w', w' ∈ η ⊓ (z' ∈ w' ⊔ w' ∈ z')
  apply le_trans (le_inf H_et le_rfl)
  apply bv_cases_left; intro w'
  -- ctx2 = (w' ∈ η ⊓ (z'∈w' ⊔ w'∈z')) ⊓ ctx1
  -- Case split on z' ∈ w' or w' ∈ z'
  apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
  apply bv_or_elim_left
  · -- Case z' ∈ w': ctx3 = (z' ∈ w') ⊓ ctx2
    -- Extractions: w'∈η=ir.il.il, z'∈w'=il, pair z'z∈f=ir.il.ir, H_eq at ir.ir.ir.ir.H_eq
    -- H_func(η) at ir.ir.ir.il.bv_and_left_Hη_inj
    have Hw'_mem_η : (z' ∈ᴮ w') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f))) ≤ w' ∈ᴮ η :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hfunc2 : (z' ∈ᴮ w') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f))) ≤ is_function η κ f :=
      inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hη_inj))))
    -- Goal: ctx3 ≤ z ∈ image ρ κ g
    -- Use sub_image_left for ρ: pair z (f_η(w')) ∈ ind_eps_ρ → z ∈ image ρ κ g
    apply induced_epsilon_rel_sub_image_left
    · -- H_func for ρ: ctx3 ≤ is_function ρ κ g
      -- ctx3.ir.ir.ir.il = Γ → bv_and_left Hρ_inj
      exact inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hρ_inj))))
    · -- pair z (f_η(w')) ∈ ind_eps_ρ (via rewrite ind_eps_η → ind_eps_ρ using H_eq)
      exact bv_rw' (ϕ := fun r => pair z (function_eval Hfunc2 w' Hw'_mem_η) ∈ᴮ r)
        (h_congr := B_ext_mem_right)
        (bv_symm (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans H_eq)))))
        (H_new := by
          rw [mem_induced_epsilon_rel_iff Hfunc2]
          -- z∈κ: ctx3.ir.ir.ir.Hz_omega (3 rights, then Hz_omega which has LHS Γ⊓z∈image)
          refine ⟨inf_le_right.trans (inf_le_right.trans (inf_le_right.trans Hz_omega)),
                 function_eval_mem_codomain, ?_⟩
          -- z'∈η: ctx3.ir.ir.il.il
          apply bv_use z'; refine le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))) ?_
          apply bv_use w'; refine le_inf Hw'_mem_η ?_
          -- pair z' z ∈ f: ctx3.ir.ir.il.ir
          exact le_inf (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))) function_eval_pair_mem)
                       inf_le_left)
  · -- Case w' ∈ z': ctx3' = (w' ∈ z') ⊓ ctx2
    have Hz'_mem_η' : (w' ∈ᴮ z') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f))) ≤ z' ∈ᴮ η :=
      inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    have Hw'_mem_η' : (w' ∈ᴮ z') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f))) ≤ w' ∈ᴮ η :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hfunc2' : (w' ∈ᴮ z') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η κ f))) ≤ is_function η κ f :=
      inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hη_inj))))
    -- Goal: ctx3' ≤ z ∈ image ρ κ g
    apply induced_epsilon_rel_sub_image_right
    · -- H_func for ρ: ctx3'.ir.ir.ir.il.bv_and_left_Hρ_inj
      exact inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hρ_inj))))
    · -- pair (f_η(w')) z ∈ ind_eps_ρ (via rewrite using H_eq)
      exact bv_rw' (ϕ := fun r => pair (function_eval Hfunc2' w' Hw'_mem_η') z ∈ᴮ r)
        (h_congr := B_ext_mem_right)
        (bv_symm (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans H_eq)))))
        (H_new := by
          rw [mem_induced_epsilon_rel_iff Hfunc2']
          refine ⟨function_eval_mem_codomain,
                 inf_le_right.trans (inf_le_right.trans (inf_le_right.trans Hz_omega)), ?_⟩
          apply bv_use w'; apply le_inf Hw'_mem_η'
          apply bv_use z'; apply le_inf Hz'_mem_η'
          -- pair z'z∈f: ctx3'.ir.ir.il.ir; w'∈z': il
          exact le_inf (le_inf function_eval_pair_mem (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))))
                       inf_le_left)

-- src/aleph_one.lean:503
lemma image_eq_of_eq_induced_epsilon_rel
    {κ η ρ f g : bSet 𝔹} {Γ}
    (Hη_inj : Γ ≤ is_injective_function η κ f)
    (Hρ_inj : Γ ≤ is_injective_function ρ κ g)
    (H_eq : Γ ≤ induced_epsilon_rel η κ f =ᴮ induced_epsilon_rel ρ κ g)
    (H_exists_two : Γ ≤ exists_two η)
    (H_exists_two' : Γ ≤ exists_two ρ) :
    Γ ≤ image η κ f =ᴮ image ρ κ g := by
  refine mem_ext ?_ ?_
  · apply image_eq_of_eq_induced_epsilon_rel_aux Hη_inj Hρ_inj H_eq H_exists_two
  · apply image_eq_of_eq_induced_epsilon_rel_aux Hρ_inj Hη_inj (bv_symm H_eq) H_exists_two'

-- src/aleph_one.lean:515
lemma eq_of_eq_induced_epsilon_rel
    {κ η ρ f g : bSet 𝔹} {Γ}
    (Hη_ord : Γ ≤ Ord η) (Hρ_ord : Γ ≤ Ord ρ)
    (Hη_inj : Γ ≤ is_injective_function η κ f)
    (Hρ_inj : Γ ≤ is_injective_function ρ κ g)
    (H_eq : Γ ≤ induced_epsilon_rel η κ f =ᴮ induced_epsilon_rel ρ κ g)
    (H_exists_two : Γ ≤ exists_two η)
    (H_exists_two' : Γ ≤ exists_two ρ) :
    Γ ≤ η =ᴮ ρ := by
  -- Suffices: construct an eps_iso η ρ h, then apply eq_of_Ord_eps_iso
  suffices H_eps : Γ ≤ ⨆ h, eps_iso η ρ h from eq_of_Ord_eps_iso Hη_ord Hρ_ord H_eps
  -- Step 1: Build the components
  -- f_factor : η → image(η,ω,f), inj
  have Hf_factor := factor_image_is_injective_function Hη_inj
  -- g_inverse : image(ρ,ω,g) → ρ, inj
  have Hg_inv := @injective_function_inverse_is_injective_function _ _ _ _ _ _ Hρ_inj
  -- image(η) = image(ρ) from H_eq and exists_two conditions
  have H_img_eq : Γ ≤ image η κ f =ᴮ image ρ κ g :=
    image_eq_of_eq_induced_epsilon_rel Hη_inj Hρ_inj H_eq H_exists_two H_exists_two'
  -- g_inverse_rw : is_injective_function (image η ω f) ρ g⁻¹
  -- (rewrite image(ρ) to image(η) in g_inverse's domain type)
  have Hg_inv_rw : Γ ≤ is_injective_function (image η κ f) ρ
      (injective_function_inverse Hρ_inj) :=
    bv_rw' (H := H_img_eq) (h_congr := B_ext_is_injective_function_left) (H_new := Hg_inv)
  -- Step 2: Let h = comp(f_factor, g_inverse_rw)
  apply le_iSup_of_le (injective_function_comp Hf_factor Hg_inv_rw)
  -- Step 3: Show eps_iso η ρ h = is_function ⊓ strong_eps_hom ⊓ is_surj
  refine le_inf (le_inf ?_ ?_) ?_
  · -- is_function η ρ h
    exact injective_function_comp_is_function
  · -- strong_eps_hom η ρ h
    rw [strong_eps_hom_iff]
    intro Γ' H_le z₁ Hz₁_η z₂ Hz₂_η w₁ Hw₁_ρ w₂ Hw₂_ρ Hpr₁ Hpr₂
    -- Hpr₁ : pair z₁ w₁ ∈ h = comp(f_factor, g_inv_rw)
    -- Hpr₂ : pair z₂ w₂ ∈ h
    -- Unfold comp membership to get intermediate elements v₁, v₂ ∈ image(η)
    have Hf_func := is_func'_of_is_injective_function (H_le.trans Hf_factor)
    have Hg_func := is_func'_of_is_injective_function (H_le.trans Hg_inv_rw)
    have H_mem₁ := (mem_is_func'_comp_iff Hf_func Hg_func).mp Hpr₁
    have H_mem₂ := (mem_is_func'_comp_iff Hf_func Hg_func).mp Hpr₂
    -- H_mem₁ : z₁ ∈ η ∧ w₁ ∈ ρ ∧ ⨆ v₁, v₁ ∈ image(η) ⊓ (pair z₁ v₁ ∈ f ⊓ pair v₁ w₁ ∈ g⁻¹)
    obtain ⟨_, _, H_v₁_ex⟩ := H_mem₁
    obtain ⟨_, _, H_v₂_ex⟩ := H_mem₂
    obtain ⟨v₁, Hv₁⟩ := exists_convert H_v₁_ex
      (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
    obtain ⟨v₂, Hv₂⟩ := exists_convert H_v₂_ex
      (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
    -- v₁, v₂ ∈ image(η) ⊓ (pair z₁ v₁ ∈ f ⊓ pair v₁ w₁ ∈ g⁻¹)
    have Hv₁_img : Γ' ≤ v₁ ∈ᴮ image η κ f := Hv₁.trans inf_le_left
    have Hv₁_f : Γ' ≤ pair z₁ v₁ ∈ᴮ f := Hv₁.trans (inf_le_right.trans inf_le_left)
    have Hv₁_ginv : Γ' ≤ pair v₁ w₁ ∈ᴮ injective_function_inverse Hρ_inj :=
      Hv₁.trans (inf_le_right.trans inf_le_right)
    have Hv₂_img : Γ' ≤ v₂ ∈ᴮ image η κ f := Hv₂.trans inf_le_left
    have Hv₂_f : Γ' ≤ pair z₂ v₂ ∈ᴮ f := Hv₂.trans (inf_le_right.trans inf_le_left)
    have Hv₂_ginv : Γ' ≤ pair v₂ w₂ ∈ᴮ injective_function_inverse Hρ_inj :=
      Hv₂.trans (inf_le_right.trans inf_le_right)
    -- pair v₁ w₁ ∈ g⁻¹ → pair w₁ v₁ ∈ g (by mem_inj_inverse_iff)
    have Hg_func₀ := is_func'_of_is_injective_function (H_le.trans Hρ_inj)
    have Hg_inj₀ := is_inj_of_is_injective_function (H_le.trans Hρ_inj)
    have Hw₁_v₁ := (mem_inj_inverse_iff Hg_func₀ Hg_inj₀).mp Hv₁_ginv
    have Hw₂_v₂ := (mem_inj_inverse_iff Hg_func₀ Hg_inj₀).mp Hv₂_ginv
    -- Hw₁_v₁ : w₁ ∈ ρ ∧ v₁ ∈ κ ∧ pair w₁ v₁ ∈ g
    -- Hw₂_v₂ : w₂ ∈ ρ ∧ v₂ ∈ κ ∧ pair w₂ v₂ ∈ g
    have Hpair_w₁v₁_g := Hw₁_v₁.2.2
    have Hpair_w₂v₂_g := Hw₂_v₂.2.2
    -- v₁, v₂ ∈ image(η) = image(ρ) (via H_img_eq)
    -- Actually, key: show v₁ ∈ v₂ ↔ z₁ ∈ z₂ ↔ w₁ ∈ w₂
    -- z₁ ∈ z₂ → v₁ ∈ v₂: from induced_epsilon_rel η κ f
    -- v₁ ∈ v₂ → w₁ ∈ w₂: from induced_epsilon_rel ρ κ g (via H_eq)
    constructor
    · -- Forward: z₁ ∈ z₂ → w₁ ∈ w₂
      intro Hz₁z₂
      -- pair v₁ v₂ ∈ induced_epsilon_rel η ω f (since z₁∈η, z₂∈η, pair z₁v₁∈f, pair z₂v₂∈f, z₁∈z₂)
      have Hv₁_omega : Γ' ≤ v₁ ∈ᴮ κ := mem_of_mem_subset (H_le.trans image_subset) Hv₁_img
      have Hv₂_omega : Γ' ≤ v₂ ∈ᴮ κ := mem_of_mem_subset (H_le.trans image_subset) Hv₂_img
      have Hpair_v₁v₂_ind_η : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel η κ f := by
        rw [mem_induced_epsilon_rel_iff (H_le.trans (bv_and_left Hη_inj))]
        exact ⟨Hv₁_omega, Hv₂_omega,
               le_iSup_of_le z₁ (le_inf Hz₁_η (le_iSup_of_le z₂
                 (le_inf Hz₂_η (le_inf (le_inf Hv₁_f Hv₂_f) Hz₁z₂))))⟩
      -- pair v₁ v₂ ∈ induced_epsilon_rel ρ ω g (via H_eq)
      have Hpair_v₁v₂_ind_ρ : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel ρ κ g :=
        bv_rw' (H := H_le.trans (bv_symm H_eq)) (h_congr := B_ext_mem_right)
          (H_new := Hpair_v₁v₂_ind_η)
      -- From pair v₁ v₂ ∈ ind_ρ with pair w₁ v₁ ∈ g and pair w₂ v₂ ∈ g: w₁ ∈ w₂
      exact mem_of_mem_induced_epsilon_rel (H_le.trans Hρ_inj) Hpair_w₁v₁_g Hpair_w₂v₂_g
        Hpair_v₁v₂_ind_ρ
    · -- Backward: w₁ ∈ w₂ → z₁ ∈ z₂
      intro Hw₁w₂
      -- pair v₁ v₂ ∈ induced_epsilon_rel ρ ω g (since w₁∈ρ, w₂∈ρ, pair w₁v₁∈g, pair w₂v₂∈g, w₁∈w₂)
      have Hv₁_omega : Γ' ≤ v₁ ∈ᴮ κ := Hw₁_v₁.2.1
      have Hv₂_omega : Γ' ≤ v₂ ∈ᴮ κ := Hw₂_v₂.2.1
      have Hpair_v₁v₂_ind_ρ : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel ρ κ g := by
        rw [mem_induced_epsilon_rel_iff (H_le.trans (bv_and_left Hρ_inj))]
        exact ⟨Hv₁_omega, Hv₂_omega,
               le_iSup_of_le w₁ (le_inf Hw₁_ρ (le_iSup_of_le w₂
                 (le_inf Hw₂_ρ (le_inf (le_inf Hpair_w₁v₁_g Hpair_w₂v₂_g) Hw₁w₂))))⟩
      -- pair v₁ v₂ ∈ induced_epsilon_rel η ω f (via H_eq symm)
      have Hpair_v₁v₂_ind_η : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel η κ f :=
        bv_rw' (H := H_le.trans H_eq) (h_congr := B_ext_mem_right) (H_new := Hpair_v₁v₂_ind_ρ)
      -- From pair v₁ v₂ ∈ ind_η with pair z₁ v₁ ∈ f and pair z₂ v₂ ∈ f: z₁ ∈ z₂
      exact mem_of_mem_induced_epsilon_rel (H_le.trans Hη_inj) Hv₁_f Hv₂_f Hpair_v₁v₂_ind_η
  · -- is_surj η ρ h
    -- h = comp(f_factor, g_inv_rw)
    -- f_factor is surjective onto image(η) (surj_image)
    -- g_inv_rw is surjective onto ρ (injective_function_inverse_is_injective_function's surjectivity)
    apply is_func'_comp_surj
      (is_func'_of_is_injective_function Hf_factor)
      (is_func'_of_is_injective_function Hg_inv_rw)
    · -- f_factor is surjective η → image(η)
      exact surj_image (is_func'_of_is_injective_function Hη_inj)
    · -- g_inv_rw is surjective image(η) → ρ
      -- inj_inverse_is_surj gives: is_surj (image ρ κ g) ρ (inj_inverse)
      -- After rewriting image(ρ) = image(η) via H_img_eq:
      apply bv_rw' (H := H_img_eq)
        (ϕ := fun z => is_surj z ρ (injective_function_inverse Hρ_inj))
        (h_congr := B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
          B_ext_iSup (h := fun w => B_ext_inf (h₁ := B_ext_mem_right) (h₂ := B_ext_const)))))
      exact inj_inverse_is_surj
        (is_func'_of_is_injective_function Hρ_inj)
        (is_inj_of_is_injective_function Hρ_inj)

end bSet
