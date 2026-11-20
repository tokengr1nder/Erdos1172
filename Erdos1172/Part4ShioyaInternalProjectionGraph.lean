/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-! # Named projection graphs, points, and regular-open word fibers -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal
open ErdosRelationGraph
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

abbrev inc (F x y : N) : B := pair x y ∈ᴮ F

/-- A subguard formulation of Boolean implication. -/
theorem projection_imp {Γ h k : B} :
    Γ ≤ h ⟹ k ↔ ∀ Δ ≤ Γ, Δ ≤ h → Δ ≤ k := by
  rw [← deduction]
  exact ⟨fun H _ a b => (le_inf a b).trans H,fun H => H _ inf_le_left inf_le_right⟩

def projectionIdentity (P : N) : N := relationGraph P P (fun x y => x =ᴮ y)

theorem projectionIdentity_pair {Γ : B} {P x y : N} :
    Γ ≤ pair x y ∈ᴮ projectionIdentity P ↔ Γ ≤ x ∈ᴮ P ∧ Γ ≤ y ∈ᴮ P ∧ Γ ≤ x =ᴮ y :=
  mem_relationGraph_iff (fun _ => B_ext_bv_eq_left) (fun _ => B_ext_bv_eq_right)

theorem projectionIdentity_is_function (P : N) {Γ : B} :
    Γ ≤ is_function P P (projectionIdentity P) := by
  apply relationGraph_is_function (fun _ => B_ext_bv_eq_left) (fun _ => B_ext_bv_eq_right)
  · exact le_iInf fun x => projection_imp.mpr fun _ _ hx => le_iSup_of_le x (le_inf hx bv_refl)
  · intro _ _ _ _ _ _ _ _ _ _ h₁ h₂ h
    exact bv_trans (bv_symm h₁) (bv_trans h h₂)

/-- The domain D is dense in P. -/
def projectionDense (P R D : N) : B :=
  ⨅ p : N, (p ∈ᴮ P) ⟹ ⨆ x : N, (x ∈ᴮ D) ⊓ inc R x p

def projectionMonotone (R S F : N) : B :=
  ⨅ x : N, ⨅ y : N, ⨅ a : N, ⨅ b : N,
    (inc F x a ⊓ inc F y b ⊓ inc R x y) ⟹ inc S a b

/-- The image is cofinal towards stronger conditions. -/
def projectionReaches (Q S F : N) : B :=
  ⨅ q : N, (q ∈ᴮ Q) ⟹ ⨆ x : N, ⨆ a : N, inc F x a ⊓ inc S a q

/-- Lifting a target strengthening allows its lifted image to be even stronger. -/
def projectionLifts (Q R S F : N) : B :=
  ⨅ x : N, ⨅ a : N, ⨅ q : N, (inc F x a ⊓ (q ∈ᴮ Q) ⊓ inc S q a) ⟹
    ⨆ y : N, ⨆ b : N, inc F y b ⊓ inc R y x ⊓ inc S b q

/-- Test the distinguished points on every domain refinement of the source point. -/
def pointTest (R S F p q : N) : B :=
  ⨅ x : N, ⨅ y : N, (inc F x y ⊓ inc R x p) ⟹ inc S y q

/-- A word names its regular open fiber by pairs (condition, ordinal).
Only the cone at the distinguished point and the old coordinates are tested. -/
def wordTest (R F p newLen newBits oldLen oldBits : N) : B :=
  (oldLen ⊆ᴮ newLen) ⊓ ⨅ x : N, ⨅ y : N, ⨅ i : N,
    (inc F x y ⊓ inc R x p ⊓ (i ∈ᴮ oldLen)) ⟹
      ((inc newBits x i ⟹ inc oldBits y i) ⊓ (inc oldBits y i ⟹ inc newBits x i))

private theorem change_first {Δ : B} {R x y a : N} (he : Δ ≤ x =ᴮ y) (h : Δ ≤ inc R x a) :
    Δ ≤ inc R y a := bv_rw'' he h B_ext_pair_mem_left

private theorem change_second {Δ : B} {R x y a : N} (he : Δ ≤ x =ᴮ y) (h : Δ ≤ inc R a x) :
    Δ ≤ inc R a y := bv_rw'' he h B_ext_pair_mem_right

theorem projectionIdentity_base (P R : N) {Γ : B}
    (refl : ∀ {Δ : B}, Δ ≤ Γ → ∀ {p : N}, Δ ≤ p ∈ᴮ P → Δ ≤ pair p p ∈ᴮ R) :
    Γ ≤ projectionDense P R P ⊓ projectionMonotone R R (projectionIdentity P) ⊓
      projectionReaches P R (projectionIdentity P) ⊓ projectionLifts P R R (projectionIdentity P) := by
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · exact le_iInf fun p => projection_imp.mpr fun _ h hp => le_iSup_of_le p (le_inf hp (refl h hp))
  · exact le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
      projection_imp.mpr fun _ _ h => change_second
        (projectionIdentity_pair.mp (h.trans (inf_le_left.trans inf_le_right))).2.2
        (change_first (projectionIdentity_pair.mp (h.trans (inf_le_left.trans inf_le_left))).2.2
          (h.trans inf_le_right))
  · exact le_iInf fun p => projection_imp.mpr fun _ h hp => le_iSup_of_le p (le_iSup_of_le p
      (le_inf (projectionIdentity_pair.mpr ⟨hp,hp,bv_refl⟩) (refl h hp)))
  · apply le_iInf
    intro x
    apply le_iInf
    intro a
    apply le_iInf
    intro q
    apply projection_imp.mpr
    intro Δ hΔ h
    have hq := h.trans (inf_le_left.trans inf_le_right)
    have hx := projectionIdentity_pair.mp (h.trans (inf_le_left.trans inf_le_left))
    exact le_iSup_of_le q (le_iSup_of_le q (le_inf
      (le_inf (projectionIdentity_pair.mpr ⟨hq,hq,bv_refl⟩) (change_second (bv_symm hx.2.2) (h.trans inf_le_right)))
      (refl hΔ hq)))

theorem projectionIdentity_point (P R p : N) {Γ : B} :
    Γ ≤ pointTest R R (projectionIdentity P) p p :=
  le_iInf fun _ => le_iInf fun _ => projection_imp.mpr fun _ _ h =>
    change_first (projectionIdentity_pair.mp (h.trans inf_le_left)).2.2 (h.trans inf_le_right)

theorem projectionIdentity_word (P R p len bits : N) {Γ : B} :
    Γ ≤ wordTest R (projectionIdentity P) p len bits len bits := by
  refine le_inf subset_self (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => projection_imp.mpr ?_)
  intro Δ _ h
  have he := (projectionIdentity_pair.mp (h.trans (inf_le_left.trans inf_le_left))).2.2
  exact le_inf (projection_imp.mpr fun _ h' hb => change_first (h'.trans he) hb)
    (projection_imp.mpr fun _ h' hb => change_first (bv_symm (h'.trans he)) hb)

end bSet.ErdosShioyaInternal
