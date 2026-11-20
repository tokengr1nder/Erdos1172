/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenIteration

@[expose] public section

/-!
# Ground capture of an internally countable set under a strict chain condition

The support consists of all ground labels whose membership is possible below
the original Boolean condition. An actual internal injection into omega and
regular-cardinal pigeonhole bound this whole support, not just the labels
decided by one strengthening. Distinct labels must be extensionally separated.

The resulting ground pre-set captures the given internal set at the SAME
Boolean condition. No nonzero-condition or nonempty-ground-set hypothesis is
needed. The concrete specialization uses the first Levy algebra's strict
kappa-chain condition; it does not assert that condition for the final
Levy--Cohen algebra or recover arbitrary ordinal sequences from real reading.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableGroundCapture

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Ground labels with nonzero possible membership below the fixed condition. -/
def possibleMembers (A : PSet.{u}) (D : bSet B) (Γ : B) : Set A.Type :=
  {i | Γ ⊓ check (A.Func i) ∈ᴮ D ≠ ⊥}

/-- A positive membership piece in the domain of an internal injection has
a positive pair at some natural index. This chooses only a positive piece,
not a ground natural that represents the whole mixed internal value. -/
theorem positive_natural_injection_pair {D f x : bSet B} {Γ : B}
    (Hf : Γ ≤ is_injective_function D omega f)
    (Hpositive : Γ ⊓ x ∈ᴮ D ≠ ⊥) :
    ∃ n : (omega : bSet B).type,
      ⊥ < is_inj f ⊓ pair x ((omega : bSet B).func n) ∈ᴮ f := by
  have Htotal : Γ ≤ is_total D omega f :=
    is_total_of_is_function (Hf.trans inf_le_left)
  have Himage : Γ ⊓ x ∈ᴮ D ≤
      ⨆ y : bSet B, y ∈ᴮ omega ⊓ pair x y ∈ᴮ f :=
    (le_inf (inf_le_left.trans (Htotal.trans (iInf_le _ x)))
      inf_le_right).trans bv_imp_elim
  rw [← @bounded_exists B _ omega (fun y => pair x y ∈ᴮ f)
    (h_congr := B_ext_pair_mem_right)] at Himage
  have Hpos : ⊥ < ⨆ n : (omega : bSet B).type,
      is_inj f ⊓ pair x ((omega : bSet B).func n) ∈ᴮ f := by
    apply (bot_lt_iff_ne_bot.mpr Hpositive).trans_le
    calc
      Γ ⊓ x ∈ᴮ D ≤ is_inj f ⊓
          ⨆ n : (omega : bSet B).type,
            pair x ((omega : bSet B).func n) ∈ᴮ f :=
        le_inf (inf_le_left.trans (Hf.trans inf_le_right))
          (Himage.trans (iSup_mono (fun _ => inf_le_right)))
      _ = ⨆ n : (omega : bSet B).type,
          is_inj f ⊓ pair x ((omega : bSet B).func n) ∈ᴮ f := inf_iSup_eq'
  exact nonzero_wit Hpos

/-- The full ground support of possible membership is small. There is no
assumption that the internal set is contained in the checked ground set. -/
theorem possible_members_cardinal_lt {κ : Cardinal.{u}}
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (Hcc : ∀ {J : Type u} (w : J → B), (∀ j, w j ≠ ⊥) →
      (∀ j k, j ≠ k → w j ⊓ w k = ⊥) → Cardinal.mk J < κ)
    (A : PSet.{u}) {D : bSet B} {Γ : B}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (Hcount : Γ ≤ injects_into D omega) :
    Cardinal.mk (possibleMembers A D Γ) < κ := by
  classical
  obtain ⟨f, Hf⟩ := exists_convert (injection_into_of_injects_into Hcount)
    ErdosSmallFiberBound.B_ext_injective_code
  have Hpositive : ∀ i : possibleMembers A D Γ,
      ∃ n : (omega : bSet B).type,
        ⊥ < is_inj f ⊓ pair (check (A.Func i.val))
          ((omega : bSet B).func n) ∈ᴮ f := by
    intro i
    exact positive_natural_injection_pair Hf i.property
  obtain ⟨g, Hg⟩ := Classical.axiomOfChoice Hpositive
  by_contra Hlarge
  have Hsize : Cardinal.mk (omega : bSet B).type < κ.ord.cof := by
    change Cardinal.mk (ULift.{u} ℕ) < κ.ord.cof
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0,
      Hκ.cof_ord] using Hunc
  obtain ⟨n, Hn⟩ := Cardinal.infinite_pigeonhole_card g κ
    (le_of_not_gt Hlarge) Hκ.aleph0_le Hsize
  let w : (g ⁻¹' {n}) → B := fun i =>
    is_inj f ⊓ pair (check (A.Func i.val.val))
      ((omega : bSet B).func (g i.val)) ∈ᴮ f
  have Hpos : ∀ i, w i ≠ ⊥ := fun i => ne_of_gt (Hg i.val)
  have Hdisj : ∀ i j, i ≠ j → w i ⊓ w j = ⊥ := by
    intro i j Hij
    apply eq_bot_iff.mpr
    have Hinj : w i ⊓ w j ≤ is_inj f := inf_le_left.trans inf_le_left
    have Hi : w i ⊓ w j ≤ pair (check (A.Func i.val.val))
        ((omega : bSet B).func (g i.val)) ∈ᴮ f :=
      inf_le_left.trans inf_le_right
    have Hj : w i ⊓ w j ≤ pair (check (A.Func j.val.val))
        ((omega : bSet B).func (g j.val)) ∈ᴮ f :=
      inf_le_right.trans inf_le_right
    have hi : g i.val = n := i.property
    have hj : g j.val = n := j.property
    rw [hi] at Hi
    rw [hj] at Hj
    have Heq : w i ⊓ w j ≤
        check (A.Func i.val.val) =ᴮ check (A.Func j.val.val) :=
      eq_of_is_inj_of_eq Hinj bv_refl Hi Hj
    exact Heq.trans_eq (check_bv_eq_bot_of_not_equiv
      (Hsep _ _ (fun h => Hij (Subtype.ext (Subtype.ext h)))))
  exact (Hcc w Hpos Hdisj).not_ge Hn

/-- The actual ground set of all possibly present labels. -/
def groundCapture (A : PSet.{u}) (D : bSet B) (Γ : B) : PSet.{u} :=
  PSet.mk (possibleMembers A D Γ) (fun i => A.Func i.val)

theorem groundCapture_subset (A : PSet.{u}) (D : bSet B) (Γ : B) :
    groundCapture A D Γ ⊆ A := by
  intro i
  exact ⟨i.val, PSet.Equiv.refl _⟩

theorem checked_member_groundCapture (A : PSet.{u}) (D : bSet B) (Γ : B)
    (i : A.Type) :
    Γ ⊓ check (A.Func i) ∈ᴮ D ≤ check (A.Func i) ∈ᴮ check (groundCapture A D Γ) := by
  classical
  by_cases Hi : Γ ⊓ check (A.Func i) ∈ᴮ D = ⊥
  · exact Hi.le.trans bot_le
  · exact check_mem (PSet.func_mem (groundCapture A D Γ) ⟨i, Hi⟩)

/-- The original condition, not merely a nonzero strengthening, forces the
whole internal set into its ground capture. This does not need a chain
condition, cardinal bound, countability, or separation of ground labels. -/
theorem subset_check_groundCapture (A : PSet.{u}) {D : bSet B} {Γ : B}
    (HS : Γ ≤ D ⊆ᴮ check A) :
    Γ ≤ D ⊆ᴮ check (groundCapture A D Γ) := by
  have Hlabels : Γ ≤ ⨅ x : bSet B,
      _root_.imp (x ∈ᴮ check A)
        (_root_.imp (x ∈ᴮ D) (x ∈ᴮ check (groundCapture A D Γ))) := by
    rw [← @bounded_forall B _ (check A)
      (fun x => _root_.imp (x ∈ᴮ D) (x ∈ᴮ check (groundCapture A D Γ)))
      (h_congr := B_ext_imp (h₁ := B_ext_mem_left) (h₂ := B_ext_mem_left))]
    apply le_iInf
    intro i
    simp only [check_bval_top, top_imp, check_func]
    rw [← deduction]
    exact checked_member_groundCapture A D Γ (check_cast i)
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have HxA : Γ ⊓ x ∈ᴮ D ≤ x ∈ᴮ check A :=
    mem_of_mem_subset (inf_le_left.trans HS) inf_le_right
  have Himp : Γ ⊓ x ∈ᴮ D ≤
      _root_.imp (x ∈ᴮ D) (x ∈ᴮ check (groundCapture A D Γ)) :=
    (le_inf (inf_le_left.trans (Hlabels.trans (iInf_le _ x))) HxA).trans bv_imp_elim
  exact (le_inf Himp inf_le_right).trans bv_imp_elim

theorem groundCapture_cardinal_lt {κ : Cardinal.{u}}
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (Hcc : ∀ {J : Type u} (w : J → B), (∀ j, w j ≠ ⊥) →
      (∀ j k, j ≠ k → w j ⊓ w k = ⊥) → Cardinal.mk J < κ)
    (A : PSet.{u}) {D : bSet B} {Γ : B}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (Hcount : Γ ≤ injects_into D omega) :
    Cardinal.mk (groundCapture A D Γ).Type < κ :=
  possible_members_cardinal_lt Hκ Hunc Hcc A Hsep Hcount

/-- Actual same-condition ground capture, including bottom conditions and
empty ground families. -/
theorem exists_ground_capture {κ : Cardinal.{u}}
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (Hcc : ∀ {J : Type u} (w : J → B), (∀ j, w j ≠ ⊥) →
      (∀ j k, j ≠ k → w j ⊓ w k = ⊥) → Cardinal.mk J < κ)
    (A : PSet.{u}) {D : bSet B} {Γ : B}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (Hcount : Γ ≤ injects_into D omega) (HS : Γ ≤ D ⊆ᴮ check A) :
    ∃ A₀ : PSet.{u}, Cardinal.mk A₀.Type < κ ∧ A₀ ⊆ A ∧ Γ ≤ D ⊆ᴮ check A₀ :=
  ⟨groundCapture A D Γ, groundCapture_cardinal_lt Hκ Hunc Hcc A Hsep Hcount,
    groundCapture_subset A D Γ, subset_check_groundCapture A HS⟩

end bSet.ErdosCountableGroundCapture

namespace Erdos1172LevyCohen

open bSet bSet.ErdosCountableGroundCapture

/-- The first-stage strict chain condition captures every internally
countable checked-ground subset in a ground family of cardinal below κ. -/
theorem firstStage_exists_countable_ground_capture (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (A : PSet.{u}) {D : bSet (FirstAlgebra κ)} {Γ : FirstAlgebra κ}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (Hcount : Γ ≤ injects_into D omega) (HS : Γ ≤ D ⊆ᴮ check A) :
    ∃ A₀ : PSet.{u}, Cardinal.mk A₀.Type < κ ∧ A₀ ⊆ A ∧ Γ ≤ D ⊆ᴮ check A₀ :=
  exists_ground_capture Hκ Hunc
    (fun w Hpos Hdisj =>
      Erdos1172LevyCollapse.below_completion_disjoint_family_cardinal_lt
        κ Hκ Hunc w Hpos Hdisj) A Hsep Hcount HS

end Erdos1172LevyCohen
