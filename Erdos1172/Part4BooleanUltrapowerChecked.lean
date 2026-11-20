/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerNames
public import Erdos1172.Part4GroundCheckedEmbedding

@[expose] public section

/-! # Hereditary Boolean ultrapowers of checked names

On families of checked names the hereditary lift represents the transitive
ground ultrapower. Each selected child is checked on a large set, and every
ground member in the collapse has an actual selection of weight top.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)

private theorem checked_child {x : bSet B} {A : PSet.{u}} (hx : x = check A) (k : x.type) :
    ∃ F : PSet.{u}, x.func k = check F ∧ F ∈ A := by
  subst x
  exact ⟨_, check_func, PSet.func_mem _ _⟩

private theorem checked_pick {x : bSet B} {A F : PSet.{u}} (hx : x = check A) (hF : F ∈ A) :
    ∃ k : x.type, ∃ D : PSet.{u}, x.func k = check D ∧ x.bval k = ⊤ ∧ PSet.Equiv D F := by
  subst x
  cases A with
  | mk T f =>
    obtain ⟨k, hk⟩ := PSet.mem_def.mp hF
    exact ⟨k, f k, rfl, rfl, PSet.Equiv.symm hk⟩

private theorem child_checked (X : I → bSet B) (A : I → PSet.{u})
    (hx : ∀ᶠ i in U, X i = check (A i)) (a : Children U X) :
    ∃ F : I → PSet.{u}, (∀ᶠ i in U, child U X a i = check (F i)) ∧
      ∀ᶠ i in U, F i ∈ A i := by
  classical
  let P (i : I) (F : PSet.{u}) := child U X a i = check F ∧ F ∈ A i
  have H : ∀ᶠ i in U, ∃ F, P i F := by
    filter_upwards [a.large, hx] with i hi hxi
    simpa only [P, child, dif_pos hi] using checked_child hxi (a.pick ⟨i, hi⟩)
  let F (i : I) := if hi : ∃ F, P i F then hi.choose else ∅
  have hf : ∀ᶠ i in U, P i (F i) := H.mono (fun i hi => by simpa only [F, dif_pos hi] using hi.choose_spec)
  exact ⟨F, hf.mono (fun _ hi => hi.1), hf.mono (fun _ hi => hi.2)⟩

private theorem select_checked_member (X : I → bSet B) (A F : I → PSet.{u})
    (hx : ∀ᶠ i in U, X i = check (A i)) (hF : ∀ᶠ i in U, F i ∈ A i) :
    ∃ a : Children U X, ∃ D : I → PSet.{u},
      (∀ᶠ i in U, child U X a i = check (D i)) ∧ (∀ᶠ i in U, weight U X a i = ⊤) ∧
      ∀ᶠ i in U, PSet.Equiv (D i) (F i) := by
  classical
  let good (i : I) := ∃ k : (X i).type, ∃ D : PSet.{u},
    (X i).func k = check D ∧ (X i).bval k = ⊤ ∧ PSet.Equiv D (F i)
  have hg : ∀ᶠ i in U, good i := (hx.and hF).mono (fun _ h => checked_pick h.1 h.2)
  let a : Children U X := ⟨{i | good i}, hg, fun t => t.property.choose⟩
  let D (i : I) := if hi : good i then hi.choose_spec.choose else ∅
  have hd : ∀ᶠ i in U, child U X a i = check (D i) ∧ weight U X a i = ⊤ ∧ PSet.Equiv (D i) (F i) :=
    hg.mono (fun i hi => by
      simpa only [child, weight, selected, a, D, Set.mem_ofPred_eq, dif_pos hi] using hi.choose_spec.choose_spec)
  exact ⟨a, D, hd.mono (fun _ h => h.1), hd.mono (fun _ h => h.2.1), hd.mono (fun _ h => h.2.2)⟩

variable [CountableInterFilter (U : Filter I)]

theorem liftName_checked_of_eventually {C : Type u} [NontrivialCompleteBooleanAlgebra C]
    (V : (I → B) → C) (hTop : ∀ w : I → B, (∀ᶠ i in U, w i = ⊤) → V w = ⊤)
    (X : I → bSet B) : ∀ A : I → PSet.{u}, (∀ᶠ i in U, X i = check (A i)) →
      (⊤ : C) ≤ liftName U V X =ᴮ check (groundPSet U A) := by
  induction X using (familyChild_wf U).induction with
  | h X ih =>
    intro A hx
    apply subset_ext
    · rw [liftName_eq U V X, subset_unfold]
      change (⊤ : C) ≤ ⨅ a : Children U X, _root_.imp (V (weight U X a))
        (liftName U V (child U X a) ∈ᴮ check (groundPSet U A))
      apply le_iInf; intro a; rw [← deduction]
      obtain ⟨F, hF, hm⟩ := child_checked U X A hx a
      have he := ih (child U X a) (child_lt U X a) F hF
      exact subst_congr_mem_left' (bv_symm (le_top.trans he))
        (check_mem ((groundPSet_mem_iff U F A).mpr hm))
    · rw [subset_unfold]
      apply le_iInf; intro k; rw [← deduction]
      let x := (groundPSet U A).Func (check_cast k)
      have hk : (check (groundPSet U A) : bSet C).func k = check x := check_func
      obtain ⟨F, hF, hf⟩ := (mem_groundPSet_rep U A x).mp (PSet.func_mem _ _)
      obtain ⟨a, D, hD, hw, hDF⟩ := select_checked_member U X A F hx hF
      have he := ih (child U X a) (child_lt U X a) D hD
      have hDx : PSet.Equiv (groundPSet U D) x := PSet.Equiv.trans ((groundPSet_equiv_iff U D F).mpr hDF) hf
      have hc : (⊤ : C) ≤ liftName U V (child U X a) =ᴮ check x := bv_trans he (check_bv_eq hDx)
      rw [hk, liftName_eq U V X, mem_unfold]
      apply le_iSup_of_le a
      change _ ≤ V (weight U X a) ⊓ (check x =ᴮ liftName U V (child U X a))
      rw [hTop _ hw]
      exact le_inf le_top (le_top.trans (bv_symm hc))

theorem liftName_checked (A : I → PSet.{u}) : (⊤ : Algebra U B) ≤
    liftName U (value U) (fun i => (check (A i) : bSet B)) =ᴮ check (groundPSet U A) :=
  liftName_checked_of_eventually U (value U) (fun w hw =>
    (value_eq_of_eventuallyEq U (f := w) (g := fun _ => ⊤) hw).trans (value_top U))
    _ A (Eventually.of_forall (fun _ => rfl))

end Erdos1172BooleanUltrapower
