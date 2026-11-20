/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4RelativeValuationNormality

@[expose] public section

/-! # The internal partition theorem from seed values in a small residual forcing -/

set_option autoImplicit false
noncomputable section
open bSet ErdosIdeal ErdosDenseBasis ErdosOmegaTwo Erdos1172SeedQuotient
open scoped Flypitch
universe u
namespace Erdos1172RelativeValuation

private theorem equal_of_mem_values {B : Type u} [NontrivialCompleteBooleanAlgebra B] {X Y : bSet B}
    (h : ∀ z : bSet B, (z ∈ᴮ X) = (z ∈ᴮ Y)) : (⊤ : B) ≤ X =ᴮ Y := by
  apply subset_ext <;> rw [subset_unfold'] <;> apply le_iInf <;> intro z <;> rw [← deduction,top_inf_eq,h z]

private theorem diagonalClosure_base {B : Type u} [NontrivialCompleteBooleanAlgebra B] {K V J : bSet B}
    (eq : (⊤ : B) ≤ K =ᴮ V) : diagonalClosure V J = diagonalClosure K J := by
  have mem (z : bSet B) : (z ∈ᴮ V) = (z ∈ᴮ K) :=
    bv_rw (top_unique eq) (fun v => z ∈ᴮ v) (h_congr := B_ext_mem_right)
  have big (R : bSet B) : (⊤ : B) ≤ diagonalUnion V R =ᴮ diagonalUnion K R := by
    apply equal_of_mem_values
    intro z
    simp only [mem_diagonalUnion,mem]
  have one (R i : bSet B) : (⊤ : B) ≤ fiber V R i =ᴮ fiber K R i := by
    apply equal_of_mem_values
    intro z
    simp only [mem_fiber,mem]
  have bm (R : bSet B) : (diagonalUnion V R ∈ᴮ J) = (diagonalUnion K R ∈ᴮ J) :=
    (bv_rw (top_unique (big R)) (fun v => v ∈ᴮ J) (h_congr := B_ext_mem_left)).symm
  have sm (R i : bSet B) : (fiber V R i ∈ᴮ J) = (fiber K R i ∈ᴮ J) :=
    (bv_rw (top_unique (one R i)) (fun v => v ∈ᴮ J) (h_congr := B_ext_mem_left)).symm
  simp only [diagonalClosure,mem,bm,sm]

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (κ : Cardinal.{u}) (e : CompleteLatticeHom B C) (he : Function.Injective e)
  (μ : BoundedLatticeHom (κ.ord.ToType → B) C) (scalar : ∀ b : B, μ (fun _ => b) = e b)
  (initial : ∀ i : κ.ord.ToType, μ (initialValue κ i) = ⊥)
  (normal : ∀ F : κ.ord.ToType → κ.ord.ToType → B, μ (diagonal κ F) ≤ ⨆ i, μ (F i))
  (d : κ.ord.ToType → C) (dense : denseOver e d)
local notation "K" => (check (PSet.ordinalMk κ.ord) : bSet B)

include he scalar initial normal dense in
/-- Construct every internal ideal and basis field required by Part 4. The
valuation acts on membership coefficients of arbitrary source names. -/
theorem internal_ideal_and_basis (hk : Cardinal.aleph0 < κ) (hk1 : (⊤ : B) ≤ K =ᴮ omegaOne) :
    ∃ J I D : bSet B, (⊤ : B) ≤ properIdeal omegaOne J ∧ (⊤ : B) ≤ countableAbsorption omegaOne J ∧
      (⊤ : B) ≤ countableClosure J ∧ (⊤ : B) ≤ diagonalClosure omegaOne J ∧
      (⊤ : B) ≤ is_function I (bv_powerset omegaOne) D ∧ (⊤ : B) ≤ positiveValues omegaOne J I D ∧
      (⊤ : B) ≤ denseValues omegaOne J I D ∧ (⊤ : B) ≤ injects_into I omegaOne := by
  let J := idealName κ e μ
  obtain ⟨I,D,funct,hp,hd,hi⟩ := exists_internal_basis κ e μ scalar κ d dense
    (fun F => ⟨diagonal κ F,diagonal_value κ μ initial normal F⟩) hk1
  have sub (X : bSet B) : (X ⊆ᴮ omegaOne) = (X ⊆ᴮ K) :=
    bv_rw (top_unique hk1) (fun v => X ⊆ᴮ v) (h_congr := B_ext_subset_right)
  have pow := bv_powerset_congr hk1
  have subpow : (J ⊆ᴮ bv_powerset omegaOne) = (J ⊆ᴮ bv_powerset K) :=
    bv_rw (top_unique pow) (fun v => J ⊆ᴮ v) (h_congr := B_ext_subset_right)
  have mem : (omegaOne ∈ᴮ J) = (K ∈ᴮ J) :=
    bv_rw (top_unique hk1) (fun v => v ∈ᴮ J) (h_congr := B_ext_mem_left)
  have pos (X : bSet B) : positive omegaOne J X = positive K J X := by rw [positive,positive,sub]
  refine ⟨J,I,D,?_,?_,idealName_countableClosure κ e μ scalar initial normal hk,?_,?_,?_,?_,hi⟩
  · simpa only [properIdeal,isIdeal,subpow,mem] using
      (show (⊤ : B) ≤ properIdeal K J from idealName_proper κ e μ scalar he)
  · simpa only [countableAbsorption,sub] using (idealName_countableAbsorption κ e μ scalar initial normal hk)
  · rw [diagonalClosure_base hk1]
    exact idealName_diagonalClosure κ e μ scalar normal
  · exact ErdosIndependentHomogeneous.is_function_codomain_mono (subset_of_eq pow) funct
  · simpa only [positiveValues,pos] using (show (⊤ : B) ≤ positiveValues K J I D from hp)
  · simpa only [denseValues,pos] using (show (⊤ : B) ≤ denseValues K J I D from hd)

end Erdos1172RelativeValuation
