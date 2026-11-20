/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationNames
public import Erdos1172.Part4BooleanCheckedIndicatorAgreement

@[expose] public section

/-! # Agreement with initial-collapse transport for all mixed bounded subsets -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport ErdosCheckedIndicator Erdos1172GroundUltrapower
open Erdos1172BooleanUltrapower Erdos1172LevyCohen
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "j" => preparedName U a hk hf hn ht
local notation "inc" => initialCollapseHom hk
variable [CardinalInterFilter (U : Filter I) κ] (hκ : κ.IsRegular) (hu : Cardinal.aleph0 < κ)

theorem prepared_fixed_ordinal (β : Ordinal.{u}) (hβ : β < κ.ord) :
    (⊤ : B) ≤ j (check (PSet.ordinalMk β)) =ᴮ check (PSet.ordinalMk β) := by
  let φ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U A) B := collapseCompletionIso U a hk hf hn ht
  have h := OrderHomClass.mono φ (hereditary_fixed_checked_ordinal («B» := A) U κ β hβ)
  rwa [TopHomClass.map_top φ,map_bv_eq φ,map_check] at h

include hκ hu in
private theorem fixed_subsets (S : PSet.{u}) (fixS : (⊤ : B) ≤ j (check S) =ᴮ check S)
    (fixChild : ∀ i, (⊤ : B) ≤ j (check (S.Func i)) =ᴮ check (S.Func i)) (X : bSet A) :
    inc (X ⊆ᴮ check S) ≤ j X =ᴮ mapNames inc X := by
  let b := inc (X ⊆ᴮ check S)
  have h₁ : b ≤ j X ⊆ᴮ check S := by
    apply bv_rw'' (le_top.trans fixS) _ B_ext_subset_right
    exact (prepared_subset U a hk hf hn ht hκ hu X (check S)).ge
  have h₂ : b ≤ mapNames inc X ⊆ᴮ check S := by
    simpa only [map_check] using (map_subset inc X (check S)).le
  have row (i) : ((check (S.Func i) : bSet B) ∈ᴮ j X) = (check (S.Func i) ∈ᴮ mapNames inc X) := by
    have he : (j (check (S.Func i)) ∈ᴮ j X) = (check (S.Func i) ∈ᴮ j X) := le_antisymm
      (subst_congr_mem_left' (le_top.trans (fixChild i)) le_rfl)
      (subst_congr_mem_left' (bv_symm (le_top.trans (fixChild i))) le_rfl)
    calc
      _ = _ := he.symm
      _ = _ := prepared_mem U a hk hf hn ht hκ hu _ _
      _ = _ := by rw [map_mem inc,map_check]
  have rep (Y : bSet B) (hY : b ≤ Y ⊆ᴮ check S) :
      b ≤ Y =ᴮ checkedIndicator S (fun i => check (S.Func i) ∈ᴮ Y) := by
    rw [checkedIndicator_membership_eq]
    exact eq_membership_indicator_of_subset hY
  have eq := rep (j X) h₁
  simp_rw [row] at eq
  exact bv_trans eq (bv_symm (rep _ h₂))

include hκ hu in
/-- A name for an arbitrary subset of any ordinal below the original critical
cardinal has exactly its ordinary initial-collapse image, on its full support. -/
theorem prepared_bounded_subset (β : Ordinal.{u}) (hβ : β < κ.ord) (X : bSet A) :
    inc (X ⊆ᴮ check (PSet.ordinalMk β)) ≤ j X =ᴮ mapNames inc X := by
  apply fixed_subsets U a hk hf hn ht hκ hu _ (prepared_fixed_ordinal U a hk hf hn ht β hβ) _ X
  rw [PSet.ordinalMk_eq_def β]
  exact fun i => prepared_fixed_ordinal U a hk hf hn ht i.toOrd.val (i.toOrd.property.trans hβ)

private theorem mk_ofNat (n : ℕ) : ZFSet.mk (PSet.ofNat n) = (n : Ordinal.{u}).toZFSet := by
  induction n with
  | zero => exact Ordinal.toZFSet_zero.symm
  | succ n ih =>
    rw [Nat.cast_succ,Ordinal.toZFSet_add_one,← ih]
    rfl

private theorem omega_equiv : PSet.Equiv PSet.omega.{u} (PSet.ordinalMk Ordinal.omega0.{u}) := by
  apply PSet.equiv_iff_eq.mpr
  change ZFSet.mk PSet.omega = Ordinal.omega0.toZFSet
  ext z
  induction z using Quotient.inductionOn with
  | _ v =>
    change ZFSet.mk v ∈ ZFSet.mk PSet.omega ↔ ZFSet.mk v ∈ Ordinal.omega0.toZFSet
    rw [ZFSet.mk_mem_iff,Ordinal.mem_toZFSet_iff]
    constructor
    · rintro ⟨⟨n⟩,hn⟩
      exact ⟨n,Ordinal.natCast_lt_omega0 n,(ZFSet.sound hn).trans (mk_ofNat n) |>.symm⟩
    · rintro ⟨o,ho,he⟩
      obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp ho
      exact ⟨⟨n⟩,ZFSet.exact (he.symm.trans (mk_ofNat n).symm)⟩

include hκ hu in
/-- In particular every interpreted lower-collapse real is fixed in the larger collapse. -/
theorem prepared_real (X : bSet A) : inc (X ⊆ᴮ omega) ≤ j X =ᴮ mapNames inc X := by
  have hω : Ordinal.omega0 < κ.ord := by simpa only [← Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hu
  have sub : (X ⊆ᴮ omega) ≤ X ⊆ᴮ check (PSet.ordinalMk Ordinal.omega0) :=
    bv_rw'' (le_top.trans (check_bv_eq omega_equiv)) le_rfl B_ext_subset_right
  exact (OrderHomClass.mono inc sub).trans (prepared_bounded_subset U a hk hf hn ht hκ hu _ hω X)

end Erdos1172LevyCollapse.Preparation
