/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationFixedSubsets

@[expose] public section

/-! # The preparation image of a name given by fewer than κ coefficients -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport Erdos1172GroundUltrapower Erdos1172BooleanUltrapower Erdos1172LevyCohen
open scoped Flypitch
universe u
namespace Erdos1172BooleanUltrapower
variable {I V J : Type u} [NontrivialCompleteBooleanAlgebra V] (U : Ultrafilter I) (κ : Cardinal.{u})
variable [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ]

/-- In a small presentation the hereditary image has the actual images of
the indicated children and coefficients, including variable children. -/
theorem hereditary_small_family (small : Cardinal.mk J < κ) (f : I → J → bSet V) (w : I → J → V) :
    (⊤ : Algebra U V) ≤ hereditary U (fun i => .mk J (f i) (w i)) =ᴮ
      .mk J (fun k => hereditary U (fun i => f i k)) (fun k => value U (fun i => w i k)) := by
  apply subset_ext
  · apply hereditary_subset_test
    intro Z
    change value U (fun i => ⨆ k : J, w i k ⊓ (Z i =ᴮ f i k)) ≤
      ⨆ k : J, value U (fun i => w i k) ⊓ (hereditary U Z =ᴮ hereditary U (fun i => f i k))
    rw [value_small_iSup U κ small]
    apply iSup_mono
    intro k
    exact ((value_inf U _ _).trans (congrArg (fun t => value U (fun i => w i k) ⊓ t)
      (value_name_eq U Z (fun i => f i k)))).le
  · rw [subset_unfold]
    apply le_iInf
    intro k
    rw [← deduction,top_inf_eq]
    apply (value_name_mem U (fun i => f i k) (fun i => .mk J (f i) (w i))).le.trans'
    exact (value_le_value_iff U).mpr (Eventually.of_forall fun i => mem_mk' (.mk J (f i) (w i)) k)

end Erdos1172BooleanUltrapower

namespace Erdos1172LevyCollapse.Preparation
variable {I J : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "j" => preparedName U a hk hf hn ht
local notation "inc" => initialCollapseHom hk
variable (hκ : κ.IsRegular) (hu : Cardinal.aleph0 < κ)

include hκ hu in
theorem prepared_small_family (small : Cardinal.mk J < κ) (f : J → bSet A) (w : J → A) :
    (⊤ : B) ≤ j (.mk J f w) =ᴮ .mk J (fun k => j (f k)) (fun k => inc (w k)) := by
  let φ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U A) B := collapseCompletionIso U a hk hf hn ht
  have h := OrderHomClass.mono φ (hereditary_small_family U κ small (fun _ => f) (fun _ => w))
  rw [TopHomClass.map_top φ,map_bv_eq φ,mapNames_mk] at h
  change (⊤ : B) ≤ j (.mk J f w) =ᴮ .mk J (fun k => j (f k)) (fun k => (collapseCompletionIso U a hk hf hn ht)
    (value U (fun _ => w k))) at h
  have ew : (fun k => (collapseCompletionIso U a hk hf hn ht) (value U (fun _ => w k))) = (fun k => inc (w k)) :=
    funext fun k => collapseCompletionIso_constant U a hk hf hn ht hκ hu (w k)
  rwa [ew] at h

private theorem same_coefficients {V : Type u} [NontrivialCompleteBooleanAlgebra V]
    (f g : J → bSet V) (w : J → V) (eq : ∀ k, (⊤ : V) ≤ f k =ᴮ g k) :
    (⊤ : V) ≤ (.mk J f w : bSet V) =ᴮ .mk J g w := by
  apply subset_ext <;> rw [subset_unfold] <;> apply le_iInf <;> intro k <;> rw [← deduction,top_inf_eq]
  · exact subst_congr_mem_left' (bv_symm (le_top.trans (eq k))) (mem_mk' (.mk J g w) k)
  · exact subst_congr_mem_left' (le_top.trans (eq k)) (mem_mk' (.mk J f w) k)

include hκ hu in
theorem prepared_fixed_small_subset (S : PSet.{u}) (small : Cardinal.mk S.Type < κ)
    (fixed : ∀ k, (⊤ : B) ≤ j (check (S.Func k)) =ᴮ check (S.Func k)) (X : bSet A) :
    inc (X ⊆ᴮ check S) ≤ j X =ᴮ mapNames inc X := by
  let w (k : S.Type) : A := check (S.Func k) ∈ᴮ X
  let Y := ErdosCheckedIndicator.checkedIndicator S w
  have same : (X ⊆ᴮ check S) ≤ X =ᴮ Y := by
    rw [show Y = ErdosCheckedIndicator.checkedIndicator S w from rfl,
      show w = (fun k => check (S.Func k) ∈ᴮ X) from rfl, ErdosCheckedIndicator.checkedIndicator_membership_eq]
    exact eq_membership_indicator_of_subset le_rfl
  have good : (⊤ : B) ≤ j Y =ᴮ mapNames inc Y := by
    apply bv_trans (prepared_small_family U a hk hf hn ht hκ hu small (fun k => check (S.Func k)) w)
    apply same_coefficients
    intro k
    rw [map_check]
    exact fixed k
  exact bv_trans (((OrderHomClass.mono inc same).trans_eq (prepared_eq U a hk hf hn ht hκ hu X Y).symm))
    (bv_trans (le_top.trans good) (bv_symm ((OrderHomClass.mono inc same).trans_eq (map_bv_eq inc X Y))))
end Erdos1172LevyCollapse.Preparation
