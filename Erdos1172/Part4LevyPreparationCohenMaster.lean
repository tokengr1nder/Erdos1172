/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationCohenConditions
public import Erdos1172.Part4CohenIndexedBinaryAssignment
public import Erdos1172.Part4CohenBitAssignmentBridge

@[expose] public section

/-! # A single upper Cohen condition for matching lower generic bits -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport Erdos1172GroundUltrapower Erdos1172BooleanUltrapower Erdos1172LevyCohen
open Lattice ErdosOmegaTwo ErdosPartialInjection ErdosCohen Erdos1172PosetCompletion
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation

private theorem homInf {V Z : Type u} [CompleteLattice V] [CompleteLattice Z] (f : CompleteLatticeHom V Z) (x y : V) : f (x ⊓ y) = f x ⊓ f y := by
  rw [← sInf_pair,map_sInf,Set.image_pair,sInf_pair]

theorem subset_by_binary_pairs {E : Type u} [NontrivialCompleteBooleanAlgebra E]
    (S : PSet.{u}) (p q : bSet E) (Γ : E) (supported : Γ ≤ p ⊆ᴮ prod (check S) two)
    (one : ∀ i, Γ ⊓ (pair (check (S.Func i)) (1 : bSet E) ∈ᴮ p) ≤ pair (check (S.Func i)) (1 : bSet E) ∈ᴮ q)
    (zero : ∀ i, Γ ⊓ (pair (check (S.Func i)) (0 : bSet E) ∈ᴮ p) ≤ pair (check (S.Func i)) (0 : bSet E) ∈ᴮ q) :
    Γ ≤ p ⊆ᴮ q := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  let d := Γ ⊓ (z ∈ᴮ p)
  have cover : d ≤ z ∈ᴮ prod (check S) two := mem_of_mem_subset (inf_le_left.trans supported) inf_le_right
  cases S with
  | mk T f =>
    apply (le_inf (le_refl d) cover).trans
    rw [mem_unfold,inf_iSup_eq]
    apply iSup_le
    rintro ⟨i,k⟩
    let n := (two : bSet E).func k
    let y := pair (check (f i)) n
    let t := d ⊓ ((⊤ ⊓ (two : bSet E).bval k) ⊓ (z =ᴮ y))
    have eqn : t ≤ z =ᴮ y := inf_le_right.trans inf_le_right
    have mem : t ≤ y ∈ᴮ p := mem_congr eqn bv_refl (inf_le_left.trans inf_le_right)
    have read : Γ ⊓ (y ∈ᴮ p) ≤ y ∈ᴮ q := by
      rcases Erdos1172CohenIteration.two_child_eq_zero_or_one (B := E) k with h | h
      · unfold y n
        rw [h]
        exact zero i
      · unfold y n
        rw [h]
        exact one i
    exact mem_congr (bv_symm eqn) bv_refl ((le_inf (inf_le_left.trans inf_le_left) mem).trans read)

variable {I E : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
variable (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "j" => preparedName U a hk.le hf hn ht
local notation "inc" => initialCollapseHom hk.le
local notation "K" => PSet.ordinalMk κ.ord
local notation "Low" => Erdos1172CohenIteration.Conditions (omegaOne : bSet A)
local notation "nm" => Erdos1172BooleanNameIteration.name
local notation "bit" => Erdos1172CohenIteration.bitValue (omegaOne : bSet A)
variable (hκ : κ.IsRegular) (hu : Cardinal.aleph0 < κ) (hθ : θ.IsRegular)

omit [Nonempty θ.ord.ToType] in
include hk hu hθ in
theorem master_binary_condition (b : (PSet.ordinalMk κ.ord).Type → B) :
    (⊤ : B) ≤ ErdosCohen.condition omegaOne (indexedBinaryAssignment K b (PSet.ordinalMk_inj κ.ord)) := by
  have mem : (⊤ : B) ≤ check K ∈ᴮ omegaOne := mem_congr bv_refl
    (firstStage_checked_upper_eq_omegaOne θ hθ (hu.trans hk)) (check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr hk)))
  have sub := subset_of_mem_Ord mem omegaOne_Ord
  have func := indexedBinaryAssignment_is_function K b (PSet.ordinalMk_inj κ.ord)
  exact le_inf (subset_trans' (subset_prod_of_is_function func) (prod_domain_mono sub))
    (le_inf (func.trans (inf_le_left.trans inf_le_left)) (le_iSup_of_le (check K)
      (le_inf mem (injects_into_of_subset (subset_of_eq (graphDomain_eq_of_function sub func))))))

variable [NontrivialCompleteBooleanAlgebra E]
variable (l : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) E) (k : CompleteLatticeHom (FirstAlgebra θ) E)
variable (comm : ∀ x : FirstAlgebra κ, l (Erdos1172LevyCohen.firstStageHom κ x) = k (initialCollapseHom hk.le x))
variable (Γ : E) (b : (PSet.ordinalMk κ.ord).Type → FirstAlgebra θ)
variable (bits : ∀ i, Γ ⊓ l (Erdos1172CohenIteration.bitValue (omegaOne : bSet (FirstAlgebra κ)) (check ((PSet.ordinalMk κ.ord).Func i)) 1) = Γ ⊓ k (b i))

omit [Nonempty θ.ord.ToType] in
include comm in
private theorem transfer_bit (p : Low) (i : (K).Type) (n : bSet A) :
    l (Erdos1172PosetCompletion.condition p) ⊓ k (inc (pair (check ((K).Func i)) n ∈ᴮ nm p)) ≤
      l (bit (check ((K).Func i)) n) := by
  rw [← comm,← homInf l]
  apply OrderHomClass.mono l
  exact Erdos1172CohenIteration.condition_inf_firstStageHom_le_bitValue inf_le_right

include hκ hu comm bits in
/-- The graph of the matched bits itself extends every lower generic condition. -/
theorem indexed_cohen_master_extends : ∀ p : Low,
    Γ ⊓ l (Erdos1172PosetCompletion.condition p) ≤ mapNames k (j (nm p)) ⊆ᴮ
      mapNames k (indexedBinaryAssignment K b (PSet.ordinalMk_inj κ.ord)) := by
  intro p
  let lowerHom := Erdos1172LevyCohen.firstStageHom κ
  let v := Erdos1172PosetCompletion.condition p
  let d := Γ ⊓ l v
  have pv : v ≤ lowerHom p.value := (Erdos1172CohenIteration.condition_le_firstStageHom_iff _ _ _).mpr le_rfl
  have cp : p.value ≤ ErdosCohen.condition omegaOne (nm p) :=
    ErdosCohen.mem_conditions_iff.mp (Erdos1172BooleanNameIteration.name_mem p)
  have dv : d ≤ k (inc p.value) := inf_le_right.trans ((OrderHomClass.mono l pv).trans_eq (comm _))
  have fix := dv.trans ((OrderHomClass.mono k ((OrderHomClass.mono inc cp).trans
    (prepared_cohen_condition U a hk.le hf hn ht hκ hu (nm p)))).trans_eq (map_bv_eq k _ _))
  apply bv_rw'' (bv_symm fix) _ B_ext_subset_left
  let f := k.comp inc
  have nmEq : mapNames k (mapNames inc (nm p)) = mapNames f (nm p) := (mapNames_comp inc k _).symm
  rw [nmEq]
  have ordEq := firstStage_checked_upper_eq_omegaOne κ hκ hu
  have groundSupport : p.value ≤ nm p ⊆ᴮ prod (check K) two :=
    subset_trans' (cp.trans inf_le_left) (prod_domain_mono (subset_of_eq (bv_symm (le_top.trans ordEq))))
  have supp : d ≤ mapNames f (nm p) ⊆ᴮ prod (check K) two := by
    have h := dv.trans (OrderHomClass.mono f groundSupport)
    simpa only [map_subset,ErdosNameTransport.map_prod,map_check,show (two : bSet A) = check (PSet.ofNat 2) from rfl] using h
  apply subset_by_binary_pairs K _ _ d supp
  · intro i
    have heq : (pair (check ((K).Func i)) (1 : bSet E) ∈ᴮ mapNames f (nm p)) =
        f (pair (check ((K).Func i)) (1 : bSet A) ∈ᴮ nm p) := by rw [map_mem,map_pair,map_check,show mapNames f (1 : bSet A) = 1 from map_check f (PSet.ofNat 1)]
    have bit1 := transfer_bit hk l k comm p i (1 : bSet A)
    have mapped := OrderHomClass.mono k (indexedBinaryAssignment_one K b (PSet.ordinalMk_inj κ.ord) i)
    rw [map_mem,map_pair,map_check] at mapped
    rw [show mapNames k (1 : bSet B) = 1 from map_check k (PSet.ofNat 1)] at mapped
    exact (le_inf (inf_le_left.trans inf_le_left)
      ((le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans_eq heq)).trans bit1)).trans
      ((bits i).le.trans (inf_le_right.trans mapped))
  · intro i
    have heq : (pair (check ((K).Func i)) (0 : bSet E) ∈ᴮ mapNames f (nm p)) =
        f (pair (check ((K).Func i)) (0 : bSet A) ∈ᴮ nm p) := by rw [map_mem,map_pair,map_check,show mapNames f (0 : bSet A) = 0 from map_check f (PSet.ofNat 0)]
    have bit0 := transfer_bit hk l k comm p i (0 : bSet A)
    have zero : bit (check ((K).Func i)) 0 ≤ (bit (check ((K).Func i)) 1)ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr (Erdos1172CohenIteration.bitValue_zero_inf_one_eq_bot _ _).le)
    have between : Γ ⊓ (l (bit (check ((K).Func i)) 1))ᶜ = Γ ⊓ (k (b i))ᶜ := by
      have mask (x : E) : Γ ⊓ xᶜ = Γ ⊓ (Γ ⊓ x)ᶜ := by rw [compl_inf,inf_sup_left,inf_compl_eq_bot,bot_sup_eq]
      exact (mask _).trans ((congrArg (fun z => Γ ⊓ zᶜ) (bits i)).trans (mask _).symm)
    have mapped := OrderHomClass.mono k (indexedBinaryAssignment_zero K b (PSet.ordinalMk_inj κ.ord) i)
    rw [map_mem,map_pair,map_check,map_compl'] at mapped
    rw [show mapNames k (0 : bSet B) = 0 from map_check k (PSet.ofNat 0)] at mapped
    exact (le_inf (inf_le_left.trans inf_le_left)
      (((le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans_eq heq)).trans bit0).trans
        ((OrderHomClass.mono l zero).trans_eq (map_compl' l _)))).trans
      (between.le.trans (inf_le_right.trans mapped))

include hκ hu hθ comm bits in
/-- Under a two-sided reading of the lower generic bits, one actual upper
condition extends every prepared ground condition on its own generic cone. -/
theorem exists_joint_cohen_master :
    ∃ m : bSet B, (⊤ : B) ≤ ErdosCohen.condition omegaOne m ∧ ∀ p : Low,
      Γ ⊓ l (Erdos1172PosetCompletion.condition p) ≤ mapNames k (j (nm p)) ⊆ᴮ mapNames k m :=
  ⟨_,master_binary_condition hk hu hθ b,indexed_cohen_master_extends U a hk hf hn ht hκ hu l k comm Γ b bits⟩

end Erdos1172LevyCollapse.Preparation
