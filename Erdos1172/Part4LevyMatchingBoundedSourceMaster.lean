/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingSourceMaster
public import Erdos1172.Part4LevyMatchingCohenCarriers
public import Erdos1172.Part4LevyPreparationBoundedCohenConditions

@[expose] public section

/-! # The source master for the bounded preparation embedding -/

noncomputable section
set_option autoImplicit false
universe u
open Cardinal Filter bSet ErdosCohen ErdosNameTransport ErdosOmegaTwo ErdosPartialInjection
open Erdos1172GroundUltrapower Erdos1172LevyCohen Erdos1172PosetCompletion Erdos1172BooleanUltrapower
open scoped Flypitch Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching
variable {κ θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R]
  {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
  (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (g : ∀ i, CompleteLatticeHom (B i) R)
local notation "A" => FirstAlgebra κ
local notation "Z" => FirstAlgebra θ
local notation "E" => JointForcing R θ.ord.ToType
local notation "src" => jointSourceHom (R := R) θ.ord.ToType
local notation "S" => PSet.ordinalMk κ.ord
local notation "Low" => Erdos1172CohenIteration.Conditions (omegaOne : bSet A)
local notation "nm" => Erdos1172BooleanNameIteration.name

include g in
/-- The same height is the first uncountable ordinal in the matching source.
All mixed predecessors of the checked height are countable. -/
theorem source_height_eq_omegaOne (hθ : θ.IsInaccessible) (good : RegularCollapsingStages B)
    (cc : StrictCC R θ) : (⊤ : R) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne := by
  apply omegaOne_property_unique
  refine le_inf (check_Ord (PSet.Ord_mk θ.ord)) (le_inf ?_ ?_)
  · have no := ErdosCardinalPreservation.surjects_onto_eq_bot (B := R) hθ.isRegular cc
      PSet.omega (PSet.ordinalMk θ.ord) (by simpa only [PSet.mk_omega_eq_mk_omega] using hθ.aleph0_lt)
      (by simp only [PSet.ordinalMk_type,Cardinal.mk_ord_toType,le_refl]) (PSet.ordinalMk_inj _)
    obtain ⟨z,hz⟩ := PSet.exists_mem_of_nonzero hθ.isRegular.ord_pos
    have nonempty : (⊤ : R) ≤ exists_mem (check (PSet.ordinalMk θ.ord)) := le_iSup_of_le (check z) (check_mem hz)
    have bot := (surjects_onto_of_injects_into' (le_refl (injects_into (check (PSet.ordinalMk θ.ord)) (omega : bSet R)))
      (le_top.trans nonempty)).trans_eq no
    rw [bot_unique bot,compl_bot]
  · rw [PSet.ordinalMk_eq_def,check_unfold,← bounded_forall (h_congr := B_ext_injects_into_left)]
    change (⊤ : R) ≤ ⨅ i : θ.ord.ToType, _root_.imp ⊤ (injects_into (check (PSet.ordinalMk i.toOrd.val)) omega)
    simp only [top_imp]
    exact le_iInf fun i => omegaOne_member_injects
      (source_bounded_ordinal_mem_omegaOne g good _ i.toOrd.property)

include g in
theorem sourceCohenMaster_valid (hk : κ < θ) (good : RegularCollapsingStages B)
    (u : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) R) :
    (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u) := by
  have mem := source_bounded_ordinal_mem_omegaOne g good _ (Cardinal.ord_lt_ord.mpr hk)
  have sub := subset_of_mem_Ord mem omegaOne_Ord
  have func : (⊤ : R) ≤ is_function (check S) two (sourceCohenMaster u) :=
    indexedBinaryAssignment_is_function S _ (PSet.ordinalMk_inj _)
  exact le_inf (subset_trans' (subset_prod_of_is_function func) (prod_domain_mono sub))
    (le_inf (func.trans (inf_le_left.trans inf_le_left)) (le_iSup_of_le (check S)
      (le_inf mem (injects_into_of_subset (subset_of_eq (graphDomain_eq_of_function sub func))))))

variable {I : Type u} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
  [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
  (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
  (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
  (u : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) R)
local notation "boundedPrep" => Preparation.boundedPreparedName U a hk.le hf hn ht
local notation "fullPrep" => Preparation.preparedName U a hk.le hf hn ht

include hκ hθ in
/-- This master belongs to the source and works for the lift whose seed is
the checked critical ordinal in the bounded ultrapower. -/
theorem exists_matching_bounded_source_master
    (cc : StrictCC R θ) (dense : DenseStageUnion g) (good : RegularCollapsingStages B)
    (ginj : ∀ i, Function.Injective (g i)) (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x)
    (uinj : Function.Injective u) :
    ∃ K : CompleteLatticeHom Z E, Function.Injective K ∧
      (∀ x, K (initialCollapseHom hk.le x) = src (u (firstStageHom κ x))) ∧
      (⊤ : E) ≤ mapNames K (ErdosCohen.conditions omegaOne) =ᴮ mapNames (src) (ErdosCohen.conditions omegaOne) ∧
      (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u) ∧
      (∀ p : Low, src (u (condition p)) ≤ mapNames K (boundedPrep (nm p)) ⊆ᴮ mapNames (src) (sourceCohenMaster u)) ∧
      (⊤ : E) ≤ ⨆ m : {m : bSet Z // (⊤ : Z) ≤ ErdosCohen.condition omegaOne m},
        (mapNames (src) (sourceCohenMaster u) =ᴮ mapNames K m.val) := by
  obtain ⟨K,kin,square,read,readBack,extend,upper⟩ := exists_matching_source_master b g U a hk hκ hθ hf hn ht u cc dense good ginj gg uinj
  have same := matched_cohen_conditions_eq K (src) hθ.aleph0_lt
    (below_checked_upper_eq_omegaOne θ hθ.isRegular hθ.aleph0_lt) (source_height_eq_omegaOne g hθ good cc) readBack read
  refine ⟨K,kin,square,same,sourceCohenMaster_valid g hk good u,fun p => ?_,upper⟩
  let l := (src).comp u
  let inc := initialCollapseHom hk.le
  have cp := ErdosCohen.mem_conditions_iff.mp (Erdos1172BooleanNameIteration.name_mem p)
  have pv : condition p ≤ firstStageHom κ p.value :=
    (Erdos1172CohenIteration.condition_le_firstStageHom_iff _ _ _).mpr le_rfl
  have support : l (condition p) ≤ K (inc (ErdosCohen.condition omegaOne (nm p))) :=
    (OrderHomClass.mono l pv).trans ((square _).symm.le.trans (OrderHomClass.mono K (OrderHomClass.mono inc cp)))
  have eq : l (condition p) ≤ mapNames K (boundedPrep (nm p)) =ᴮ mapNames K (fullPrep (nm p)) := by
    apply support.trans
    rw [← map_bv_eq K]
    apply OrderHomClass.mono K
    exact bv_trans (Preparation.boundedPrepared_cohen_condition U a hk.le hf hn ht hκ _)
      (bv_symm (Preparation.prepared_cohen_condition U a hk.le hf hn ht hκ.isRegular hκ.aleph0_lt _))
  exact subset_trans' (subset_of_eq eq) (extend p)

end Erdos1172LevyCollapse.Matching
