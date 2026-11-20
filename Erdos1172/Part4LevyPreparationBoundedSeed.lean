/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationBoundedChecked
public import Erdos1172.Part4ShioyaUltrapowerSeedDecision

@[expose] public section

/-! # Prepared critical-seed evaluation in the bounded ultrapower -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport Erdos1172GroundUltrapower Erdos1172Shioya.UltrapowerStage
open Erdos1172LevyCohen Erdos1172BooleanUltrapower ErdosOmegaTwo
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a)
variable (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "T" => Erdos1172BooleanUltrapower.Algebra U A
local notation "liftF" => boundedName (κ := κ) U a
local notation "φ" => collapseCompletionIso U a hk.le hf hn ht
local notation "hom" => ((φ) : CompleteLatticeHom T B)
local notation "j" => boundedPreparedName U a hk.le hf hn ht
local notation "seed" => criticalOrdinalPoint U a hf hn ht hk

include hκ in
theorem boundedPrepared_ordinal (o : Ordinal.{u}) : (⊤ : B) ≤
    j (check (PSet.ordinalMk o)) =ᴮ check (PSet.ordinalMk (ordinalImage U a o)) := by
  apply bv_trans (boundedPrepared_checked U a hk.le hf hn ht hκ (PSet.ordinalMk o))
  apply check_bv_eq
  apply PSet.equiv_iff_eq.mpr
  exact (ZFSet.mk_out _).trans (ordinalImage_code U a o).symm

include hκ in
/-- Arbitrary lower-collapse subsets are tested at the very same bounded
critical ordinal point used in the stage master construction. -/
theorem boundedPrepared_seed_trace (X : bSet A) :
    ((check (PSet.ordinalMk κ.ord) : bSet B) ∈ᴮ j X) =
      φ (value U (fun i => (check (PSet.ordinalMk (repr U a seed i).toOrd.val) : bSet A) ∈ᴮ X)) := by
  let o (i : I) := (repr U a seed i).toOrd.val
  let S (i : I) := PSet.ordinalMk (o i)
  have supp : Supported U a S := ⟨(seed).property.choose,
    fun t => PSet.ordinalMk (((seed).property.choose_spec.choose t).toOrd.val),EventuallyEq.rfl⟩
  let v : BoundedHull U θ a := ⟨Germ.map ordinalLabel (seed).val,by
    obtain ⟨η,g,hg⟩ := (seed).property
    exact ⟨η,ordinalLabel ∘ g,congrArg (Germ.map ordinalLabel) hg⟩⟩
  have hw : Germ.ofFun (fun i => ZFSet.mk (S i)) = v.val := congrArg (Germ.map ordinalLabel) (repr_eq U a seed)
  have hv : boundedCollapse U θ a v = κ.ord.toZFSet :=
    (indexEquiv_label U a _ seed).symm.trans (congrArg Ordinal.toZFSet (criticalOrdinalPoint_ord U a hf hn ht hk))
  have eq : (⊤ : T) ≤ liftF (fun i => check (S i)) =ᴮ check (PSet.ordinalMk κ.ord) := by
    apply bv_trans (bounded_checked_family U a hk.le hf hn ht hκ v S supp hw)
    exact check_bv_eq (PSet.equiv_iff_eq.mpr ((ZFSet.mk_out _).trans hv))
  have src : ((check (PSet.ordinalMk κ.ord) : bSet T) ∈ᴮ liftF (fun _ => X)) =
      value U (fun i => (check (S i) : bSet A) ∈ᴮ X) :=
    (bv_rw (top_unique eq) (fun y => y ∈ᴮ liftF (fun _ => X)) (h_congr := B_ext_mem_left)).trans
      (boundedName_mem U a hk.le hf hn ht hκ _ _ (supp.map check) (Supported.const _)).symm
  have he := congrArg (fun b => hom b) src
  rw [map_mem hom,map_check] at he
  exact he

variable [CardinalInterFilter (U : Filter I) κ]

include hκ in
theorem boundedPrepared_omegaOne : (⊤ : B) ≤ j omegaOne =ᴮ check (PSet.ordinalMk θ.ord) := by
  have lo := OrderHomClass.mono (initialCollapseHom hk.le) (below_omegaOne_eq_checked_upper κ hκ.isRegular hκ.aleph0_lt)
  rw [TopHomClass.map_top,← boundedPrepared_eq U a hk.le hf hn ht hκ] at lo
  have eq : ordinalImage U a κ.ord = θ.ord :=
    Ordinal.toZFSet_injective ((ordinalImage_code U a _).trans (boundedDiagonal_critical_image U κ θ a hf hn ht))
  have hi := boundedPrepared_ordinal U a hk hf hn ht hκ κ.ord
  rw [eq] at hi
  exact bv_trans lo hi

end Erdos1172LevyCollapse.Preparation
