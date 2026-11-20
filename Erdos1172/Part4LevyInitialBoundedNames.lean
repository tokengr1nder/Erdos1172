/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyInitialEmbeddingCodes
public import Erdos1172.Part4CompletionAntichainRepresentation
public import Erdos1172.Part4LevyChainCondition
public import Erdos1172.Part4CohenRealReading
public import Erdos1172.Part4BooleanCheckedIndicatorAgreement

@[expose] public section

/-! # Reading Lévy names at a single smaller collapse -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion bSet ErdosNameTransport
open scoped Flypitch Erdos1172LevyCollapse
universe u
namespace Erdos1172LevyCollapse
variable {θ : Cardinal.{u}}

private theorem zeroExtension_of_supported {μ : Cardinal.{u}} (h : μ ≤ θ) (p : BelowCondition θ)
    (small : ∀ k ∈ p.support, k ∈ Set.range (initialCoordinate h)) :
    zeroExtension h (initialProjection h p) = p := by
  classical
  apply DFinsupp.ext
  intro k
  by_cases hk : k ∈ Set.range (initialCoordinate h)
  · obtain ⟨i,rfl⟩ := hk
    apply Erdos1172Collapse.Condition.ext
    rw [zeroExtension_entries,initialProjection_entries]
    simp
  · rw [zeroExtension_off h _ hk]
    exact (DFinsupp.notMem_support_iff.mp (fun hv => hk (small k hv))).symm

/-- A short family of Boolean coefficients has a common bounded support in
the finite-support collapse Col(ω,<θ). The bound may be chosen above any
specified starting cardinal. -/
theorem exists_initial_reading (hθ : θ.IsInaccessible) {J : Type u} (hJ : Cardinal.mk J < θ)
    (f : J → Completion (BelowCondition θ)) {start : Cardinal.{u}} (hs : start < θ) :
    ∃ (μ : Cardinal.{u}) (hμ : μ < θ), start < μ ∧
      ∃ g : J → Completion (BelowCondition μ), ∀ j, initialCollapseHom hμ.le (g j) = f j := by
  classical
  choose A card _ supA using fun j => exists_small_condition_antichain_sup θ
    (fun b hp hd => below_completion_disjoint_family_cardinal_lt θ hθ.isRegular hθ.aleph0_lt b hp hd) (f j)
  let K := Σ j, A j
  have hK : Cardinal.mk K < θ := by
    rw [show Cardinal.mk K = _ from Cardinal.mk_sigma _]
    exact Cardinal.sum_lt_of_isRegular hθ.isRegular hJ card
  let S := (z : K) × (z.2.val.support : Set θ.ord.ToType)
  have hS : Cardinal.mk S < θ := by
    rw [show Cardinal.mk S = _ from Cardinal.mk_sigma _]
    exact Cardinal.sum_lt_of_isRegular hθ.isRegular hK (fun _ => Cardinal.mk_lt_aleph0.trans hθ.aleph0_lt)
  let β := ⨆ x : S, x.2.val.toOrd.val + 1
  have hβ : β < θ.ord := Ordinal.iSup_add_one_lt_of_lt_cof (by rw [hθ.isRegular.cof_ord]; exact hS)
    (fun x => x.2.val.toOrd.property)
  let μ := Order.succ (max start β.card)
  have hμ : μ < θ := hθ.isSuccLimit.succ_lt (max_lt hs (Cardinal.lt_ord.mp hβ))
  let proj := initialProjection hμ.le
  have supported (j : J) (p : A j) : zeroExtension hμ.le (proj p.val) = p.val := by
    apply zeroExtension_of_supported
    intro k hk
    have hkb : k.toOrd.val < β := Ordinal.lt_iSup_add_one _ (⟨⟨j,p⟩,⟨k,hk⟩⟩ : S)
    have hu : β < μ.ord := Cardinal.lt_ord.mpr (Order.lt_succ_of_le (le_max_right _ _))
    let i := Ordinal.ToType.mk (⟨k.toOrd.val,hkb.trans hu⟩ : Set.Iio μ.ord)
    refine ⟨i,Ordinal.ToType.mk.symm.injective (Subtype.ext ?_)⟩
    exact (initialCoordinate_ordinal hμ.le i).trans (congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _))
  refine ⟨μ,hμ,Order.lt_succ_of_le (le_max_left _ _),fun j => ⨆ p : A j, condition (proj p.val),fun j => ?_⟩
  rw [map_iSup]
  exact (iSup_congr (fun p => (initialCollapseHom_condition hμ.le _).trans
    (congrArg condition (supported j p)))).trans (supA j)

/-- Every real name in the full collapse is locally equal, on the entire
condition forcing it to be a real, to a name from one bounded collapse. -/
theorem realName_from_initial (hθ : θ.IsInaccessible) (x : bSet (Completion (BelowCondition θ)))
    {Γ : Completion (BelowCondition θ)} (hx : Γ ≤ x ⊆ᴮ omega)
    {start : Cardinal.{u}} (hs : start < θ) :
    ∃ (μ : Cardinal.{u}) (hμ : μ < θ), start < μ ∧
      ∃ g : ℕ → Completion (BelowCondition μ),
        Γ ≤ x =ᴮ mapNames (initialCollapseHom hμ.le) (Erdos1172CohenIteration.realName g) := by
  let coeff (n : ULift.{u} ℕ) := (of_nat n.down : bSet (Completion (BelowCondition θ))) ∈ᴮ x
  obtain ⟨μ,hμ,high,g,reads⟩ := exists_initial_reading hθ (by simpa using hθ.aleph0_lt) coeff hs
  refine ⟨μ,hμ,high,fun n => g ⟨n⟩,Erdos1172CohenIteration.eq_map_realName_of_binary_agreement _ hx ?_⟩
  intro n
  rw [reads ⟨n⟩]
  simp [coeff]

open ErdosCheckedIndicator in
/-- A single proper initial collapse suffices simultaneously for any short
family of names for subsets of small ground sets, with their original
Boolean conditions. -/
theorem small_subsets_from_initial (hθ : θ.IsInaccessible) {J : Type u} (hJ : Cardinal.mk J < θ)
    (A : J → PSet.{u}) (hA : ∀ j, Cardinal.mk (A j).Type < θ)
    (x : J → bSet (Completion (BelowCondition θ))) (Γ : J → Completion (BelowCondition θ))
    (hx : ∀ j, Γ j ≤ x j ⊆ᴮ check (A j)) {start : Cardinal.{u}} (hs : start < θ) :
    ∃ (μ : Cardinal.{u}) (hμ : μ < θ), start < μ ∧
      ∃ g : (j : J) → (A j).Type → Completion (BelowCondition μ), ∀ j,
        Γ j ≤ x j =ᴮ mapNames (initialCollapseHom hμ.le) (checkedIndicator (A j) (g j)) := by
  let T := (j : J) × (A j).Type
  have hT : Cardinal.mk T < θ := by
    rw [show Cardinal.mk T = _ from Cardinal.mk_sigma _]
    exact Cardinal.sum_lt_of_isRegular hθ.isRegular hJ hA
  let coeff (z : T) := (check ((A z.1).Func z.2) : bSet (Completion (BelowCondition θ))) ∈ᴮ x z.1
  obtain ⟨μ,hμ,high,g,reads⟩ := exists_initial_reading hθ hT coeff hs
  refine ⟨μ,hμ,high,fun j i => g ⟨j,i⟩,fun j => ?_⟩
  simp only [checkedIndicator,mapNames_mk,map_check]
  apply eq_checkedIndicator_of_binary_agreement (A j) (hx j)
  intro i
  rw [reads ⟨j,i⟩]
  simp [coeff]

end Erdos1172LevyCollapse
