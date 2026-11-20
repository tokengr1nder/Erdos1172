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

end Erdos1172LevyCollapse
