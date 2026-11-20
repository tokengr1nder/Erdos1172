/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIncreasingPartial
public import Erdos1172.Part4InternalInjectionExtension

@[expose] public section

/-!
# One-point extension of an increasing initial-range partial injection

The next domain point is the actual domain name computed from the old
graph. Adjoining the least unused value extends the ordinal domain by one,
preserves increasingness, and preserves the initial-range property.
All membership and freshness hypotheses hold under the same arbitrary
Boolean condition; no ground enumeration is used.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingPartial

open ErdosPartition ErdosPartialInjection ErdosInjectionExtension

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_insert1_value {x y A : bSet 𝔹} :
    x ∈ᴮ bSet.insert1 y A = x =ᴮ y ⊔ x ∈ᴮ A :=
  mem_insert1

private theorem insert_cases {p q f : bSet 𝔹} {Γ v : 𝔹}
    (Hp : Γ ≤ p ∈ᴮ bSet.insert1 q f)
    (Hnew : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ p =ᴮ q → Δ ≤ v)
    (Hold : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ p ∈ᴮ f → Δ ≤ v) : Γ ≤ v := by
  have Hsplit : Γ ≤ p =ᴮ q ⊔ p ∈ᴮ f :=
    Hp.trans (mem_insert1_value (x := p) (y := q) (A := f)).le
  exact (le_inf le_rfl Hsplit).trans
    (bv_or_elim_right (Hnew inf_le_left inf_le_right) (Hold inf_le_left inf_le_right))

/-- The newly adjoined value follows every old range value. A putative
new-domain-before-old-domain case would create a membership two-cycle. -/
theorem increasingOn_insert_next {θ A f y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ partialGraph θ A f) (Hinc : Γ ≤ increasingOn θ f)
    (Habove : Γ ≤ ⨅ x : bSet 𝔹, _root_.imp (rangeMem θ f x) (x ∈ᴮ y)) :
    Γ ≤ increasingOn θ (bSet.insert1 (pair (graphDomain θ A f) y) f) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro z
  rw [← deduction]
  let D := graphDomain θ A f
  let g := bSet.insert1 (pair D y) f
  let Δ := Γ ⊓ (((i ∈ᴮ θ ⊓ j ∈ᴮ θ) ⊓ i ∈ᴮ j) ⊓
    (pair i x ∈ᴮ g ⊓ pair j z ∈ᴮ g))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hdom : Δ ≤ (i ∈ᴮ θ ⊓ j ∈ᴮ θ) ⊓ i ∈ᴮ j :=
    inf_le_right.trans inf_le_left
  have Hi : Δ ≤ i ∈ᴮ θ := Hdom.trans (inf_le_left.trans inf_le_left)
  have Hj : Δ ≤ j ∈ᴮ θ := Hdom.trans (inf_le_left.trans inf_le_right)
  have Hij : Δ ≤ i ∈ᴮ j := Hdom.trans inf_le_right
  have Hix : Δ ≤ pair i x ∈ᴮ g := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have Hjz : Δ ≤ pair j z ∈ᴮ g := inf_le_right.trans (inf_le_right.trans inf_le_right)
  apply insert_cases Hix
  · intro Λ HΛ Hnew₁
    apply insert_cases (HΛ.trans Hjz)
    · intro Θ HΘ Hnew₂
      have HDD : Θ ≤ D ∈ᴮ D :=
        mem_congr (HΘ.trans (eq_of_eq_pair_left' Hnew₁))
          (eq_of_eq_pair_left' Hnew₂) ((HΘ.trans HΛ).trans Hij)
      exact (bot_of_mem_self' HDD).trans bot_le
    · intro Θ HΘ Hold₂
      have HjD : Θ ≤ j ∈ᴮ D :=
        mem_graphDomain_of_pair (((HΘ.trans HΛ).trans HΔ).trans
          (Hf.trans inf_le_left)) Hold₂
      have HDj : Θ ≤ D ∈ᴮ j :=
        mem_congr (HΘ.trans (eq_of_eq_pair_left' Hnew₁)) bv_refl
          ((HΘ.trans HΛ).trans Hij)
      exact (bot_of_mem_mem' D j HDj HjD).trans bot_le
  · intro Λ HΛ Hold₁
    apply insert_cases (HΛ.trans Hjz)
    · intro Θ HΘ Hnew₂
      have Hrange : Θ ≤ rangeMem θ f x :=
        rangeMem_of_pair ((HΘ.trans HΛ).trans Hi) (HΘ.trans Hold₁)
      have Hxy : Θ ≤ x ∈ᴮ y :=
        (le_inf (((HΘ.trans HΛ).trans HΔ).trans
          (Habove.trans (iInf_le _ x))) Hrange).trans bv_imp_elim
      exact mem_congr bv_refl (bv_symm (eq_of_eq_pair_right' Hnew₂)) Hxy
    · intro Θ HΘ Hold₂
      exact increasingOn_apply (((HΘ.trans HΛ).trans HΔ).trans Hinc)
        ((HΘ.trans HΛ).trans Hi) ((HΘ.trans HΛ).trans Hj)
        ((HΘ.trans HΛ).trans Hij) (HΘ.trans Hold₁) Hold₂

/-- The new value contributes only predecessors already in the old range.
The proof applies to arbitrary names, including locally equal graph pairs. -/
theorem rangeInitial_insert_next {θ A f y : bSet 𝔹} {Γ : 𝔹}
    (Hrange : Γ ≤ rangeInitial θ A f)
    (Hleast : Γ ≤ ⨅ z : bSet 𝔹,
      _root_.imp (z ∈ᴮ A ⊓ z ∈ᴮ y) (rangeMem θ f z)) :
    Γ ≤ rangeInitial θ A (bSet.insert1 (pair (graphDomain θ A f) y) f) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro z
  rw [← deduction]
  let g := bSet.insert1 (pair (graphDomain θ A f) y) f
  let Δ := Γ ⊓ ((rangeMem θ g x ⊓ z ∈ᴮ A) ⊓ z ∈ᴮ x)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hx : Δ ≤ rangeMem θ g x := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have HzA : Δ ≤ z ∈ᴮ A := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have Hzx : Δ ≤ z ∈ᴮ x := inf_le_right.trans inf_le_right
  obtain ⟨i, Hi⟩ := exists_convert Hx
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  apply insert_cases (Hi.trans inf_le_right)
  · intro Θ HΘ Hnew
    have Hzy : Θ ≤ z ∈ᴮ y :=
      mem_congr bv_refl (eq_of_eq_pair_right' Hnew) (HΘ.trans Hzx)
    have Hzrange : Θ ≤ rangeMem θ f z :=
      (le_inf ((HΘ.trans HΔ).trans (Hleast.trans (iInf_le _ z)))
        (le_inf (HΘ.trans HzA) Hzy)).trans bv_imp_elim
    exact rangeMem_mono subset_insertPair Hzrange
  · intro Θ HΘ Hold
    have Hxrange : Θ ≤ rangeMem θ f x :=
      rangeMem_of_pair (HΘ.trans (Hi.trans inf_le_left)) Hold
    exact rangeMem_mono subset_insertPair
      (rangeInitial_apply ((HΘ.trans HΔ).trans Hrange) Hxrange
        (HΘ.trans HzA) (HΘ.trans Hzx))

/-- Adjoin the least unused range value at the current ordinal domain.
The extended graph remains an increasing initial-range partial injection. -/
theorem increasingPartial_insert_next {θ A f y : bSet 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ) (Hf : Γ ≤ increasingPartial θ A f)
    (HDmem : Γ ≤ graphDomain θ A f ∈ᴮ θ) (Hy : Γ ≤ y ∈ᴮ A)
    (Hfresh : Γ ≤ (rangeMem θ f y)ᶜ)
    (Habove : Γ ≤ ⨅ x : bSet 𝔹, _root_.imp (rangeMem θ f x) (x ∈ᴮ y))
    (Hleast : Γ ≤ ⨅ z : bSet 𝔹,
      _root_.imp (z ∈ᴮ A ⊓ z ∈ᴮ y) (rangeMem θ f z)) :
    Γ ≤ increasingPartial θ A
      (bSet.insert1 (pair (graphDomain θ A f) y) f) := by
  let D := graphDomain θ A f
  have Hpartial : Γ ≤ partialGraph θ A f := Hf.trans inf_le_left
  have HDOrd : Γ ≤ Ord D := partialGraph_domain_Ord Hθ Hpartial
  have Hfunction : Γ ≤ is_injective_function D A f := partialGraph_function Hpartial
  have Hnotself : Γ ≤ (D ∈ᴮ D)ᶜ := by
    rw [← imp_bot, ← deduction]
    exact bot_of_mem_self' inf_le_right
  have HfreshImage : Γ ≤ (y ∈ᴮ image D A f)ᶜ := by
    rw [← imp_bot, ← deduction]
    have Hrange : Γ ⊓ y ∈ᴮ image D A f ≤ rangeMem θ f y :=
      (partial_rangeMem_iff_image (inf_le_left.trans Hpartial)).mpr inf_le_right
    exact bv_absurd _ Hrange (inf_le_left.trans Hfresh)
  have Hextended : Γ ≤ is_injective_function (succ D) A
      (bSet.insert1 (pair D y) f) :=
    is_injective_function_insertPair Hfunction Hnotself Hy HfreshImage
  have Hnew : Γ ≤ partialGraph θ A (bSet.insert1 (pair D y) f) :=
    partialGraph_of_ordinal_function (Ord_succ HDOrd)
      (Ord.succ_le_of_lt Hθ HDmem) Hextended
  exact le_inf Hnew
    (le_inf (increasingOn_insert_next Hpartial
      (Hf.trans (inf_le_right.trans inf_le_left)) Habove)
      (rangeInitial_insert_next (Hf.trans (inf_le_right.trans inf_le_right)) Hleast))

end bSet.ErdosIncreasingPartial
