/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenConditions
public import Erdos1172.Part4InternalCountableSuccessor
public import Erdos1172.Part4InternalFullGCH

@[expose] public section

/-!
# Actual one-coordinate extensions of internal Cohen conditions

For the internal first uncountable ordinal, small domains are countable.
Adjoining a fresh binary assignment preserves this property, using an
actual insertion bound on the graph domain. All hypotheses and conclusions
hold at the same Boolean condition, for arbitrary mixed names.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection ErdosInjectionExtension

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_insert1_value {x y z : bSet 𝔹} :
    x ∈ᴮ bSet.insert1 y z = x =ᴮ y ⊔ x ∈ᴮ z := mem_insert1

theorem graphDomain_insertPair_subset {K S f a y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ graphDomain K S (bSet.insert1 (pair a y) f) ⊆ᴮ
      bSet.insert1 a (graphDomain K S f) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hmem : Γ ⊓ x ∈ᴮ graphDomain K S (bSet.insert1 (pair a y) f) ≤
      x ∈ᴮ K ⊓ ⨆ z, z ∈ᴮ S ⊓ pair x z ∈ᴮ bSet.insert1 (pair a y) f :=
    inf_le_right.trans (mem_graphDomain K S (bSet.insert1 (pair a y) f) x).le
  obtain ⟨z, Hz⟩ := exists_convert (Hmem.trans inf_le_right)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hpair := Hz.trans inf_le_right
  rw [mem_insert1_value] at Hpair
  apply (le_inf le_rfl Hpair).trans
  apply bv_or_elim_right
  · rw [mem_insert1_value]
    exact (eq_of_eq_pair_left' inf_le_right).trans le_sup_left
  · rw [mem_insert1_value]
    apply le_sup_of_le_right
    apply le_trans ?_ (mem_graphDomain K S f x).ge
    exact le_inf (inf_le_left.trans (Hmem.trans inf_le_left))
      (le_iSup_of_le z (le_inf (inf_le_left.trans (Hz.trans inf_le_left)) inf_le_right))

theorem smallDomain_of_countable {K p : bSet 𝔹} {Γ : 𝔹}
    (Hω : Γ ≤ omega ∈ᴮ K)
    (Hcount : Γ ≤ injects_into (graphDomain K two p) omega) :
    Γ ≤ smallDomain K p :=
  le_iSup_of_le omega (le_inf Hω Hcount)

theorem countable_of_smallDomain {K p : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ smallDomain K p) :
    Γ ≤ injects_into (graphDomain K two p) omega := by
  apply (le_inf le_rfl Hp).trans
  rw [smallDomain, inf_iSup_eq]
  apply iSup_le
  intro δ
  exact injects_into_trans (inf_le_right.trans inf_le_right)
    (ErdosFullGCH.hartogs_predecessor_injects (inf_le_left.trans HK)
      (inf_le_right.trans inf_le_left))

theorem omega_mem_of_hartogsProperty {K : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K) : Γ ≤ omega ∈ᴮ K :=
  mem_congr bv_refl (bv_symm (ErdosOmegaTwo.omegaOne_property_unique HK))
    ErdosOmegaTwo.omega_mem_omegaOne

theorem condition_insertPair {K p a y : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (Ha : Γ ≤ a ∈ᴮ K)
    (Hfresh : Γ ≤ (a ∈ᴮ graphDomain K two p)ᶜ)
    (Hy : Γ ≤ y ∈ᴮ two) :
    Γ ≤ condition K (bSet.insert1 (pair a y) p) := by
  have Hfunc : Γ ≤ is_function (graphDomain K two p) two p := condition_function Hp
  refine le_inf ?_ (le_inf (is_func_insertPair Hfunc Hfresh) ?_)
  · rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction, mem_insert1_value]
    apply bv_or_elim_right
    · exact bv_rw' inf_le_right (ϕ := fun w => w ∈ᴮ prod K two)
        (h_congr := B_ext_mem_left)
        (H_new := inf_le_left.trans (mem_prod Ha Hy))
    · exact mem_of_mem_subset (inf_le_left.trans (Hp.trans inf_le_left)) inf_le_right
  · apply smallDomain_of_countable (omega_mem_of_hartogsProperty HK)
    exact injects_into_trans (injects_into_of_subset graphDomain_insertPair_subset)
      (ErdosCountableSuccessor.insert_countable_of_fresh
        (countable_of_smallDomain HK (Hp.trans (inf_le_right.trans inf_le_right))) Hfresh)

theorem condition_extension_decides {K p a : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (Ha : Γ ≤ a ∈ᴮ K) :
    Γ ≤ ⨆ q : bSet 𝔹, condition K q ⊓ (p ⊆ᴮ q ⊓
      ⨆ y : bSet 𝔹, y ∈ᴮ two ⊓ pair a y ∈ᴮ q) := by
  have Hsplit : Γ ≤ (a ∈ᴮ graphDomain K two p) ⊔
      (a ∈ᴮ graphDomain K two p)ᶜ := by
    rw [sup_compl_eq_top]
    exact le_top
  apply (le_inf le_rfl Hsplit).trans
  apply bv_or_elim_right
  · apply le_iSup_of_le p
    refine le_inf (inf_le_left.trans Hp) (le_inf subset_self ?_)
    have Hdom : Γ ⊓ a ∈ᴮ graphDomain K two p ≤
        a ∈ᴮ K ⊓ ⨆ y, y ∈ᴮ two ⊓ pair a y ∈ᴮ p :=
      inf_le_right.trans (mem_graphDomain K two p a).le
    exact Hdom.trans inf_le_right
  · have Hz : Γ ⊓ (a ∈ᴮ graphDomain K two p)ᶜ ≤ (0 : bSet 𝔹) ∈ᴮ two :=
      check_mem (PSet.ofNat_mem_of_lt (show 0 < 2 by omega))
    apply le_iSup_of_le (bSet.insert1 (pair a (0 : bSet 𝔹)) p)
    exact le_inf
      (condition_insertPair (inf_le_left.trans HK) (inf_le_left.trans Hp)
        (inf_le_left.trans Ha) inf_le_right Hz)
      (le_inf subset_insertPair (le_iSup_of_le (0 : bSet 𝔹)
        (le_inf Hz pair_mem_insertPair)))

end bSet.ErdosCohen
