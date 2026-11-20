/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalNonstationaryFiniteIdeal
public import Erdos1172.Part4InternalNonstationarySmallUnion
public import Erdos1172.Part4InternalNonstationaryNormal
public import Erdos1172.Part4InternalColargeIntersection

@[expose] public section

/-!
Pressing down now uses the explicitly constructed internal nonstationary
ideal on omega-two. CH supplies its proved closure properties; neither
normality nor a normal ideal witness is an extra premise. Positivity for
this ideal is stationarity, and every such set is internally omega-two
large. A specific stationary endpoint set for stopped-run freezing is
still not constructed here.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNonstationary

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosClubs ErdosColargeIntersection

theorem nonstationaryIdeal_package {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ properIdeal omegaTwo nonstationaryIdeal ⊓
      (countableAbsorption omegaTwo nonstationaryIdeal ⊓
        (countableClosure nonstationaryIdeal ⊓ diagonalClosure omegaTwo nonstationaryIdeal)) :=
  le_inf (nonstationaryIdeal_proper HCH)
    (le_inf (nonstationaryIdeal_countableAbsorption HCH)
      (le_inf (nonstationaryIdeal_countableClosure HCH)
        (nonstationaryIdeal_diagonalClosure HCH)))

theorem omegaTwo_stationary {Γ : 𝔹} :
    Γ ≤ positive omegaTwo nonstationaryIdeal omegaTwo :=
  le_inf subset_self omegaTwo_not_mem_nonstationaryIdeal

/-- Stationarity of the actual name implies omega-two cardinal size.
The converse is deliberately not asserted. -/
theorem stationary_injects_omegaTwo {S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S) :
    Γ ≤ injects_into omegaTwo S := by
  have Hcases := ErdosPartialInjection.omegaTwo_cardinal_dichotomy (S := S) (Γ := Γ)
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact (bv_absurd _
      (omegaOne_small_mem_nonstationaryIdeal (inf_le_left.trans HCH)
        (inf_le_left.trans (HS.trans inf_le_left)) inf_le_right)
      (inf_le_left.trans (HS.trans inf_le_right))).trans bot_le
  · exact inf_le_right

theorem exists_mem_stationary_club {S C : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S)
    (HC : Γ ≤ club omegaTwo C) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ S ⊓ x ∈ᴮ C := by
  have Hsmall : Γ ≤ difference omegaTwo C ∈ᴮ nonstationaryIdeal :=
    mem_nonstationaryIdeal_of_club HC subset_self
  have Hpositive := positive_difference_of_small (nonstationaryIdeal_isIdeal HCH) HS Hsmall
  obtain ⟨x, Hx⟩ := exists_mem_of_positive (nonstationaryIdeal_isIdeal HCH) Hpositive
  rw [mem_difference] at Hx
  have Hxω : Γ ≤ x ∈ᴮ omegaTwo := mem_of_mem_subset (HS.trans inf_le_left)
    (Hx.trans inf_le_left)
  refine ⟨x, le_inf (Hx.trans inf_le_left) ?_⟩
  rw [← compl_compl (x ∈ᴮ C), ← imp_bot, ← deduction]
  have Hbad : Γ ⊓ (x ∈ᴮ C)ᶜ ≤ x ∈ᴮ difference omegaTwo C := by
    rw [mem_difference]
    exact le_inf (inf_le_left.trans Hxω) inf_le_right
  exact bv_absurd _ Hbad (inf_le_left.trans (Hx.trans inf_le_right))

/-- Meeting every internally named club suffices for positivity of the
constructed nonstationary ideal, without assuming stationarity separately. -/
theorem stationary_of_meets_clubs {S : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hmeets : Γ ≤ ⨅ C, _root_.imp (club omegaTwo C)
      (⨆ x, x ∈ᴮ S ⊓ x ∈ᴮ C)) :
    Γ ≤ positive omegaTwo nonstationaryIdeal S := by
  refine le_inf HS ?_
  rw [← imp_bot, ← deduction]
  obtain ⟨C, HC⟩ := exists_avoiding_club
    (show Γ ⊓ S ∈ᴮ nonstationaryIdeal ≤ S ∈ᴮ nonstationaryIdeal from inf_le_right)
  have Hex : Γ ⊓ S ∈ᴮ nonstationaryIdeal ≤ ⨆ x, x ∈ᴮ S ⊓ x ∈ᴮ C :=
    (le_inf (inf_le_left.trans (Hmeets.trans (iInf_le _ C)))
      (HC.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨x, Hx⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_mem_left)
  have Hbad := mem_of_mem_subset (HC.trans inf_le_right) (Hx.trans inf_le_left)
  rw [mem_difference] at Hbad
  exact bv_absurd _ (Hx.trans inf_le_right) (Hbad.trans inf_le_right)

/-- The normality premise of internal pressing down has been discharged
for this concrete ideal. A stationary domain and regressive function
remain the explicit mathematical inputs. -/
theorem stationary_subfiber_of_regressiveFunction {S f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S)
    (Hf : Γ ≤ is_function S omegaTwo f)
    (Hreg : Γ ≤ ⨅ x, ⨅ i, _root_.imp (pair x i ∈ᴮ f) (i ∈ᴮ x)) :
    Γ ≤ ⨆ i, i ∈ᴮ omegaTwo ⊓
      (positive omegaTwo nonstationaryIdeal (ErdosIdeal.fiber omegaTwo f i) ⊓
        ErdosIdeal.fiber omegaTwo f i ⊆ᴮ S) :=
  positive_subfiber_of_regressiveFunction nonstationaryIdeal_downward
    (nonstationaryIdeal_diagonalClosure HCH) HS Hf Hreg

theorem stationary_large_subfiber_of_regressiveFunction {S f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S)
    (Hf : Γ ≤ is_function S omegaTwo f)
    (Hreg : Γ ≤ ⨅ x, ⨅ i, _root_.imp (pair x i ∈ᴮ f) (i ∈ᴮ x)) :
    Γ ≤ ⨆ i, i ∈ᴮ omegaTwo ⊓
      (positive omegaTwo nonstationaryIdeal (ErdosIdeal.fiber omegaTwo f i) ⊓
        (injects_into omegaTwo (ErdosIdeal.fiber omegaTwo f i) ⊓
          ErdosIdeal.fiber omegaTwo f i ⊆ᴮ S)) := by
  have Hfiber := stationary_subfiber_of_regressiveFunction HCH HS Hf Hreg
  apply (le_inf (le_refl Γ) Hfiber).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  have Hpos : Γ ⊓ (i ∈ᴮ omegaTwo ⊓
      (positive omegaTwo nonstationaryIdeal (ErdosIdeal.fiber omegaTwo f i) ⊓
        ErdosIdeal.fiber omegaTwo f i ⊆ᴮ S)) ≤
      positive omegaTwo nonstationaryIdeal (ErdosIdeal.fiber omegaTwo f i) :=
    inf_le_right.trans (inf_le_right.trans inf_le_left)
  exact le_iSup_of_le i (le_inf (inf_le_right.trans inf_le_left)
    (le_inf Hpos (le_inf (stationary_injects_omegaTwo (inf_le_left.trans HCH) Hpos)
      (inf_le_right.trans (inf_le_right.trans inf_le_right)))))

end bSet.ErdosNonstationary
