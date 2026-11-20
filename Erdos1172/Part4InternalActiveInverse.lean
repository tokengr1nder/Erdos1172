/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedFallbackChoice
public import Erdos1172.Part4InternalFusionRowCandidates

@[expose] public section

/-!
# A total inverse selector for a birth-guarded increasing row

Only stages strictly after the birth ordinal participate in the inverse.
The actual selector is total on omega-one, with zero as a fallback where
there is no active preimage. Active strict increase makes its value the
original active stage. Closure points of this total inverse then prohibit
a chosen value from lying below its active stage.

No increasingness is asserted for the inactive default-zero prefix, and
no co-large range or supplied inverse function is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosActiveInverse

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosFusionRowCandidates
open ErdosBoundedFallbackChoice ErdosClosurePoints

def activePreimage (ν f v i : bSet 𝔹) : 𝔹 :=
  ν ∈ᴮ i ⊓ pair i v ∈ᴮ f

theorem activePreimage_ext_value (ν f i : bSet 𝔹) :
    B_ext (fun v => activePreimage ν f v i) :=
  B_ext_inf B_ext_const B_ext_pair_mem_right

theorem activePreimage_ext_stage (ν f v : bSet 𝔹) :
    B_ext (activePreimage ν f v) :=
  B_ext_inf B_ext_mem_right B_ext_pair_mem_left

def activeInverseLaw (ν f g : bSet 𝔹) : 𝔹 :=
  fallbackFamilyLaw omegaOne omegaOne (activePreimage ν f) 0 g

/-- Bounded choice constructs the total inverse-or-zero graph, even for
arbitrary malformed forward graphs. -/
theorem exists_active_inverse (ν f : bSet 𝔹) {Γ : 𝔹} :
    ∃ g : bSet 𝔹, Γ ≤ is_function omegaOne omegaOne g ⊓ activeInverseLaw ν f g :=
  exists_fallback_selector (activePreimage_ext_value ν f)
    (activePreimage_ext_stage ν f) ErdosLargeDifference.zero_mem_omegaOne

/-- Strict increase on the active domain suffices for unique active
preimages; nothing is required of the prebirth values. -/
theorem active_preimage_unique {ν f i j v : bSet 𝔹} {Γ : 𝔹}
    (Hinc : Γ ≤ increasingOn (activatedStages omegaOne ν) f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hj : Γ ≤ j ∈ᴮ omegaOne)
    (Hνi : Γ ≤ ν ∈ᴮ i) (Hνj : Γ ≤ ν ∈ᴮ j)
    (Hiv : Γ ≤ pair i v ∈ᴮ f) (Hjv : Γ ≤ pair j v ∈ᴮ f) :
    Γ ≤ i =ᴮ j := by
  have HiD := mem_activatedStages_iff.mpr ⟨Hi, Hνi⟩
  have HjD := mem_activatedStages_iff.mpr ⟨Hj, Hνj⟩
  apply (le_inf (le_refl Γ) (epsilon_trichotomy_of_Ord Hi Hj omegaOne_Ord)).trans
  rw [inf_sup_left, inf_sup_left]
  apply sup_le
  · apply sup_le
    · exact inf_le_right
    · exact (bot_of_mem_self' (increasingOn_apply (inf_le_left.trans Hinc)
        (inf_le_left.trans HiD) (inf_le_left.trans HjD) inf_le_right
        (inf_le_left.trans Hiv) (inf_le_left.trans Hjv))).trans bot_le
  · exact (bot_of_mem_self' (increasingOn_apply (inf_le_left.trans Hinc)
      (inf_le_left.trans HjD) (inf_le_left.trans HiD) inf_le_right
      (inf_le_left.trans Hjv) (inf_le_left.trans Hiv))).trans bot_le

/-- Every actual active pair is reversed in the constructed total
selector, at the same original Boolean condition. -/
theorem active_inverse_pair {ν f g i v : bSet 𝔹} {Γ : 𝔹}
    (Hg : Γ ≤ is_function omegaOne omegaOne g)
    (Hlaw : Γ ≤ activeInverseLaw ν f g)
    (Hinc : Γ ≤ increasingOn (activatedStages omegaOne ν) f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hνi : Γ ≤ ν ∈ᴮ i)
    (Hv : Γ ≤ v ∈ᴮ omegaOne) (Hiv : Γ ≤ pair i v ∈ᴮ f) :
    Γ ≤ pair v i ∈ᴮ g := by
  have Hex : Γ ≤ ⨆ j, j ∈ᴮ omegaOne ⊓ pair v j ∈ᴮ g :=
    (le_inf ((is_total_of_is_function Hg).trans (iInf_le _ v)) Hv).trans bv_imp_elim
  obtain ⟨j, Hj⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hpre : Γ ≤ activePreimage ν f v j :=
    selected_candidate Hg Hlaw (Hj.trans inf_le_right)
      (le_iSup_of_le i (le_inf Hi (le_inf Hνi Hiv)))
  have Hij := active_preimage_unique Hinc Hi (Hj.trans inf_le_left) Hνi
    (Hpre.trans inf_le_left) Hiv (Hpre.trans inf_le_right)
  exact mem_congr (pair_congr bv_refl (bv_symm Hij)) bv_refl (Hj.trans inf_le_right)

/-- On a closure point of the total inverse, an active output cannot be
below its stage. This is not a global increasing-selfmap assertion. -/
theorem active_index_subset_value_of_inverse_closure
    {ν f g i v : bSet 𝔹} {Γ : 𝔹}
    (Hg : Γ ≤ is_function omegaOne omegaOne g)
    (Hlaw : Γ ≤ activeInverseLaw ν f g)
    (Hinc : Γ ≤ increasingOn (activatedStages omegaOne ν) f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hνi : Γ ≤ ν ∈ᴮ i)
    (Hv : Γ ≤ v ∈ᴮ omegaOne) (Hiv : Γ ≤ pair i v ∈ᴮ f)
    (Hclosed : Γ ≤ i ∈ᴮ closurePoints g) : Γ ≤ i ⊆ᴮ v := by
  have Hvi := active_inverse_pair Hg Hlaw Hinc Hi Hνi Hv Hiv
  have Hnot : Γ ≤ (v ∈ᴮ i)ᶜ := by
    rw [← imp_bot, ← deduction]
    exact bot_of_mem_self' (closurePoints_apply (inf_le_left.trans Hclosed)
      (inf_le_left.trans Hv) inf_le_right (inf_le_left.trans Hvi))
  apply (Ord.le_iff_lt_or_eq (Ord_of_mem_Ord Hi omegaOne_Ord)
    (Ord_of_mem_Ord Hv omegaOne_Ord)).mpr
  apply (le_inf (le_refl Γ) (epsilon_trichotomy_of_Ord Hi Hv omegaOne_Ord)).trans
  rw [inf_sup_left, inf_sup_left]
  exact sup_le (sup_le (inf_le_right.trans le_sup_right) (inf_le_right.trans le_sup_left))
    ((bv_absurd _ inf_le_right (inf_le_left.trans Hnot)).trans bot_le)

end bSet.ErdosActiveInverse
