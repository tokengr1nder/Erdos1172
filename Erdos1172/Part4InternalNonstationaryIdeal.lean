/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClubTails
public import Erdos1172.Part4InternalCountableAbsorption

@[expose] public section

/-!
The actual internal family of subsets of omega-two missing a club.
Membership witnesses are constructed names at the original condition.
Downward closure, properness of membership, and absorption of every
omega-one-small subset follow from the club constructions. Finite union
closure and normality are established separately, not assumed here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNonstationary

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosClubs ErdosRelationGraph

def missesClub (A : bSet 𝔹) : 𝔹 :=
  ⨆ C, club omegaTwo C ⊓ A ⊆ᴮ difference omegaTwo C

theorem missesClub_ext : B_ext (missesClub : bSet 𝔹 → 𝔹) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_subset_left)

theorem avoidingClub_ext (A : bSet 𝔹) :
    B_ext (fun C => club omegaTwo C ⊓ A ⊆ᴮ difference omegaTwo C) :=
  B_ext_inf (club_ext_set omegaTwo)
    (B_ext_term (ϕ := fun D => A ⊆ᴮ D) (t := difference omegaTwo)
      B_ext_subset_right (B_congr_difference_right omegaTwo))

def nonstationaryIdeal : bSet 𝔹 :=
  comprehend missesClub (bv_powerset omegaTwo)

theorem mem_nonstationaryIdeal_iff {A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ A ∈ᴮ nonstationaryIdeal ↔ Γ ≤ A ⊆ᴮ omegaTwo ∧ Γ ≤ missesClub A := by
  constructor
  · intro H
    have Hparts := (mem_comprehend_and missesClub_ext).mp H
    exact ⟨mem_powerset_iff.mp Hparts.1, Hparts.2⟩
  · rintro ⟨Hsub, Hmiss⟩
    exact (mem_comprehend_and missesClub_ext).mpr ⟨mem_powerset_iff.mpr Hsub, Hmiss⟩

theorem mem_nonstationaryIdeal_of_club {A C : bSet 𝔹} {Γ : 𝔹}
    (HC : Γ ≤ club omegaTwo C) (Havoid : Γ ≤ A ⊆ᴮ difference omegaTwo C) :
    Γ ≤ A ∈ᴮ nonstationaryIdeal :=
  mem_nonstationaryIdeal_iff.mpr ⟨subset_trans' Havoid difference_subset,
    le_iSup_of_le C (le_inf HC Havoid)⟩

theorem exists_avoiding_club {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ∈ᴮ nonstationaryIdeal) :
    ∃ C : bSet 𝔹, Γ ≤ club omegaTwo C ⊓ A ⊆ᴮ difference omegaTwo C :=
  exists_convert (mem_nonstationaryIdeal_iff.mp HA).2 (avoidingClub_ext A)

theorem nonstationaryIdeal_downward {Γ : 𝔹} : Γ ≤ downwardClosed (nonstationaryIdeal : bSet 𝔹) := by
  apply le_iInf
  intro A
  apply le_iInf
  intro B
  rw [← deduction]
  obtain ⟨C, HC⟩ := exists_avoiding_club
    (show Γ ⊓ (A ⊆ᴮ B ⊓ B ∈ᴮ nonstationaryIdeal) ≤ B ∈ᴮ nonstationaryIdeal from
      inf_le_right.trans inf_le_right)
  exact mem_nonstationaryIdeal_of_club (HC.trans inf_le_left)
    (subset_trans' (inf_le_right.trans inf_le_left) (HC.trans inf_le_right))

theorem omegaOne_small_mem_nonstationaryIdeal {A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ A ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into A omegaOne) : Γ ≤ A ∈ᴮ nonstationaryIdeal := by
  obtain ⟨C, HC⟩ := exists_club_avoiding_small HCH HA Hsmall
  exact mem_nonstationaryIdeal_of_club (HC.trans inf_le_left) (HC.trans inf_le_right)

end bSet.ErdosNonstationary
