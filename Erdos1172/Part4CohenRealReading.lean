/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenRelativeBinaryReading
public import Erdos1172.Part4GeneratedSubsetName
public import Erdos1172.Part4InternalPowersetPairCoding

@[expose] public section

/-!
# Reading arbitrary internal real names through the first-stage embedding

For an arbitrary second-stage name locally contained in omega, its natural
membership coefficients form a countable Boolean sequence. The proved
relative binary-reading cover supplies first-stage coefficient sequences
on Boolean pieces. Each such sequence gives an actual first-stage subset
name, and local coefficient agreement gives equality of the full names.

The conclusion is a Boolean join over first-stage names at the original
condition. It does not assert one global first-stage witness, unbounded
elementarity, cardinal preservation, or full-GCH preservation.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet bSet.ErdosNameTransport

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B]
variable [NontrivialCompleteBooleanAlgebra C]

/-- An actual subset of omega with prescribed Boolean coefficients. -/
def realName (b : ℕ → B) : bSet B :=
  .mk (ULift.{u} ℕ) (fun i => of_nat i.down) (fun i => b i.down)

theorem realName_eq_indicator (b : ℕ → B) :
    realName b = set_of_indicator (u := (omega : bSet B)) (fun i => b i.down) := rfl

theorem realName_subset (b : ℕ → B) : (⊤ : B) ≤ realName b ⊆ᴮ omega := by
  rw [realName_eq_indicator]
  apply set_of_indicator_subset
  intro i
  change _ ≤ (⊤ : B)
  exact le_top

theorem realName_subset_value (b : ℕ → B) : realName b ⊆ᴮ omega = (⊤ : B) :=
  top_unique (realName_subset b)

/-- Hereditary transport fixes the natural children and transports their
coefficients. This is an equality of actual names, not just a forcing claim. -/
theorem map_realName (e : CompleteLatticeHom B C) (b : ℕ → B) :
    mapNames e (realName b) = realName (fun n => e (b n)) := by
  simp only [realName, mapNames_mk, of_nat, map_check]

private theorem agreement_forward {a b Γ : C}
    (H : Γ ≤ (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ)) : Γ ⊓ a ≤ b := by
  rw [deduction]
  change Γ ≤ aᶜ ⊔ b
  exact H.trans (sup_le (inf_le_right.trans le_sup_right)
    (inf_le_left.trans le_sup_left))

private theorem agreement_reverse {a b Γ : C}
    (H : Γ ≤ (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ)) : Γ ⊓ b ≤ a := by
  rw [deduction]
  change Γ ≤ bᶜ ⊔ a
  exact H.trans (sup_le (inf_le_left.trans le_sup_right)
    (inf_le_right.trans le_sup_left))

/-- Local binary agreement of all natural membership coefficients recovers
the entire arbitrary subset name at precisely the same condition. -/
theorem eq_map_realName_of_binary_agreement (e : CompleteLatticeHom B C)
    {x : bSet C} {Γ : C} {b : ℕ → B}
    (Hx : Γ ≤ x ⊆ᴮ omega)
    (Hcoeff : ∀ n : ℕ, Γ ≤
      (((of_nat n : bSet C) ∈ᴮ x) ⊓ e (b n)) ⊔
        (((of_nat n : bSet C) ∈ᴮ x)ᶜ ⊓ (e (b n))ᶜ)) :
    Γ ≤ x =ᴮ mapNames e (realName b) := by
  rw [map_realName, realName_eq_indicator]
  apply bv_trans (eq_membership_indicator_of_subset Hx)
  apply ErdosPowersetPairCoding.indicator_eq_iff.mpr
  constructor
  · intro i
    change Γ ⊓ ((of_nat i.down : bSet C) ∈ᴮ x) ≤ e (b i.down)
    exact agreement_forward (Hcoeff i.down)
  · intro i
    change Γ ⊓ e (b i.down) ≤ (of_nat i.down : bSet C) ∈ᴮ x
    exact agreement_reverse (Hcoeff i.down)

/-- Every arbitrary internal real name is locally read by first-stage real
names. The witnesses form a Boolean cover; no single global witness is claimed. -/
theorem real_reading_cover {x : bSet (omegaOneAlgebra B)} {Γ : omegaOneAlgebra B}
    (Hx : Γ ≤ x ⊆ᴮ omega) :
    Γ ≤ ⨆ y : bSet B,
      omegaOneFirstStageHom (y ⊆ᴮ omega) ⊓
        (x =ᴮ mapNames omegaOneFirstStageHom y) := by
  let c : ℕ → omegaOneAlgebra B := fun n => (of_nat n : bSet (omegaOneAlgebra B)) ∈ᴮ x
  let agreement : (ℕ → B) → omegaOneAlgebra B := fun b =>
    ⨅ n : ℕ, (c n ⊓ omegaOneFirstStageHom (b n)) ⊔
      ((c n)ᶜ ⊓ (omegaOneFirstStageHom (b n))ᶜ)
  have Hcover : (⨆ b : ℕ → B, agreement b) = ⊤ :=
    iSup_iInf_relative_binary_reading_eq_top ErdosOmegaTwo.omegaOne_property c
  have Hpieces : Γ = ⨆ b : ℕ → B, Γ ⊓ agreement b := by
    erw [← inf_iSup_eq, Hcover, inf_top_eq]
  rw [Hpieces]
  apply iSup_le
  intro b
  have Hcoeff (n : ℕ) : Γ ⊓ agreement b ≤
      (c n ⊓ omegaOneFirstStageHom (b n)) ⊔
        ((c n)ᶜ ⊓ (omegaOneFirstStageHom (b n))ᶜ) :=
    inf_le_right.trans (iInf_le _ n)
  have Heq : Γ ⊓ agreement b ≤
      x =ᴮ mapNames omegaOneFirstStageHom (realName b) :=
    eq_map_realName_of_binary_agreement omegaOneFirstStageHom
      (inf_le_left.trans Hx) Hcoeff
  apply le_iSup_of_le (realName b)
  refine le_inf ?_ Heq
  rw [realName_subset_value, map_top]
  exact le_top

end Erdos1172CohenIteration
