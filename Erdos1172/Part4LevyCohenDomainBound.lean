/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaOneCountablyBounded
public import Erdos1172.Part4LevyCohenIteration

@[expose] public section

/-!
# Checked ground bounds for first-stage countable domains

Ideal-free internal countable boundedness, together with the proved
first-stage identification of checked kappa with omega-one, gives a Boolean
cover by checked ground ordinal bounds. A positive piece of that cover
refines any actual Cohen iteration condition without changing its graph.

Only the first-stage regular uncountable collapse is used. This does not
assume a kappa-chain condition for the final two-stage algebra, nor assert
one globally chosen ground bound at an unchanged Boolean condition.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosOmegaTwo ErdosPartialInjection

private theorem checked_bound_cover {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (A : PSet.{u}) {S : bSet B} {Γ : B}
    (H : Γ ≤ ⨆ b : bSet B, b ∈ᴮ check A ⊓ S ⊆ᴮ b) :
    Γ ≤ ⨆ i : A.Type, S ⊆ᴮ check (A.Func i) := by
  rcases A with ⟨I, a⟩
  rw [← bounded_exists (v := check (PSet.mk I a))
    (ϕ := fun b : bSet B => S ⊆ᴮ b) (h_congr := B_ext_subset_right)] at H
  change Γ ≤ ⨆ i : I, (⊤ : B) ⊓ S ⊆ᴮ check (a i) at H
  change Γ ≤ ⨆ i : I, S ⊆ᴮ check (a i)
  simpa only [top_inf_eq] using H

/-- Every first-stage countable subset of checked kappa has a checked
ground ordinal bound on a Boolean cover of the entire original context. -/
theorem firstStage_countable_subset_bound_cover (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    {S : bSet (FirstAlgebra κ)} {Γ : FirstAlgebra κ}
    (HS : Γ ≤ S ⊆ᴮ check (PSet.ordinalMk κ.ord))
    (Hcount : Γ ≤ injects_into S bSet.omega) :
    Γ ≤ ⨆ i : κ.ord.ToType, S ⊆ᴮ check (PSet.ordinalMk i.toOrd.val) := by
  have Heq : Γ ≤ check (PSet.ordinalMk κ.ord) =ᴮ omegaOne :=
    le_top.trans (firstStage_checked_upper_eq_omegaOne κ Hκ Hunc)
  have HSω : Γ ≤ S ⊆ᴮ omegaOne :=
    bv_rw'' Heq HS (show B_ext (fun a : bSet (FirstAlgebra κ) => S ⊆ᴮ a) from
      B_ext_subset_right)
  obtain ⟨b, Hb⟩ := ErdosOmegaOneCountablyBounded.exists_bound_of_countable HSω Hcount
  have Hcover : Γ ≤ ⨆ b : bSet (FirstAlgebra κ),
      b ∈ᴮ check (PSet.ordinalMk κ.ord) ⊓ S ⊆ᴮ b :=
    le_iSup_of_le b (le_inf
      (mem_congr bv_refl (bv_symm Heq) (Hb.trans inf_le_left))
      (Hb.trans inf_le_right))
  have Hbounded := checked_bound_cover (PSet.ordinalMk κ.ord) Hcover
  rwa [PSet.ordinalMk_eq_def] at Hbounded

/-- The actual graph domain of an arbitrary locally valid Cohen condition
is countable; no external enumeration or supplied bound is required. -/
theorem firstStage_condition_domain_bound_cover (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    {q : bSet (FirstAlgebra κ)} {Γ : FirstAlgebra κ}
    (Hq : Γ ≤ ErdosCohen.condition omegaOne q) :
    Γ ≤ ⨆ i : κ.ord.ToType,
      graphDomain omegaOne two q ⊆ᴮ check (PSet.ordinalMk i.toOrd.val) := by
  apply firstStage_countable_subset_bound_cover κ Hκ Hunc
  · exact bv_rw''
      (bv_symm (le_top.trans (firstStage_checked_upper_eq_omegaOne κ Hκ Hunc)))
      (graphDomain_subset (κ := omegaOne) (S := two) (f := q) (Γ := Γ))
      (show B_ext (fun a : bSet (FirstAlgebra κ) => graphDomain omegaOne two q ⊆ᴮ a)
        from B_ext_subset_right)
  · exact ErdosCohen.countable_of_smallDomain omegaOne_property
      (Hq.trans (inf_le_right.trans inf_le_right))

/-- Choosing a checked ground bound is justified by an actual nonzero
refinement. The selected condition keeps the original canonical graph. -/
theorem exists_ground_bound_refinement (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (p : Erdos1172CohenIteration.Conditions
      (omegaOne : bSet (FirstAlgebra κ))) :
    ∃ (i : κ.ord.ToType)
      (r : Erdos1172CohenIteration.Conditions (omegaOne : bSet (FirstAlgebra κ))),
      r ≤ p ∧ r.value ≤ graphDomain omegaOne two
        (Erdos1172BooleanNameIteration.name r) ⊆ᴮ check (PSet.ordinalMk i.toOrd.val) := by
  have Hq : p.value ≤ ErdosCohen.condition omegaOne
      (Erdos1172BooleanNameIteration.name p) :=
    ErdosCohen.mem_conditions_iff.mp (Erdos1172BooleanNameIteration.name_mem p)
  have Hcover := firstStage_condition_domain_bound_cover κ Hκ Hunc Hq
  have Hpos : ⊥ < ⨆ i : κ.ord.ToType,
      p.value ⊓ graphDomain omegaOne two (Erdos1172BooleanNameIteration.name p)
        ⊆ᴮ check (PSet.ordinalMk i.toOrd.val) := by
    apply (bot_lt_iff_ne_bot.mpr p.nonzero).trans_le
    exact (le_inf le_rfl Hcover).trans_eq (inf_iSup_eq _ _)
  obtain ⟨i, Hi⟩ := nonzero_wit Hpos
  let b : FirstAlgebra κ := p.value ⊓
    graphDomain omegaOne two (Erdos1172BooleanNameIteration.name p)
      ⊆ᴮ check (PSet.ordinalMk i.toOrd.val)
  let r := Erdos1172BooleanNameIteration.shrink p b (ne_of_gt Hi) inf_le_left
  refine ⟨i, r, Erdos1172BooleanNameIteration.shrink_le p b (ne_of_gt Hi) inf_le_left, ?_⟩
  exact inf_le_right

end Erdos1172LevyCohen
