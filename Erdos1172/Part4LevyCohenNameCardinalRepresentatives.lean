/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenSuccessorHartogs
public import Erdos1172.Part4InternalMutualCardinalDichotomy

@[expose] public section

/-!
# Mixed-name cardinal representatives in the actual Levy--Cohen algebra

The external child-index bound places an arbitrary internal name below a
checked cardinal. The constructed two-stage successor noncollapse excludes
the full-domain branch of the ordinal mutual-cardinal dichotomy. Bounded
existential quantification then gives a Boolean cover by mutual injections
with checked ordinal predecessors.

The arbitrary name is not assumed checked or externally countable. No one
ground ordinal representative at the original condition is selected, and
neither GCH nor an ideal is an input or a conclusion of this theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet

/-- Every second-stage name has a Boolean cover of checked-ordinal
mutual-cardinality representatives. Both injection directions are retained. -/
theorem name_mutual_checked_ordinal (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (S : bSet (Algebra κ)) :
    (⊤ : Algebra κ) ≤
      ⨆ η : Ordinal.{u}, injects_into S (check (PSet.ordinalMk η)) ⊓
        injects_into (check (PSet.ordinalMk η)) S := by
  let μ := max κ (Cardinal.mk S.type)
  have Hκμ : κ ≤ μ := le_max_left _ _
  have HS : (⊤ : Algebra κ) ≤
      injects_into S (check (PSet.ordinalMk μ.ord)) :=
    ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
      μ S (le_max_right _ _)
  have Hnot : (injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) S :
      Algebra κ) = ⊥ := by
    apply bot_unique
    have Hcomp := injects_into_trans
      (le_rfl : (injects_into (check (PSet.ordinalMk (Order.succ μ).ord)) S :
        Algebra κ) ≤ _)
      (le_top.trans HS)
    exact Hcomp.trans_eq (checked_successor_injects_base_eq_bot κ Hκ μ Hκμ)
  have Hcase := ErdosPartialInjection.ordinal_mutual_cardinal_dichotomy
    (S := S) (Γ := (⊤ : Algebra κ))
    (check_Ord (PSet.Ord_mk (Order.succ μ).ord))
  rw [Hnot, bot_sup_eq] at Hcase
  have Hext : B_ext (fun A : bSet (Algebra κ) =>
      injects_into S A ⊓ injects_into A S) :=
    B_ext_inf B_ext_injects_into_right B_ext_injects_into_left
  have Hbounded := Hcase.trans_eq
    (bounded_exists (v := check (PSet.ordinalMk (Order.succ μ).ord))
      (h_congr := Hext)).symm
  rw [PSet.ordinalMk_eq_def, check_unfold] at Hbounded
  change (⊤ : Algebra κ) ≤
    ⨆ i : (Order.succ μ).ord.ToType,
      ⊤ ⊓ (injects_into S (check (PSet.ordinalMk i.toOrd.val)) ⊓
        injects_into (check (PSet.ordinalMk i.toOrd.val)) S) at Hbounded
  apply Hbounded.trans
  apply iSup_le
  intro i
  exact le_iSup_of_le i.toOrd.val inf_le_right

end Erdos1172LevyCohen
