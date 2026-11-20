/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCardinality
public import Erdos1172.Part4ShioyaGenericString
public import Erdos1172.Part4DenseCompletionCardinality
public import Erdos1172.Part4BooleanCardinalPreservation
public import Erdos1172.Part4InternalHartogsInitial

@[expose] public section

/-! # Preservation of cardinals above the dual Shioya collapse

The θ-sized forcing has the θ⁺ chain condition. Every checked ground
cardinal above θ is an initial ordinal against arbitrary internal
predecessors in the extension, including when the cardinal is singular.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion bSet Lattice
open scoped Flypitch
universe u

namespace Erdos1172Shioya

variable (κ θ : Cardinal.{u}) [Fact (Cardinal.aleph0 < κ)] (hθ : θ.IsInaccessible)
include hθ

theorem disjoint_family_cardinal_le {J : Type u} (w : J → Algebra κ θ)
    (hp : ∀ i, w i ≠ ⊥) (hd : ∀ i j, i ≠ j → w i ⊓ w j = ⊥) : Cardinal.mk J ≤ θ := by
  have h := disjoint_family_cardinal_le_dense (Set.univ : Set (Condition κ θ))
    (fun p => ⟨p, Set.mem_univ _, le_rfl⟩) w hp hd
  rw [Cardinal.mk_univ] at h
  exact h.trans (Condition.cardinal_le hθ)

variable [Nonempty (Condition κ θ)]

theorem surjects_onto_eq_bot_of_cardinal_lt (X Y : PSet.{u})
    (hxy : Cardinal.mk X.Type < Cardinal.mk Y.Type) (hy : θ < Cardinal.mk Y.Type)
    (hsep : ∀ i j : Y.Type, i ≠ j → ¬PSet.Equiv (Y.Func i) (Y.Func j)) :
    (surjects_onto (check X) (check Y) : Algebra κ θ) = ⊥ :=
  ErdosCardinalPreservation.surjects_onto_eq_bot_of_cardinal_lt
    (κ := Order.succ θ) (Cardinal.isRegular_succ hθ.aleph0_lt.le)
    (fun w hp hd => (disjoint_family_cardinal_le κ θ hθ w hp hd).trans_lt (Order.lt_succ θ))
    X Y hxy (Order.succ_le_of_lt hy) hsep

theorem checked_injects_predecessor_eq_bot (μ : Cardinal.{u}) (hμ : θ < μ)
    (γ : Ordinal.{u}) (hγ : γ < μ.ord) :
    (injects_into (check (PSet.ordinalMk μ.ord)) (check (PSet.ordinalMk γ)) : Algebra κ θ) = ⊥ := by
  have hsurj := surjects_onto_eq_bot_of_cardinal_lt κ θ hθ (PSet.ordinalMk γ) (PSet.ordinalMk μ.ord)
    (by simpa only [PSet.ordinalMk_card, Cardinal.card_ord] using Cardinal.lt_ord.mp hγ)
    (by simpa only [PSet.ordinalMk_card, Cardinal.card_ord] using hμ) (PSet.ordinalMk_inj μ.ord)
  have hne : (⊤ : Algebra κ θ) ≤ exists_mem (check (PSet.ordinalMk μ.ord)) := by
    obtain ⟨x, hx⟩ := PSet.exists_mem_of_nonzero (Cardinal.ord_pos.mpr (hθ.pos.trans hμ))
    exact le_iSup_of_le (check x) (check_mem hx)
  apply bot_unique
  exact (surjects_onto_of_injects_into' le_rfl (le_top.trans hne)).trans_eq hsurj

theorem checked_initialOrdinal (μ : Cardinal.{u}) (hμ : θ < μ) :
    (⊤ : Algebra κ θ) ≤ ErdosHartogs.initialOrdinal (check (PSet.ordinalMk μ.ord)) := by
  refine le_inf (check_Ord (PSet.Ord_mk μ.ord)) ?_
  rw [← bounded_forall (h_congr := B_ext_neg (h := B_ext_injects_into_right))]
  rw [PSet.ordinalMk_eq_def μ.ord, check_unfold]
  change (⊤ : Algebra κ θ) ≤ ⨅ i : μ.ord.ToType, _root_.imp ⊤
    (injects_into (check (PSet.mk μ.ord.ToType fun j => PSet.ordinalMk j.toOrd.val))
      (check (PSet.ordinalMk i.toOrd.val)))ᶜ
  apply le_iInf
  intro i
  rw [top_imp, ← PSet.ordinalMk_eq_def, checked_injects_predecessor_eq_bot κ θ hθ μ hμ _ i.toOrd.property,
    compl_bot]

end Erdos1172Shioya
