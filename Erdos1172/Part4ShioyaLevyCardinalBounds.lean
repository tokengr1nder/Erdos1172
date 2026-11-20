/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyChainCondition
public import Erdos1172.Part4ShioyaLevyRestrictions
public import Erdos1172.Part4CompletionAntichainRepresentation
public import Erdos1172.Part4SmallSubsetCardinality
public import Erdos1172.Part4GroundIndexNameBound
public import Erdos1172.Part4BooleanCardinalPreservation
public import Erdos1172.Part4InternalHartogsInitial

@[expose] public section

/-! # Cardinal preservation and powerset bounds in the full Lévy product

Every regular Boolean value is represented by a small antichain. The forcing
has size at most θ, so there are at most θ Boolean values and at most θ
coefficient families of any fixed length below θ. The chain condition also
preserves each checked cardinal at and above θ.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion bSet Lattice
open scoped Flypitch
universe u

namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}}

instance fullCompletionNontrivial [Nonempty (Full κ θ)] :
    NontrivialCompleteBooleanAlgebra (Completion (Full κ θ)) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

variable (hθ : θ.IsInaccessible) (hκθ : κ < θ) (hκ : Cardinal.aleph0 ≤ κ)

include hθ hκθ hκ in
theorem full_completion_cardinal_le : Cardinal.mk (Completion (Full κ θ)) ≤ θ :=
  (completion_cardinal_le_small_subsets θ
    (fun a hp hd => full_completion_disjoint_family_cardinal_lt hθ hκθ hκ a hp hd)).trans
    (Erdos1172SmallSubsetCardinality.small_subsets_cardinal_le θ hθ
      (full_cardinal_le hθ hκθ (Cardinal.aleph0_pos.trans_le hκ)))

include hθ hκθ hκ in
theorem full_short_coefficients_cardinal_le {I : Type u} (hI : Cardinal.mk I < θ) :
    Cardinal.mk (I → Completion (Full κ θ)) ≤ θ := by
  let B := Completion (Full κ θ)
  have hprod : Cardinal.mk (I × B) ≤ θ := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact (mul_le_mul' hI.le (full_completion_cardinal_le hθ hκθ hκ)).trans_eq
      (Cardinal.mul_eq_self hθ.aleph0_lt.le)
  let code (f : I → B) : {s : Set (I × B) // Cardinal.mk s < θ} :=
    ⟨Set.range (fun i => (i, f i)), Cardinal.mk_range_le.trans_lt hI⟩
  have hi : Function.Injective code := by
    intro f g he
    funext i
    have hm := (Set.ext_iff.mp (congrArg Subtype.val he) (i, f i)).mp (Set.mem_range_self i)
    obtain ⟨j, hj⟩ := hm
    obtain rfl : j = i := congrArg Prod.fst hj
    exact (congrArg Prod.snd hj).symm
  exact (Cardinal.mk_le_of_injective hi).trans
    (Erdos1172SmallSubsetCardinality.small_subsets_cardinal_le θ hθ hprod)

variable [Nonempty (Full κ θ)]
include hθ hκθ hκ

theorem full_checked_powerset_injects_upper (μ : Cardinal.{u}) (hμ : μ < θ) :
    (⊤ : Completion (Full κ θ)) ≤ injects_into (bv_powerset (check (PSet.ordinalMk μ.ord)))
      (check (PSet.ordinalMk θ.ord)) := by
  apply ErdosGroundIndexNameBound.powerset_injects_checked_cardinal_of_index_cardinal_le
  apply full_short_coefficients_cardinal_le hθ hκθ hκ
  simpa only [check_type', PSet.ordinalMk_type, Cardinal.mk_ord_toType] using hμ

theorem full_checked_injects_predecessor_eq_bot (μ : Cardinal.{u}) (hμ : θ ≤ μ)
    (γ : Ordinal.{u}) (hγ : γ < μ.ord) :
    (injects_into (check (PSet.ordinalMk μ.ord)) (check (PSet.ordinalMk γ)) :
      Completion (Full κ θ)) = ⊥ := by
  have hs := ErdosCardinalPreservation.surjects_onto_eq_bot_of_cardinal_lt hθ.isRegular
    (fun w hp hd => full_completion_disjoint_family_cardinal_lt hθ hκθ hκ w hp hd)
    (PSet.ordinalMk γ) (PSet.ordinalMk μ.ord)
    (by simpa only [PSet.ordinalMk_card, Cardinal.card_ord] using Cardinal.lt_ord.mp hγ)
    (by simpa only [PSet.ordinalMk_card, Cardinal.card_ord] using hμ) (PSet.ordinalMk_inj _)
  have hm : (⊤ : Completion (Full κ θ)) ≤ exists_mem (check (PSet.ordinalMk μ.ord)) := by
    obtain ⟨x, hx⟩ := PSet.exists_mem_of_nonzero (Cardinal.ord_pos.mpr (hθ.pos.trans_le hμ))
    exact le_iSup_of_le (check x) (check_mem hx)
  exact bot_unique ((surjects_onto_of_injects_into' le_rfl (le_top.trans hm)).trans_eq hs)

theorem full_checked_initialOrdinal (μ : Cardinal.{u}) (hμ : θ ≤ μ) :
    (⊤ : Completion (Full κ θ)) ≤ ErdosHartogs.initialOrdinal (check (PSet.ordinalMk μ.ord)) := by
  refine le_inf (check_Ord (PSet.Ord_mk μ.ord)) ?_
  rw [← bounded_forall (h_congr := B_ext_neg (h := B_ext_injects_into_right))]
  rw [PSet.ordinalMk_eq_def μ.ord, check_unfold]
  change (⊤ : Completion (Full κ θ)) ≤ ⨅ i : μ.ord.ToType, _root_.imp ⊤
    (injects_into (check (PSet.mk μ.ord.ToType fun j => PSet.ordinalMk j.toOrd.val))
      (check (PSet.ordinalMk i.toOrd.val)))ᶜ
  apply le_iInf
  intro i
  rw [top_imp, ← PSet.ordinalMk_eq_def, full_checked_injects_predecessor_eq_bot hθ hκθ hκ
    μ hμ _ i.toOrd.property, compl_bot]

end Erdos1172Shioya.LevyProduct
