/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetBooleanCompletion
public import Mathlib.Order.Zorn
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

/-!
# Antichain representations of actual Boolean-completion values

Every regular lower set is the supremum of a pairwise disjoint family of
actual principal-condition values. The family is constructed by Zorn's
lemma and density of the original conditions, not supplied as a premise.
A proved chain condition then bounds the size of these representations.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172PosetCompletion

variable {P : Type u} [Preorder P]

theorem exists_condition_antichain_sup (b : Completion P) :
    ∃ A : Set P, (∀ p ∈ A, condition p ≤ b) ∧
      A.Pairwise (fun p q => condition p ⊓ condition q = ⊥) ∧
      (⨆ p : A, condition p.val) = b := by
  classical
  obtain ⟨A, _, hA⟩ := zorn_subset_nonempty
    {A : Set P | (∀ p ∈ A, condition p ≤ b) ∧
      A.Pairwise (fun p q => condition p ⊓ condition q = ⊥)}
    (fun chain hchain hordered _ => by
      refine ⟨⋃₀ chain, ⟨?_, ?_⟩, ?_⟩
      · rintro p ⟨s, hs, hps⟩
        exact (hchain hs).1 p hps
      · rintro p ⟨s, hs, hps⟩ q ⟨t, ht, hqt⟩ hpq
        rcases hordered.total hs ht with hst | hts
        · exact (hchain ht).2 (hst hps) hqt hpq
        · exact (hchain hs).2 hps (hts hqt) hpq
      · exact fun s hs => Set.subset_sUnion_of_mem hs)
    ∅ ⟨by intro p hp; exact hp.elim, by intro p hp; exact hp.elim⟩
  refine ⟨A, hA.1.1, hA.1.2, ?_⟩
  apply le_antisymm
  · exact iSup_le (fun p => hA.1.1 p.val p.property)
  · by_contra h
    have hres : b ⊓ (⨆ p : A, condition p.val)ᶜ ≠ ⊥ := by
      intro heq
      exact h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr heq.le))
    obtain ⟨p, hp⟩ := exists_condition_le hres
    have hpb : condition p ≤ b := hp.trans inf_le_left
    have hpc : condition p ≤ (⨆ q : A, condition q.val)ᶜ := hp.trans inf_le_right
    have hdisj : ∀ q ∈ A, condition p ⊓ condition q = ⊥ := by
      intro q hq
      apply bot_unique
      have hqs : condition q ≤ ⨆ r : A, condition r.val :=
        le_iSup (fun r : A => condition r.val) ⟨q, hq⟩
      exact (inf_le_inf hpc hqs).trans compl_inf_eq_bot.le
    have hpA : p ∉ A := by
      intro hpA
      exact condition_ne_bot p (bot_unique ((le_inf le_rfl le_rfl).trans (hdisj p hpA).le))
    have hinsert : (∀ q ∈ insert p A, condition q ≤ b) ∧
        (insert p A).Pairwise (fun q r => condition q ⊓ condition r = ⊥) := by
      constructor
      · intro q hq
        rcases Set.mem_insert_iff.mp hq with rfl | hq
        · exact hpb
        · exact hA.1.1 q hq
      · exact hA.1.2.insert (fun q hq _ =>
          ⟨hdisj q hq, bot_unique ((le_inf inf_le_right inf_le_left).trans (hdisj q hq).le)⟩)
    exact hpA (hA.2 hinsert (Set.subset_insert _ _) (Set.mem_insert _ _))

/-- The cardinal bound is applied to a constructed representation of each
Boolean value, not assumed as a separate density representation. -/
theorem exists_small_condition_antichain_sup (κ : Cardinal.{u})
    (Hcc : ∀ {J : Type u} (a : J → Completion P),
      (∀ j, a j ≠ ⊥) → (∀ j k, j ≠ k → a j ⊓ a k = ⊥) →
      Cardinal.mk J < κ) (b : Completion P) :
    ∃ A : Set P, Cardinal.mk A < κ ∧
      A.Pairwise (fun p q => condition p ⊓ condition q = ⊥) ∧
      (⨆ p : A, condition p.val) = b := by
  obtain ⟨A, _, hdisj, hsup⟩ := exists_condition_antichain_sup b
  refine ⟨A, ?_, hdisj, hsup⟩
  apply Hcc (fun p : A => condition p.val) (fun p => condition_ne_bot p.val)
  intro p q hpq
  exact hdisj p.property q.property (fun heq => hpq (Subtype.ext heq))

theorem completion_cardinal_le_small_subsets (κ : Cardinal.{u})
    (Hcc : ∀ {J : Type u} (a : J → Completion P),
      (∀ j, a j ≠ ⊥) → (∀ j k, j ≠ k → a j ⊓ a k = ⊥) →
      Cardinal.mk J < κ) :
    Cardinal.mk (Completion P) ≤ Cardinal.mk {A : Set P // Cardinal.mk A < κ} := by
  apply Cardinal.mk_le_of_surjective (f := fun A : {A : Set P // Cardinal.mk A < κ} =>
      ⨆ p : A.val, condition p.val)
  intro b
  obtain ⟨A, hsize, _, hsup⟩ := exists_small_condition_antichain_sup κ Hcc b
  exact ⟨⟨A, hsize⟩, hsup⟩

end Erdos1172PosetCompletion
