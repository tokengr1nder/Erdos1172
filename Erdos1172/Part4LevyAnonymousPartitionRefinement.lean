/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousCheckedSequenceReading

@[expose] public section

/-!
# Local refinement of countably many Boolean partitions

Below a positive condition, a single strengthening identifies every column
of every ambient partition with a value in the anonymous algebra. All the
anonymous rows partition a common positive source support.
-/

set_option autoImplicit false
noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosNameTransport ErdosOmegaSequence ErdosBoundedFunctionValue
  Erdos1172CompleteSubalgebra

private theorem membership_checked_labels {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (A : PSet.{u}) (x : bSet B) :
    x ∈ᴮ check A = ⨆ i : A.Type, x =ᴮ check (A.Func i) := by
  cases A with
  | mk I l =>
    change (⨆ i : I, (⊤ : B) ⊓ (x =ᴮ check (l i))) = ⨆ i : I, x =ᴮ check (l i)
    simp only [top_inf_eq]

private theorem localized_partition_eq {C : Type u} [CompleteBooleanAlgebra C]
    {I : Type u} (d : C) (a b : I → C)
    (Hcov : d ≤ ⨆ j, a j) (Hsep : ∀ i j, i ≠ j → b i ⊓ b j = ⊥)
    (Hab : ∀ j, d ⊓ a j ≤ b j) (i : I) : d ⊓ b i = d ⊓ a i := by
  apply le_antisymm _ (le_inf inf_le_left (Hab i))
  apply le_inf inf_le_left
  apply (le_inf (le_refl (d ⊓ b i)) (inf_le_left.trans Hcov)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  by_cases h : i = j
  · subst j
    exact inf_le_right
  · have hz : (d ⊓ b i) ⊓ a j ≤ b i ⊓ b j :=
      le_inf (inf_le_left.trans inf_le_right)
        ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans (Hab j))
    rw [Hsep i j h] at hz
    exact hz.trans bot_le

/-- The ambient rows may cover only the original condition. All source
rows have the same support, and one positive ambient condition witnesses
all of the equalities simultaneously. -/
theorem exists_anonymous_partition_refinement (κ : Cardinal.{u}) (Hκ : κ.IsRegular)
    (Hunc : Cardinal.aleph0 < κ) (A : PSet.{u})
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (a : ℕ → A.Type → Algebra κ) (Γ : Algebra κ) (HΓ : Γ ≠ ⊥)
    (Hdisj : ∀ n i j, i ≠ j → a n i ⊓ a n j = ⊥)
    (Hcov : ∀ n, Γ ≤ ⨆ i, a n i) :
    ∃ (d : Algebra κ) (s : anonymousAlgebra κ) (b : ℕ → A.Type → anonymousAlgebra κ),
      d ≠ ⊥ ∧ d ≤ Γ ∧ s ≠ ⊥ ∧ d ≤ inclusion (anonymousAlgebra κ) s ∧
      (∀ n, (⨆ i, b n i) = s) ∧
      (∀ n i j, i ≠ j → b n i ⊓ b n j = ⊥) ∧
      ∀ n i, d ⊓ inclusion (anonymousAlgebra κ) (b n i) = d ⊓ a n i := by
  classical
  let e := inclusion (anonymousAlgebra κ)
  let label := fun i : A.Type => (check (A.Func i) : bSet (Algebra κ))
  let v := fun n => mixture (a n) label
  have Hmix : ∀ n i, a n i ≤ v n =ᴮ label i := by
    intro n
    apply mixing_lemma'
    intro i j
    by_cases h : i = j
    · subst j
      exact bv_refl
    · exact (Hdisj n i j h).le.trans bot_le
  have Hmem : ∀ n, Γ ≤ v n ∈ᴮ check A := by
    intro n
    rw [membership_checked_labels]
    exact (Hcov n).trans (iSup_mono (Hmix n))
  let f := sequenceGraph v
  let S := fun g : bSet (anonymousAlgebra κ) => is_function omega (check A) g
  let U := fun g : bSet (anonymousAlgebra κ) => e (S g) ⊓ (f =ᴮ mapNames e g)
  have Hread : Γ ≤ ⨆ g, U g :=
    anonymous_checked_sequence_reading_cover κ Hκ Hunc A Hsep (sequenceGraph_is_function Hmem)
  obtain ⟨g, Hd⟩ : ∃ g, Γ ⊓ U g ≠ ⊥ := by
    by_contra! Hzero
    apply HΓ
    apply bot_unique
    apply (le_inf le_rfl Hread).trans
    rw [inf_iSup_eq]
    exact iSup_le fun g => (Hzero g).le
  let d := Γ ⊓ U g
  let s := S g
  have Hds : d ≤ e s := inf_le_right.trans inf_le_left
  have Hdg : d ≤ f =ᴮ mapNames e g := inf_le_right.trans inf_le_right
  let z := fun n : ℕ => graphValue (check A) g (of_nat n)
  let b := fun n i => s ⊓ (z n =ᴮ check (A.Func i))
  have Hrow : ∀ n, (⨆ i, b n i) = s := by
    intro n
    change (⨆ i, s ⊓ (z n =ᴮ check (A.Func i))) = s
    rw [← inf_iSup_eq, ← membership_checked_labels, inf_eq_left]
    exact graphValue_mem (D := omega) (V := check A) (F := g) (Γ := s) le_rfl of_nat_mem_omega
  have HsepB : ∀ n i j, i ≠ j → b n i ⊓ b n j = ⊥ := by
    intro n i j hij
    apply bot_unique
    have h : b n i ⊓ b n j ≤ (check (A.Func i) : bSet (anonymousAlgebra κ)) =ᴮ
        check (A.Func j) :=
      bv_trans (bv_symm (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)
    exact h.trans_eq (check_bv_eq_bot_of_not_equiv (Hsep i j hij))
  refine ⟨d, s, b, Hd, inf_le_left, ?_, Hds, Hrow, HsepB, ?_⟩
  · intro h
    apply Hd
    exact bot_unique (Hds.trans_eq (by rw [h, map_bot]))
  · intro n
    have Hpair : s ≤ pair (of_nat n) (z n) ∈ᴮ g :=
      graphValue_pair_mem (D := omega) (V := check A) (F := g) le_rfl of_nat_mem_omega
    have Hmapped : d ≤ pair (of_nat n) (mapNames e (z n)) ∈ᴮ mapNames e g := by
      have h := Hds.trans (OrderHomClass.mono e Hpair)
      simpa only [map_mem, map_pair, of_nat, map_check] using h
    have Hz : d ≤ v n =ᴮ mapNames e (z n) :=
      bv_symm (pair_of_nat_mem_iff.mp (mem_congr bv_refl (bv_symm Hdg) Hmapped))
    apply localized_partition_eq d (a n) (fun i => e (b n i)) (inf_le_left.trans (Hcov n))
    · intro i j hij
      rw [← map_inf, HsepB n i j hij, map_bot]
    · intro i
      change d ⊓ a n i ≤ e s ⊓ e (z n =ᴮ check (A.Func i))
      rw [map_bv_eq, map_check]
      exact le_inf (inf_le_left.trans Hds)
        (bv_trans (bv_symm (inf_le_left.trans Hz)) (inf_le_right.trans (Hmix n i)))

/-- Every ground index type can be labelled by distinct ground ordinals.
The simultaneous refinement therefore applies to partitions of any width. -/
theorem exists_anonymous_indexed_partition_refinement (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) (I : Type u)
    (a : ℕ → I → Algebra κ) (Γ : Algebra κ) (HΓ : Γ ≠ ⊥)
    (Hdisj : ∀ n i j, i ≠ j → a n i ⊓ a n j = ⊥)
    (Hcov : ∀ n, Γ ≤ ⨆ i, a n i) :
    ∃ (d : Algebra κ) (s : anonymousAlgebra κ) (b : ℕ → I → anonymousAlgebra κ),
      d ≠ ⊥ ∧ d ≤ Γ ∧ s ≠ ⊥ ∧ d ≤ inclusion (anonymousAlgebra κ) s ∧
      (∀ n, (⨆ i, b n i) = s) ∧
      (∀ n i j, i ≠ j → b n i ⊓ b n j = ⊥) ∧
      ∀ n i, d ⊓ inclusion (anonymousAlgebra κ) (b n i) = d ⊓ a n i := by
  let O := PSet.ordinalMk (Cardinal.mk I).ord
  have hcard : Cardinal.mk I ≤ Cardinal.mk O.Type := by
    simpa only [O, PSet.ordinalMk_type, Cardinal.mk_ord_toType] using
      (le_rfl : Cardinal.mk I ≤ Cardinal.mk I)
  obtain ⟨j⟩ := (Cardinal.le_def I O.Type).mp hcard
  let A : PSet.{u} := .mk I (fun i => O.Func (j i))
  refine exists_anonymous_partition_refinement κ Hκ Hunc A ?_ a Γ HΓ Hdisj Hcov
  intro i k hik
  exact PSet.ordinalMk_inj (Cardinal.mk I).ord (j i) (j k) (fun he => hik (j.injective he))

end Erdos1172LevyCohen
