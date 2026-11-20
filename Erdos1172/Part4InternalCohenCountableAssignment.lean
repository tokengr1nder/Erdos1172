/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenCountableUnion
public import Erdos1172.Part4InternalNameSequence

@[expose] public section

/-!
# Prescribed countable assignments to fresh internal Cohen coordinates

Starting with a locally valid graph, the literal finite stages insert the
prescribed pairs one at a time. Pairwise Boolean inequality and freshness
over the original domain preserve freshness of every future coordinate.
The actual internally countable inclusion-chain family of these stages has
a valid union, containing every prescribed pair at the original condition.

The coordinates and values may be arbitrary mixed names. Their membership,
separation, and original-domain freshness are explicit local hypotheses;
no existence of such a fresh sequence is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection ErdosInjectionExtension

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- The finite stages are actual named graphs, defined without validity or
freshness proofs and without any choice of extension witnesses. -/
def assignmentStages (p : bSet B) (a y : ℕ → bSet B) : ℕ → bSet B
  | 0 => p
  | n + 1 => bSet.insert1 (pair (a n) (y n)) (assignmentStages p a y n)

/-- Insertion cannot introduce a distinct fresh coordinate into the domain. -/
theorem not_mem_domain_insertPair_of_fresh {K p a x y : bSet B} {Γ : B}
    (Hfresh : Γ ≤ (a ∈ᴮ graphDomain K two p)ᶜ)
    (Hneq : Γ ≤ (a =ᴮ x)ᶜ) :
    Γ ≤ (a ∈ᴮ graphDomain K two (bSet.insert1 (pair x y) p))ᶜ := by
  have Hinsert : a ∈ᴮ bSet.insert1 x (graphDomain K two p) =
      (a =ᴮ x) ⊔ (a ∈ᴮ graphDomain K two p) := mem_insert1
  have Hnot : Γ ≤ (a ∈ᴮ bSet.insert1 x (graphDomain K two p))ᶜ := by
    rw [Hinsert, compl_sup]
    exact le_inf Hneq Hfresh
  rw [← imp_bot, ← deduction]
  have Hmem : Γ ⊓ a ∈ᴮ graphDomain K two (bSet.insert1 (pair x y) p) ≤
      a ∈ᴮ bSet.insert1 x (graphDomain K two p) :=
    mem_of_mem_subset graphDomain_insertPair_subset inf_le_right
  exact bv_absurd _ Hmem (inf_le_left.trans Hnot)

/-- Every stage extends all earlier stages, regardless of validity. -/
theorem assignmentStages_mono (p : bSet B) (a y : ℕ → bSet B)
    {Γ : B} (m n : ℕ) (Hmn : m ≤ n) :
    Γ ≤ assignmentStages p a y m ⊆ᴮ assignmentStages p a y n := by
  induction n generalizing m with
  | zero =>
    have Hm : m = 0 := Nat.eq_zero_of_le_zero Hmn
    subst m
    exact subset_self
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le Hmn with Heq | Hlt
    · subst m
      exact subset_self
    · exact subset_trans' (ih m (by omega))
        (subset_insertPair (a := a n) (y := y n))

/-- Validity and freshness of all not-yet-inserted coordinates are proved
together at the unchanged Boolean condition. -/
theorem assignmentStages_condition_and_fresh {K p : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (a y : ℕ → bSet B)
    (Ha : ∀ n, Γ ≤ a n ∈ᴮ K)
    (Hy : ∀ n, Γ ≤ y n ∈ᴮ two)
    (Hsep : ∀ m n, m ≠ n → Γ ≤ (a m =ᴮ a n)ᶜ)
    (Hfresh : ∀ n, Γ ≤ (a n ∈ᴮ graphDomain K two p)ᶜ)
    (n : ℕ) :
    Γ ≤ condition K (assignmentStages p a y n) ∧
      ∀ m, n ≤ m → Γ ≤ (a m ∈ᴮ graphDomain K two (assignmentStages p a y n))ᶜ := by
  induction n with
  | zero => exact ⟨Hp, fun m _ => Hfresh m⟩
  | succ n ih =>
    constructor
    · exact condition_insertPair HK ih.1 (Ha n) (ih.2 n le_rfl) (Hy n)
    · intro m Hnm
      exact not_mem_domain_insertPair_of_fresh
        (ih.2 m (by omega)) (Hsep m n (by omega))

/-- One actual condition simultaneously realizes every prescribed countable
assignment, with all conclusions at the same original Boolean condition. -/
theorem exists_countable_assignment {K p : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (a y : ℕ → bSet B)
    (Ha : ∀ n, Γ ≤ a n ∈ᴮ K)
    (Hy : ∀ n, Γ ≤ y n ∈ᴮ two)
    (Hsep : ∀ m n, m ≠ n → Γ ≤ (a m =ᴮ a n)ᶜ)
    (Hfresh : ∀ n, Γ ≤ (a n ∈ᴮ graphDomain K two p)ᶜ) :
    ∃ q : bSet B, Γ ≤ condition K q ∧ Γ ≤ p ⊆ᴮ q ∧
      ∀ n, Γ ≤ pair (a n) (y n) ∈ᴮ q := by
  let s : ℕ → bSet B := assignmentStages p a y
  have Hstage (n : ℕ) : Γ ≤ condition K (s n) :=
    (assignmentStages_condition_and_fresh HK Hp a y Ha Hy Hsep Hfresh n).1
  let q : bSet B := bv_union (ErdosNameSequence.family s)
  have Hq : Γ ≤ condition K q :=
    condition_union_of_countable_chain HK
      (ErdosNameSequence.family_subset (fun n => mem_conditions_iff.mpr (Hstage n)))
      (ErdosNameSequence.family_inclusionChain
        (fun m n Hmn => assignmentStages_mono p a y m n Hmn))
      (ErdosNameSequence.family_countable s)
  refine ⟨q, Hq, ErdosNameSequence.term_subset_union s 0, ?_⟩
  intro n
  have Hpair : Γ ≤ pair (a n) (y n) ∈ᴮ s (n + 1) := pair_mem_insertPair
  exact mem_of_mem_subset (ErdosNameSequence.term_subset_union s (n + 1)) Hpair

end bSet.ErdosCohen
