/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ConvergentCore
public import Mathlib.Order.Preorder.Chain

@[expose] public section

/-!
# Pulling clique decisions through a countably closed order

This is the combinatorial transfer used by the closed-forcing route to
BHT's large core: only omegaOne many decisions are needed to recover a
clique of cardinality at most alephOne. No lower bound of the completed
omegaOne sequence is asserted or needed.

The file proves the transfer from explicit dense, persistent decisions.
It does not posit a generic extension, prove a forcing theorem, or add
the auxiliary domination principle to GCH.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3ClosedDecisionSystem

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ConvergentCore (mk_Iio_W1_lt)

/-- Smaller conditions carry more information. Every countable nonempty
chain has a common strengthening. -/
def CountablyClosed (P : Type) [Preorder P] : Prop :=
  ∀ s : Set P, s.Nonempty → s.Countable → IsChain (· ≤ ·) s →
    ∃ p : P, ∀ q ∈ s, p ≤ q

def DenseBelow {P : Type} [Preorder P] (s : Set P) : Prop :=
  ∀ p : P, ∃ q ∈ s, q ≤ p

/-- The omegaOne-length Rasiowa--Sikorski construction. Closure is used
only at its countable proper stages, not after all omegaOne decisions. -/
theorem exists_antitone_dense_sequence {P : Type} [Preorder P]
    (hclosed : CountablyClosed P) (p0 : P) (D : W1 → Set P)
    (hD : ∀ i, DenseBelow (D i)) :
    ∃ f : W1 → P, Antitone f ∧ (∀ i, f i ≤ p0) ∧ ∀ i, f i ∈ D i := by
  classical
  let Candidate (i : W1) (previous : ∀ j, j < i → P) (p : P) : Prop :=
    p ≤ p0 ∧ p ∈ D i ∧ ∀ j (hj : j < i), p ≤ previous j hj
  let next (i : W1) (previous : ∀ j, j < i → P) : P :=
    if h : ∃ p, Candidate i previous p then h.choose else p0
  let branch : W1 → P := WellFoundedLT.fix next
  have hbranch (i : W1) : branch i = next i (fun j _ => branch j) := by
    dsimp only [branch]
    rw [WellFoundedLT.fix_eq]
  have hspec : ∀ i : W1, Candidate i (fun j _ => branch j) (branch i) := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      let prior : Set P := Set.range (fun j : Set.Iio i => branch j.val)
      have hcount : prior.Countable := by
        apply Cardinal.le_aleph0_iff_set_countable.mp
        exact Cardinal.mk_range_le.trans (Cardinal.lt_aleph_one_iff.mp (mk_Iio_W1_lt i))
      have hchain : IsChain (· ≤ ·) (insert p0 prior) := by
        intro p hp q hq _
        rcases Set.mem_insert_iff.mp hp with rfl | ⟨j, rfl⟩ <;>
          rcases Set.mem_insert_iff.mp hq with rfl | ⟨k, rfl⟩
        · exact Or.inl le_rfl
        · exact Or.inr (ih k.val k.property).1
        · exact Or.inl (ih j.val j.property).1
        · rcases le_total j.val k.val with hjk | hkj
          · rcases hjk.eq_or_lt with heq | hlt
            · exact Or.inl (congrArg branch heq).le
            · exact Or.inr ((ih k.val k.property).2.2 j.val hlt)
          · rcases hkj.eq_or_lt with heq | hlt
            · exact Or.inl (congrArg branch heq.symm).le
            · exact Or.inl ((ih j.val j.property).2.2 k.val hlt)
      obtain ⟨lower, hlower⟩ := hclosed (insert p0 prior) (Set.insert_nonempty _ _)
        (hcount.insert p0) hchain
      obtain ⟨p, hpD, hplower⟩ := hD i lower
      have hex : ∃ p, Candidate i (fun j _ => branch j) p := by
        refine ⟨p, hplower.trans (hlower p0 (Set.mem_insert _ _)), hpD, ?_⟩
        intro j hj
        exact hplower.trans (hlower (branch j) (Or.inr ⟨⟨j, hj⟩, rfl⟩))
      rw [hbranch]
      simpa only [next, dif_pos hex] using hex.choose_spec
  refine ⟨branch, ?_, fun i => (hspec i).1, fun i => (hspec i).2.1⟩
  intro i j hij
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hspec j).2.2 i hlt

/-- A name-like system of decisions, expressed entirely in the ground
types. The compatibility conditions are explicit mathematical premises;
constructing such a system for the BHT argument is a separate obligation. -/
structure CliqueDecisions (P I V : Type) [Preorder P] [LinearOrder I] [LinearOrder V]
    (G : SimpleGraph V) where
  decides : P → I → V → Prop
  dense : ∀ p i, ∃ q, q ≤ p ∧ ∃ v, decides q i v
  persistent : ∀ {p q i v}, q ≤ p → decides p i v → decides q i v
  unique : ∀ {p i v w}, decides p i v → decides p i w → v = w
  ordered : ∀ {p i j v w}, i < j → decides p i v → decides p j w → v < w
  adjacent : ∀ {p i j v w}, i ≠ j → decides p i v → decides p j w → G.Adj v w

/-- Recover the entire small clique by deciding its elements along one
descending omegaOne sequence. Pairwise compatibility is witnessed at the
later of the two decision stages. -/
theorem CliqueDecisions.exists_clique_map
    {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]
    {G : SimpleGraph V} (sys : CliqueDecisions P I V G)
    (hclosed : CountablyClosed P) (p0 : P) (hI : #I ≤ ℵ_ 1) :
    ∃ f : I → V, StrictMono f ∧ G.IsClique (Set.range f) := by
  classical
  obtain ⟨index⟩ : Nonempty (I ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hI)
  let D (j : W1) : Set P := {p | ∀ i, index i = j → ∃ v, sys.decides p i v}
  have hD : ∀ j, DenseBelow (D j) := by
    intro j p
    by_cases h : ∃ i, index i = j
    · obtain ⟨q, hqp, v, hv⟩ := sys.dense p h.choose
      refine ⟨q, ?_, hqp⟩
      intro i hi
      have heq : i = h.choose := index.injective (hi.trans h.choose_spec.symm)
      subst i
      exact ⟨v, hv⟩
    · exact ⟨p, fun i hi => (h ⟨i, hi⟩).elim, le_rfl⟩
  obtain ⟨conditions, hanti, _, hconditions⟩ := exists_antitone_dense_sequence hclosed p0 D hD
  have hdec (i : I) : ∃ v, sys.decides (conditions (index i)) i v :=
    hconditions (index i) i rfl
  let f (i : I) : V := (hdec i).choose
  have hf (i : I) : sys.decides (conditions (index i)) i (f i) := (hdec i).choose_spec
  have common (i j : I) : ∃ p, sys.decides p i (f i) ∧ sys.decides p j (f j) := by
    refine ⟨conditions (max (index i) (index j)), ?_, ?_⟩
    · exact sys.persistent (hanti (le_max_left _ _)) (hf i)
    · exact sys.persistent (hanti (le_max_right _ _)) (hf j)
  have hstrict : StrictMono f := by
    intro i j hij
    obtain ⟨p, hpi, hpj⟩ := common i j
    exact sys.ordered hij hpi hpj
  refine ⟨f, hstrict, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
  obtain ⟨p, hpi, hpj⟩ := common i j
  exact sys.adjacent (fun heq => hne (congrArg f heq)) hpi hpj

theorem CliqueDecisions.exists_clique_type
    {P I V : Type} [Preorder P] [LinearOrder I] [WellFoundedLT I]
    [LinearOrder V] [WellFoundedLT V]
    {G : SimpleGraph V} (sys : CliqueDecisions P I V G)
    (hclosed : CountablyClosed P) (p0 : P) (hI : #I ≤ ℵ_ 1) :
    ∃ s : Set V, G.IsClique s ∧ typeLT s = typeLT I := by
  obtain ⟨f, hf, hclique⟩ := sys.exists_clique_map hclosed p0 hI
  exact ⟨Set.range f, hclique, Ordinal.typeLT_range_of_strictMono f hf⟩

end Erdos1172Part3ClosedDecisionSystem
