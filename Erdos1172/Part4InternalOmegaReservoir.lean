/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalLargeDifference
public import Erdos1172.Part4InternalGraphNeighborhood
public import Erdos1172.Part4InternalOmegaSequenceColor

@[expose] public section

/-!
The countable-clique branch of the internal Dushnik--Miller construction.
The hypothesis quantifies all large internal subreservoirs. Fullness and
recursion construct the sequence; no coherent sequence is assumed.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaReservoir

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosGraphNeighborhood

/-- Every internally omega-two-large subreservoir contains a point with an
internally omega-two-large neighborhood of the specified color. -/
noncomputable def richNeighborhoods (color : Bool) (R S : bSet 𝔹) : 𝔹 :=
  ⨅ X, _root_.imp (X ⊆ᴮ S ⊓ injects_into omegaTwo X)
    (⨆ x, x ∈ᴮ X ⊓ injects_into omegaTwo (neighborhood color R X x))

theorem richNeighborhoods_apply {color : Bool} {R S X : bSet 𝔹} {Γ : 𝔹}
    (Hrich : Γ ≤ richNeighborhoods color R S)
    (HXS : Γ ≤ X ⊆ᴮ S) (HX : Γ ≤ injects_into omegaTwo X) :
    Γ ≤ ⨆ x, x ∈ᴮ X ⊓ injects_into omegaTwo (neighborhood color R X x) :=
  (le_inf (Hrich.trans (iInf_le _ X)) (le_inf HXS HX)).trans bv_imp_elim

theorem above_of_not_mem_succ {a y : bSet 𝔹} {Γ : 𝔹}
    (Ha : Γ ≤ a ∈ᴮ omegaTwo) (Hy : Γ ≤ y ∈ᴮ omegaTwo)
    (Hnot : Γ ≤ (y ∈ᴮ succ a)ᶜ) : Γ ≤ a ∈ᴮ y := by
  have Htri := epsilon_trichotomy_of_Ord Hy Ha (omegaTwo_Ord (Γ := Γ))
  apply (le_inf (le_refl Γ) Htri).trans
  rw [inf_sup_left]
  apply sup_le
  · have Hsucc : y ∈ᴮ succ a = y =ᴮ a ⊔ y ∈ᴮ a := mem_insert1
    exact (bv_absurd _ (inf_le_right.trans Hsucc.ge)
      (inf_le_left.trans Hnot)).trans bot_le
  · exact inf_le_right

/-- One genuine recursive step, retaining full largeness and placing the
next reservoir strictly above the chosen vertex in the same color. -/
theorem exists_reservoir_step {color : Bool} {R S X : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hrich : Γ ≤ richNeighborhoods color R S)
    (HXS : Γ ≤ X ⊆ᴮ S) (HX : Γ ≤ injects_into omegaTwo X) :
    ∃ x Y : bSet 𝔹, (Γ ≤ x ∈ᴮ X) ∧ (Γ ≤ Y ⊆ᴮ X) ∧
      (Γ ≤ injects_into omegaTwo Y) ∧
      ∀ y : bSet 𝔹, Γ ≤ y ∈ᴮ Y → Γ ≤ x ∈ᴮ y ⊓ graphColor color R x y := by
  obtain ⟨x, Hx⟩ := exists_large_neighborhood (richNeighborhoods_apply Hrich HXS HX)
  have HxX : Γ ≤ x ∈ᴮ X := Hx.1
  have HxTwo : Γ ≤ x ∈ᴮ omegaTwo :=
    mem_of_mem_subset HS (mem_of_mem_subset HXS HxX)
  let Y := difference (neighborhood color R X x) (succ x)
  have HYX : Γ ≤ Y ⊆ᴮ X := subset_trans' difference_subset neighborhood_subset
  have HYlarge : Γ ≤ injects_into omegaTwo Y :=
    ErdosLargeDifference.omegaTwo_injects_difference_succ HCH
      Hx.2 HxTwo
  refine ⟨x, Y, HxX, HYX, HYlarge, ?_⟩
  intro y Hy
  have HY : Γ ≤ y ∈ᴮ neighborhood color R X x ⊓ (y ∈ᴮ succ x)ᶜ := by
    simpa only [Y, mem_difference] using Hy
  have HN : Γ ≤ y ∈ᴮ X ⊓ graphColor color R x y := by
    rw [← mem_neighborhood]
    exact HY.trans inf_le_left
  exact le_inf
    (above_of_not_mem_succ HxTwo
      (mem_of_mem_subset HS (mem_of_mem_subset HXS (HN.trans inf_le_left)))
      (HY.trans inf_le_right)) (HN.trans inf_le_right)

/-- Fullness supplies coherent name-valued choices at one fixed Boolean
condition; recursion and nested reservoirs prove every required pair law. -/
theorem exists_increasing_colored_sequence {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S)
    (Hrich : Γ ≤ richNeighborhoods color R S) :
    ∃ v : ℕ → bSet 𝔹, (∀ n, Γ ≤ v n ∈ᴮ S) ∧
      ∀ m n, m < n → Γ ≤ v m ∈ᴮ v n ⊓ graphColor color R (v m) (v n) := by
  classical
  let State := {X : bSet 𝔹 // (Γ ≤ X ⊆ᴮ S) ∧ (Γ ≤ injects_into omegaTwo X)}
  have hstep : ∀ q : State, ∃ p : bSet 𝔹 × State,
      (Γ ≤ p.1 ∈ᴮ q.val) ∧ (Γ ≤ p.2.val ⊆ᴮ q.val) ∧
      ∀ y : bSet 𝔹, Γ ≤ y ∈ᴮ p.2.val →
        Γ ≤ p.1 ∈ᴮ y ⊓ graphColor color R p.1 y := by
    intro q
    obtain ⟨x, Y, Hx, HY, HYL, Hpair⟩ :=
      exists_reservoir_step HCH HS Hrich q.property.1 q.property.2
    exact ⟨(x, ⟨Y, subset_trans' HY q.property.1, HYL⟩), Hx, HY, Hpair⟩
  choose next hnext using hstep
  let initial : State := ⟨S, subset_self, Hlarge⟩
  let states : ℕ → State := Nat.rec initial (fun _ q => (next q).2)
  let v : ℕ → bSet 𝔹 := fun n => (next (states n)).1
  have Hv (n : ℕ) : Γ ≤ v n ∈ᴮ (states n).val := (hnext (states n)).1
  have Hdown (n : ℕ) : Γ ≤ (states (n + 1)).val ⊆ᴮ (states n).val :=
    (hnext (states n)).2.1
  have HdownAll : ∀ n m : ℕ, m ≤ n → Γ ≤ (states n).val ⊆ᴮ (states m).val := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have heq : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact subset_self
    | succ n ih =>
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · subst m
        exact subset_self
      · exact subset_trans' (Hdown n) (ih m (by omega))
  refine ⟨v, fun n => mem_of_mem_subset (states n).property.1 (Hv n), ?_⟩
  intro m n hmn
  exact (hnext (states m)).2.2 (v n)
    (mem_of_mem_subset (HdownAll n (m + 1) (by omega)) (Hv n))

/-- An actual internal increasing injection with homogeneous range is
constructed, including its behavior on arbitrary mixed natural names. -/
theorem exists_internal_omega_clique {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S)
    (Hrich : Γ ≤ richNeighborhoods color R S) :
    ∃ f : bSet 𝔹, Γ ≤ is_injective_function bSet.omega S f ⊓
      (increasingOn bSet.omega f ⊓ homogeneousUnion color R bSet.omega bSet.omega f f) := by
  obtain ⟨v, Hv, Hpair⟩ := exists_increasing_colored_sequence HCH HS Hlarge Hrich
  have Hinc : ∀ m n, m < n → Γ ≤ v m ∈ᴮ v n :=
    fun m n h => (Hpair m n h).trans inf_le_left
  have Hcolor : ∀ m n, m < n → Γ ≤ graphColor color R (v m) (v n) :=
    fun m n h => (Hpair m n h).trans inf_le_right
  exact ⟨ErdosOmegaSequence.sequenceGraph v,
    le_inf (ErdosOmegaSequence.sequenceGraph_is_injective Hv Hinc)
      (le_inf (ErdosOmegaSequence.sequenceGraph_increasing Hinc)
        (ErdosOmegaSequence.sequenceGraph_homogeneousUnion Hcolor))⟩

theorem internal_omega_clique_value {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S)
    (Hrich : Γ ≤ richNeighborhoods color R S) :
    Γ ≤ ⨆ f, is_injective_function bSet.omega S f ⊓
      (increasingOn bSet.omega f ⊓ homogeneousUnion color R bSet.omega bSet.omega f f) := by
  obtain ⟨f, Hf⟩ := exists_internal_omega_clique HCH HS Hlarge Hrich
  exact le_iSup_of_le f Hf

end bSet.ErdosOmegaReservoir
