/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartialInjectionDomain
public import Erdos1172.Part4InternalPrefixFunction

@[expose] public section

/-!
# The internal set of small partial binary functions

Domains are arbitrary subsets of K, not ordinal initial segments. A graph
has small domain when that domain injects into some member of K. The actual
set of conditions is a separated powerset, and all its membership laws cover
arbitrary mixed graph names. No injectivity of the binary function is imposed.

The all-bottom indicator is a fixed external label representing the empty
condition. Its coefficient is top whenever zero belongs to K at top. No
generic filter, iteration, ideal, or forcing-preservation claim is made here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection ErdosRelationGraph

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def smallDomain (K p : bSet 𝔹) : 𝔹 :=
  ⨆ δ, δ ∈ᴮ K ⊓ injects_into (graphDomain K two p) δ

def condition (K p : bSet 𝔹) : 𝔹 :=
  p ⊆ᴮ prod K two ⊓ (is_func p ⊓ smallDomain K p)

def conditions (K : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun p => is_func p ⊓ smallDomain K p) (bv_powerset (prod K two))

/-- Computing the graph domain respects Boolean equality of arbitrary
graphs; neither graph is required to be a condition. -/
theorem graphDomain_congr_graph (K S : bSet 𝔹) : B_congr (graphDomain K S) := by
  intro p q Γ Hpq
  have Hext (x : bSet 𝔹) : B_ext (fun f : bSet 𝔹 =>
      x ∈ᴮ K ⊓ ⨆ y, y ∈ᴮ S ⊓ pair x y ∈ᴮ f) :=
    B_ext_inf B_ext_const (B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right))
  apply mem_ext
  · apply le_iInf
    intro x
    rw [← deduction, mem_graphDomain, mem_graphDomain]
    exact bv_rw'' (inf_le_left.trans Hpq) inf_le_right (Hext x)
  · apply le_iInf
    intro x
    rw [← deduction, mem_graphDomain, mem_graphDomain]
    exact bv_rw'' (inf_le_left.trans (bv_symm Hpq)) inf_le_right (Hext x)

theorem smallDomain_ext_graph (K : bSet 𝔹) : B_ext (smallDomain K) := by
  unfold smallDomain
  exact B_ext_iSup (h := fun δ => B_ext_inf B_ext_const
    (B_ext_term (fun A => injects_into A δ) (graphDomain K two)
      B_ext_injects_into_left (graphDomain_congr_graph K two)))

theorem condition_ext_graph (K : bSet 𝔹) : B_ext (condition K) :=
  B_ext_inf B_ext_subset_left
    (B_ext_inf ErdosPrefixFunction.is_func_ext_graph (smallDomain_ext_graph K))

theorem mem_conditions_iff {K p : bSet 𝔹} {Γ : 𝔹} : Γ ≤ p ∈ᴮ conditions K ↔ Γ ≤ condition K p := by
  unfold conditions
  rw [mem_comprehend_and
    (B_ext_inf ErdosPrefixFunction.is_func_ext_graph (smallDomain_ext_graph K))]
  constructor
  · rintro ⟨Hsub, Hlaw⟩
    exact le_inf (mem_powerset_iff.mp Hsub) Hlaw
  · intro H
    exact ⟨mem_powerset_iff.mpr (H.trans inf_le_left), H.trans inf_le_right⟩

/-- A condition is an actual supported function on its computed domain,
without asserting that this domain is an initial segment. -/
theorem condition_function {K p : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ condition K p) :
    Γ ≤ is_function (graphDomain K two p) two p :=
  function_on_graphDomain (H.trans inf_le_left) (H.trans (inf_le_right.trans inf_le_left))

theorem graphDomain_empty {K S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ graphDomain K S ∅ =ᴮ ∅ :=
  graphDomain_eq_of_function empty_subset (le_inf is_func'_empty empty_subset)

theorem empty_smallDomain {K : bSet 𝔹} {Γ : 𝔹}
    (Hzero : Γ ≤ (0 : bSet 𝔹) ∈ᴮ K) : Γ ≤ smallDomain K ∅ := by
  apply le_iSup_of_le (0 : bSet 𝔹)
  refine le_inf Hzero ?_
  exact bv_rw' (graphDomain_empty (K := K) (S := two))
    (ϕ := fun A => injects_into A (0 : bSet 𝔹))
    (h_congr := B_ext_injects_into_left)
    (H_new := injects_into_of_subset empty_subset)

theorem empty_condition {K : bSet 𝔹} {Γ : 𝔹}
    (Hzero : Γ ≤ (0 : bSet 𝔹) ∈ᴮ K) : Γ ≤ condition K ∅ :=
  le_inf empty_subset
    (le_inf ((is_func'_empty (x := two)).trans inf_le_left) (empty_smallDomain Hzero))

theorem empty_mem_conditions {K : bSet 𝔹} {Γ : 𝔹}
    (Hzero : Γ ≤ (0 : bSet 𝔹) ∈ᴮ K) : Γ ≤ (∅ : bSet 𝔹) ∈ᴮ conditions K :=
  mem_conditions_iff.mpr (empty_condition Hzero)

theorem conditions_bval_eq_condition (K : bSet 𝔹) (i : (conditions K).type) :
    (conditions K).bval i = condition K ((conditions K).func i) := by
  change (is_func ((conditions K).func i) ⊓ smallDomain K ((conditions K).func i)) ⊓
      ((conditions K).func i ⊆ᴮ prod K two) =
    ((conditions K).func i ⊆ᴮ prod K two) ⊓
      (is_func ((conditions K).func i) ⊓ smallDomain K ((conditions K).func i))
  exact inf_comm _ _

/-- A canonical label, defined without choosing a name from a Boolean join. -/
def emptyLabel (K : bSet 𝔹) : (conditions K).type := fun _ => ⊥

theorem emptyLabel_func_eq_empty {K : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (conditions K).func (emptyLabel K) =ᴮ ∅ := by
  change Γ ≤ (bSet.mk (prod K two).type (prod K two).func (fun _ => ⊥)) =ᴮ ∅
  rw [eq_empty]
  change Γ ≤ (⨆ _ : (prod K two).type, (⊥ : 𝔹))ᶜ
  simpa only [iSup_bot, compl_bot] using (le_top : Γ ≤ (⊤ : 𝔹))

theorem emptyLabel_bval {K : bSet 𝔹} {Γ : 𝔹}
    (Hzero : Γ ≤ (0 : bSet 𝔹) ∈ᴮ K) :
    Γ ≤ (conditions K).bval (emptyLabel K) := by
  rw [conditions_bval_eq_condition]
  exact bv_rw' emptyLabel_func_eq_empty (h_congr := condition_ext_graph K)
    (H_new := empty_condition Hzero)

theorem emptyLabel_bval_eq_top {K : bSet 𝔹}
    (Hzero : (⊤ : 𝔹) ≤ (0 : bSet 𝔹) ∈ᴮ K) :
    (conditions K).bval (emptyLabel K) = ⊤ :=
  top_unique (emptyLabel_bval Hzero)

end bSet.ErdosCohen
