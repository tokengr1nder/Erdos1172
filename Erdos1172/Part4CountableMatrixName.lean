/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaSequence

@[expose] public section

/-!
# A surjection name constructed from a Boolean collapse matrix

Mix each row and form the actual graph on internal omega. Disjoint rows
give coherent values, row joins give totality, and column joins give
surjectivity. Every quantifier in the conclusion ranges over arbitrary
internal names, including mixed naturals and mixed target elements.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableMatrix

open ErdosOmegaSequence

variable {β : Type u} [NontrivialCompleteBooleanAlgebra β]
variable {α : Type u}

def rowName (M : ℕ → α → β) (Y : α → bSet β) (n : ℕ) : bSet β :=
  mixture (M n) Y

def graph (M : ℕ → α → β) (Y : α → bSet β) : bSet β :=
  sequenceGraph (rowName M Y)

theorem rowName_agrees (M : ℕ → α → β) (Y : α → bSet β)
    (Hdisj : ∀ n a b, a ≠ b → M n a ⊓ M n b = ⊥)
    (n : ℕ) (a : α) : M n a ≤ rowName M Y n =ᴮ Y a := by
  apply mixing_lemma'
  intro i j
  by_cases hij : i = j
  · subst j
    exact bv_refl
  · rw [Hdisj n i j hij]
    exact bot_le

theorem rowName_mem (M : ℕ → α → β) (Y : α → bSet β)
    (Hdisj : ∀ n a b, a ≠ b → M n a ⊓ M n b = ⊥)
    (Hrow : ∀ n, (⨆ a, M n a) = ⊤) (n : ℕ) :
    (⊤ : β) ≤ rowName M Y n ∈ᴮ check'' Y := by
  rw [← Hrow n]
  apply iSup_le
  intro a
  apply bv_rw' (rowName_agrees M Y Hdisj n a) (h_congr := B_ext_mem_left)
  exact le_top.trans (mem_mk' (check'' Y) a)

theorem graph_is_function (M : ℕ → α → β) (Y : α → bSet β)
    (Hdisj : ∀ n a b, a ≠ b → M n a ⊓ M n b = ⊥)
    (Hrow : ∀ n, (⨆ a, M n a) = ⊤) :
    (⊤ : β) ≤ is_function omega (check'' Y) (graph M Y) :=
  sequenceGraph_is_function (rowName_mem M Y Hdisj Hrow)

theorem graph_pair_of_weight (M : ℕ → α → β) (Y : α → bSet β)
    (Hdisj : ∀ n a b, a ≠ b → M n a ⊓ M n b = ⊥)
    (n : ℕ) (a : α) :
    M n a ≤ pair (of_nat n) (Y a) ∈ᴮ graph M Y :=
  pair_of_nat_mem_iff.mpr (bv_symm (rowName_agrees M Y Hdisj n a))

theorem graph_is_surj (M : ℕ → α → β) (Y : α → bSet β)
    (Hdisj : ∀ n a b, a ≠ b → M n a ⊓ M n b = ⊥)
    (Hcol : ∀ a, (⨆ n, M n a) = ⊤) :
    (⊤ : β) ≤ is_surj omega (check'' Y) (graph M Y) := by
  unfold is_surj
  rw [← bounded_forall (h_congr := B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_const B_ext_pair_mem_right))]
  apply le_iInf
  intro a
  change (⊤ : β) ≤ _root_.imp ⊤
    (⨆ w, w ∈ᴮ omega ⊓ pair w (Y a) ∈ᴮ graph M Y)
  rw [top_imp, ← Hcol a]
  apply iSup_le
  intro n
  exact le_iSup_of_le (of_nat n)
    (le_inf of_nat_mem_omega (graph_pair_of_weight M Y Hdisj n a))

theorem graph_is_surjective_function (M : ℕ → α → β) (Y : α → bSet β)
    (Hdisj : ∀ n a b, a ≠ b → M n a ⊓ M n b = ⊥)
    (Hrow : ∀ n, (⨆ a, M n a) = ⊤)
    (Hcol : ∀ a, (⨆ n, M n a) = ⊤) :
    (⊤ : β) ≤ is_function omega (check'' Y) (graph M Y) ⊓
      is_surj omega (check'' Y) (graph M Y) :=
  le_inf (graph_is_function M Y Hdisj Hrow) (graph_is_surj M Y Hdisj Hcol)

end bSet.ErdosCountableMatrix
