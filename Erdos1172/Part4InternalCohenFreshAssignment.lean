/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenExtension
public import Erdos1172.Part4InternalFusionActiveHistory

@[expose] public section

/-!
# Adjoining an internally countable fresh assignment to a Cohen condition

The new assignment is an actual supported function on an arbitrary
internally countable domain, not an externally enumerated family. Disjoint
domains make the binary graph union functional. Its actual domain is
contained in the union of the old domain and the assignment domain, which
is internally countable by the proved finite-union theorem.

Every statement is local to the same Boolean condition. The checked-set
specialization turns freshness of all ground children into freshness for
all mixed members; it assumes neither an externally countable index set
nor a coherent external enumeration.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection ErdosIdeal ErdosSmallPoolOperations

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

private theorem bot_of_old_new_pairs {K A p g i j x y : bSet B} {Γ : B}
    (Hp : Γ ≤ condition K p) (Hg : Γ ≤ is_function A two g)
    (Hfresh : Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (a ∈ᴮ graphDomain K two p)ᶜ)
    (Hix : Γ ≤ pair i x ∈ᴮ p) (Hjy : Γ ≤ pair j y ∈ᴮ g)
    (Hij : Γ ≤ i =ᴮ j) : Γ ≤ ⊥ := by
  have Hi : Γ ≤ i ∈ᴮ graphDomain K two p := mem_graphDomain_of_pair (Hp.trans inf_le_left) Hix
  have Hj : Γ ≤ j ∈ᴮ A := mem_domain_of_is_function Hjy Hg
  have Hnot : Γ ≤ (j ∈ᴮ graphDomain K two p)ᶜ :=
    (le_inf (Hfresh.trans (iInf_le _ j)) Hj).trans bv_imp_elim
  exact bv_absurd _ (mem_congr Hij bv_refl Hi) Hnot

/-- A whole fresh-domain function can be adjoined without requiring its
values to be injective or distinct from the old values. -/
theorem is_func_binary_union_of_fresh_function {K A p g : bSet B} {Γ : B}
    (Hp : Γ ≤ condition K p) (Hg : Γ ≤ is_function A two g)
    (Hfresh : Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (a ∈ᴮ graphDomain K two p)ᶜ) :
    Γ ≤ is_func (binary_union p g) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction, ← deduction]
  let Δ : B := (Γ ⊓ (pair i x ∈ᴮ binary_union p g ⊓ pair j y ∈ᴮ binary_union p g)) ⊓ (i =ᴮ j)
  change Δ ≤ x =ᴮ y
  have Hbase : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have HpΔ := Hbase.trans Hp
  have HgΔ := Hbase.trans Hg
  have HfreshΔ := Hbase.trans Hfresh
  have Hij : Δ ≤ i =ᴮ j := inf_le_right
  have Hleft : Δ ≤ pair i x ∈ᴮ p ⊔ pair i x ∈ᴮ g :=
    (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans (mem_binary_union p g (pair i x)).le
  have Hright : Δ ≤ pair j y ∈ᴮ p ⊔ pair j y ∈ᴮ g :=
    (inf_le_left.trans (inf_le_right.trans inf_le_right)).trans (mem_binary_union p g (pair j y)).le
  apply (le_inf le_rfl Hleft).trans
  rw [inf_sup_left]
  apply sup_le
  · apply (le_inf le_rfl (inf_le_left.trans Hright)).trans
    rw [inf_sup_left]
    apply sup_le
    · exact eq_of_is_func_of_eq
        ((inf_le_left.trans inf_le_left).trans (HpΔ.trans (inf_le_right.trans inf_le_left)))
        ((inf_le_left.trans inf_le_left).trans Hij)
        (inf_le_left.trans inf_le_right) inf_le_right
    · exact (bot_of_old_new_pairs
        ((inf_le_left.trans inf_le_left).trans HpΔ)
        ((inf_le_left.trans inf_le_left).trans HgΔ)
        ((inf_le_left.trans inf_le_left).trans HfreshΔ)
        (inf_le_left.trans inf_le_right) inf_le_right
        ((inf_le_left.trans inf_le_left).trans Hij)).trans bot_le
  · apply (le_inf le_rfl (inf_le_left.trans Hright)).trans
    rw [inf_sup_left]
    apply sup_le
    · exact (bot_of_old_new_pairs
        ((inf_le_left.trans inf_le_left).trans HpΔ)
        ((inf_le_left.trans inf_le_left).trans HgΔ)
        ((inf_le_left.trans inf_le_left).trans HfreshΔ)
        inf_le_right (inf_le_left.trans inf_le_right)
        (bv_symm ((inf_le_left.trans inf_le_left).trans Hij))).trans bot_le
    · exact eq_of_is_func_of_eq
        ((inf_le_left.trans inf_le_left).trans (HgΔ.trans (inf_le_left.trans inf_le_left)))
        ((inf_le_left.trans inf_le_left).trans Hij)
        (inf_le_left.trans inf_le_right) inf_le_right

/-- The actual union graph has no domain points outside the old domain
and the supported new assignment domain. No disjointness is needed here. -/
theorem graphDomain_binary_union_subset {K A p g : bSet B} {Γ : B}
    (Hg : Γ ≤ is_function A two g) :
    Γ ≤ graphDomain K two (binary_union p g) ⊆ᴮ binary_union (graphDomain K two p) A := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ : B := Γ ⊓ x ∈ᴮ graphDomain K two (binary_union p g)
  have Hmem : Δ ≤ x ∈ᴮ K ⊓ ⨆ y, y ∈ᴮ two ⊓ pair x y ∈ᴮ binary_union p g :=
    inf_le_right.trans (mem_graphDomain K two (binary_union p g) x).le
  obtain ⟨y, Hy⟩ := exists_convert (Hmem.trans inf_le_right)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hpair : Δ ≤ pair x y ∈ᴮ p ⊔ pair x y ∈ᴮ g :=
    (Hy.trans inf_le_right).trans (mem_binary_union p g (pair x y)).le
  apply (le_inf le_rfl Hpair).trans
  rw [inf_sup_left]
  apply sup_le
  · rw [mem_binary_union]
    apply le_sup_of_le_left
    apply le_trans ?_ (mem_graphDomain K two p x).ge
    exact le_inf (inf_le_left.trans (Hmem.trans inf_le_left))
      (le_iSup_of_le y (le_inf (inf_le_left.trans (Hy.trans inf_le_left)) inf_le_right))
  · rw [mem_binary_union]
    apply le_sup_of_le_right
    exact mem_domain_of_is_function inf_le_right ((inf_le_left.trans inf_le_left).trans Hg)

/-- The union itself is a valid condition. Its small domain is proved by
an actual injection of the union of two internally countable domains. -/
theorem condition_binary_union_of_fresh_function {K A p g : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (Hg : Γ ≤ is_function A two g)
    (HA : Γ ≤ A ⊆ᴮ K) (Hcount : Γ ≤ injects_into A omega)
    (Hfresh : Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (a ∈ᴮ graphDomain K two p)ᶜ) :
    Γ ≤ condition K (binary_union p g) := by
  have Hsupport : Γ ≤ binary_union p g ⊆ᴮ prod K two :=
    binary_union_subset (Hp.trans inf_le_left)
      (subset_trans' (subset_prod_of_is_function Hg) (prod_domain_mono HA))
  have Hold : Γ ≤ injects_into (graphDomain K two p) omega :=
    countable_of_smallDomain HK (Hp.trans (inf_le_right.trans inf_le_right))
  have Hdomain : Γ ≤ injects_into (graphDomain K two (binary_union p g)) omega :=
    injects_into_trans (injects_into_of_subset (graphDomain_binary_union_subset Hg))
      (ErdosFusionActiveHistory.binary_union_countable Hold Hcount)
  exact le_inf Hsupport (le_inf (is_func_binary_union_of_fresh_function Hp Hg Hfresh)
    (smallDomain_of_countable (omega_mem_of_hartogsProperty HK) Hdomain))

/-- The same concrete union retains the entire old graph and the entire
new supported assignment at the original Boolean condition. -/
theorem fresh_assignment_extension {K A p g : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (Hg : Γ ≤ is_function A two g)
    (HA : Γ ≤ A ⊆ᴮ K) (Hcount : Γ ≤ injects_into A omega)
    (Hfresh : Γ ≤ ⨅ a, _root_.imp (a ∈ᴮ A) (a ∈ᴮ graphDomain K two p)ᶜ) :
    Γ ≤ condition K (binary_union p g) ⊓ (p ⊆ᴮ binary_union p g ⊓ g ⊆ᴮ binary_union p g) :=
  le_inf (condition_binary_union_of_fresh_function HK Hp Hg HA Hcount Hfresh)
    (le_inf subset_binary_union_left subset_binary_union_right)

/-- Canonical checked-child freshness suffices for the whole internally
countable checked domain, including all its arbitrary mixed members. -/
theorem fresh_checked_assignment_extension (C : PSet.{u})
    {K p g : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (Hg : Γ ≤ is_function (check C) two g)
    (HC : Γ ≤ check C ⊆ᴮ K) (Hcount : Γ ≤ injects_into (check C) omega)
    (Hfresh : ∀ i : C.Type, Γ ≤ (check (C.Func i) ∈ᴮ graphDomain K two p)ᶜ) :
    Γ ≤ condition K (binary_union p g) ⊓ (p ⊆ᴮ binary_union p g ⊓ g ⊆ᴮ binary_union p g) := by
  apply fresh_assignment_extension HK Hp Hg HC Hcount
  rw [← bounded_forall (v := check C)
    (ϕ := fun a : bSet B => (a ∈ᴮ graphDomain K two p)ᶜ)
    (h_congr := B_ext_neg (h := B_ext_mem_left))]
  apply le_iInf
  intro i
  rw [check_bval_top, top_imp, check_func]
  exact Hfresh (check_cast i)

end bSet.ErdosCohen
