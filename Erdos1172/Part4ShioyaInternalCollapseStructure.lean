/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseTreeDensity

@[expose] public section

/-! # Order, separativity, and short infima of the mixed countable collapse -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosPartialInjection ErdosOmegaTwo ErdosInjectionExtension ErdosCountableSuccessor
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem collapse_union {Γ : B} {H X U : N} (sub : Γ ≤ U ⊆ᴮ countableCollapse H X)
    (count : Γ ≤ injects_into U omega) (chain : Γ ≤ ErdosInjectionChain.inclusionChain U) :
    Γ ≤ bv_union U ∈ᴮ countableCollapse H X := by
  have members {d : B} (hd : d ≤ Γ) {g : N} (hg : d ≤ g ∈ᴮ U) :=
    countableCollapse_mem.mp (mem_of_mem_subset (hd.trans sub) hg)
  exact countableCollapse_mem.mpr ⟨ErdosInjectionChain.subset_prod_union
    (le_iInf fun _ => projection_imp.mpr fun _ hd hg => (members hd hg).1),
    ErdosInjectionChain.is_func_union_of_chain chain
      (le_iInf fun _ => projection_imp.mpr fun _ hd hg => (members hd hg).2.1),
    ErdosCountableFamilyUnion.union_countable count
      (le_iInf fun _ => projection_imp.mpr fun _ hd hg => (members hd hg).2.2)⟩

private theorem negate {d a b : B} (h : d ≤ aᶜ) (f : ∀ e ≤ d, e ≤ b → e ≤ a) : d ≤ bᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  exact disjoint_iff_inf_le.mpr ((le_inf (f _ inf_le_left inf_le_right) (inf_le_left.trans h)).trans (by simp))

theorem collapse_insert {Γ : B} {H X p i v : N} (hp : Γ ≤ p ∈ᴮ countableCollapse H X)
    (hi : Γ ≤ i ∈ᴮ H) (hv : Γ ≤ v ∈ᴮ X) (fresh : Γ ≤ (i ∈ᴮ graphDomain H X p)ᶜ) :
    Γ ≤ bSet.insert1 (pair i v) p ∈ᴮ countableCollapse H X := by
  obtain ⟨sub,func,count⟩ := countableCollapse_mem.mp hp
  exact countableCollapse_mem.mpr ⟨ErdosRelationChoice.insert_subset_of_mem sub (mem_prod hi hv),
    is_func_insertPair (function_on_graphDomain sub func) fresh,
    insert_countable_of_fresh count (negate fresh fun _ hd h => mem_graphDomain_of_pair (hd.trans sub) h)⟩

end bSet.ErdosShioyaInternal.CollapsePath
