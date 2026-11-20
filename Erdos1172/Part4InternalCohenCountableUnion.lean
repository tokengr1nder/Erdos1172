/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenExtension
public import Erdos1172.Part4InternalCountableFamilyUnion
public import Erdos1172.Part4InternalInjectionChain

@[expose] public section

/-!
# Countable chain unions of internal Cohen conditions

The domains form the actual bounded image of a supported internal function.
Its union is countable, and it contains the domain of the union graph.
The inclusion-chain hypothesis gives functionality of that graph. These
facts prove closure for arbitrary internally countable families of mixed
names, at the original Boolean condition, including the empty family.

No CH, ideal, external enumeration, or supplied union-smallness assumption
is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection ErdosRelationGraph

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The actual internal graph sending each member of C to its domain.
It is defined even when C contains arbitrary malformed graph names. -/
def domainMap (K C : bSet 𝔹) : bSet 𝔹 :=
  relationGraph C (bv_powerset K) (fun p D => graphDomain K two p =ᴮ D)

private theorem domain_eq_ext (K D : bSet 𝔹) :
    B_ext (fun p => graphDomain K two p =ᴮ D) :=
  B_ext_term (fun A => A =ᴮ D) (graphDomain K two)
    B_ext_bv_eq_left (graphDomain_congr_graph K two)

theorem mem_domainMap_iff {K C p D : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair p D ∈ᴮ domainMap K C ↔
      Γ ≤ p ∈ᴮ C ∧ Γ ≤ D ∈ᴮ bv_powerset K ∧
        Γ ≤ graphDomain K two p =ᴮ D :=
  mem_relationGraph_iff (fun D => domain_eq_ext K D)
    (fun _ => B_ext_bv_eq_right)

theorem domainMap_is_function {K C : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function C (bv_powerset K) (domainMap K C) := by
  apply relationGraph_is_function
    (P := fun p D => graphDomain K two p =ᴮ D)
    (fun D => domain_eq_ext K D) (fun _ => B_ext_bv_eq_right)
  · apply le_iInf
    intro p
    rw [← deduction]
    exact le_iSup_of_le (graphDomain K two p)
      (le_inf (mem_powerset_iff.mpr graphDomain_subset) bv_refl)
  · intro p₁ p₂ D₁ D₂ Δ _ _ _ _ _ H₁ H₂ Heq
    exact bv_trans (bv_symm H₁)
      (bv_trans (graphDomain_congr_graph K two Heq) H₂)

/-- The values of the domain map are countable when its inputs really are
conditions on an internal first uncountable ordinal. -/
theorem domainMap_countableValues {K C : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (HC : Γ ≤ C ⊆ᴮ conditions K) :
    Γ ≤ ErdosCountableFamilyUnion.countableValues C (domainMap K C) := by
  apply le_iInf
  intro p
  apply le_iInf
  intro D
  rw [← deduction]
  have Hp : Γ ⊓ (p ∈ᴮ C ⊓ pair p D ∈ᴮ domainMap K C) ≤ condition K p :=
    mem_conditions_iff.mp
      (mem_of_mem_subset (inf_le_left.trans HC) (inf_le_right.trans inf_le_left))
  have Hmap := mem_domainMap_iff.mp
    (show Γ ⊓ (p ∈ᴮ C ⊓ pair p D ∈ᴮ domainMap K C) ≤
      pair p D ∈ᴮ domainMap K C from inf_le_right.trans inf_le_right)
  exact bv_rw'' Hmap.2.2
    (countable_of_smallDomain (inf_le_left.trans HK)
      (Hp.trans (inf_le_right.trans inf_le_right))) B_ext_injects_into_left

/-- Every point of the union graph's bounded domain belongs to an actual
domain value in the image. This requires neither chain nor validity. -/
theorem graphDomain_union_subset_union_domainMap {K C : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ graphDomain K two (bv_union C) ⊆ᴮ
      bv_union (image C (bv_powerset K) (domainMap K C)) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ graphDomain K two (bv_union C)
  have Hdom : Δ ≤ x ∈ᴮ K ⊓ ⨆ y, y ∈ᴮ two ⊓ pair x y ∈ᴮ bv_union C :=
    inf_le_right.trans (mem_graphDomain K two (bv_union C) x).le
  obtain ⟨y, Hy⟩ := exists_convert (Hdom.trans inf_le_right)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  obtain ⟨p, Hp⟩ := exists_convert
    ((bv_union_spec_split C (pair x y)).mp (Hy.trans inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hxp : Δ ≤ x ∈ᴮ graphDomain K two p := by
    rw [mem_graphDomain]
    exact le_inf (Hdom.trans inf_le_left)
      (le_iSup_of_le y (le_inf (Hy.trans inf_le_left) (Hp.trans inf_le_right)))
  have HD : Δ ≤ graphDomain K two p ∈ᴮ bv_powerset K :=
    mem_powerset_iff.mpr graphDomain_subset
  have Hmap : Δ ≤ pair p (graphDomain K two p) ∈ᴮ domainMap K C :=
    mem_domainMap_iff.mpr ⟨Hp.trans inf_le_left, HD, bv_refl⟩
  have Himage : Δ ≤ graphDomain K two p ∈ᴮ
      image C (bv_powerset K) (domainMap K C) :=
    mem_image Hmap (Hp.trans inf_le_left) HD
  exact (bv_union_spec_split _ x).mpr
    (le_iSup_of_le (graphDomain K two p) (le_inf Himage Hxp))

/-- Countability of the union graph's actual domain is derived from the
countable internal family, not from any external presentation of it. -/
theorem graphDomain_union_countable {K C : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (HC : Γ ≤ C ⊆ᴮ conditions K)
    (Hcount : Γ ≤ injects_into C omega) :
    Γ ≤ injects_into (graphDomain K two (bv_union C)) omega :=
  injects_into_trans
    (injects_into_of_subset graphDomain_union_subset_union_domainMap)
    (ErdosCountableFamilyUnion.indexed_union_countable
      (is_func'_of_is_function domainMap_is_function) Hcount
      (domainMap_countableValues HK HC))

/-- The union of an internally countable inclusion chain of internal
Cohen conditions is an internal Cohen condition at the same Γ. -/
theorem condition_union_of_countable_chain {K C : bSet 𝔹} {Γ : 𝔹}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (HC : Γ ≤ C ⊆ᴮ conditions K)
    (Hchain : Γ ≤ ErdosInjectionChain.inclusionChain C)
    (Hcount : Γ ≤ injects_into C omega) :
    Γ ≤ condition K (bv_union C) := by
  have Hsupport : Γ ≤ ⨅ p, _root_.imp (p ∈ᴮ C) (p ⊆ᴮ prod K two) := by
    apply le_iInf
    intro p
    rw [← deduction]
    exact (mem_conditions_iff.mp
      (mem_of_mem_subset (inf_le_left.trans HC) inf_le_right)).trans inf_le_left
  have Hfunc : Γ ≤ ⨅ p, _root_.imp (p ∈ᴮ C) (is_func p) := by
    apply le_iInf
    intro p
    rw [← deduction]
    exact (mem_conditions_iff.mp
      (mem_of_mem_subset (inf_le_left.trans HC) inf_le_right)).trans
        (inf_le_right.trans inf_le_left)
  exact le_inf (ErdosInjectionChain.subset_prod_union Hsupport)
    (le_inf (ErdosInjectionChain.is_func_union_of_chain Hchain Hfunc)
      (smallDomain_of_countable (omega_mem_of_hartogsProperty HK)
        (graphDomain_union_countable HK HC Hcount)))

end bSet.ErdosCohen
