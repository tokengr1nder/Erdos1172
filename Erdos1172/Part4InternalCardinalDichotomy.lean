/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartialInjectionMaximal
public import Erdos1172.Part4InternalPartialInjectionDomain
public import Erdos1172.Part4InternalInjectionExtension

@[expose] public section

/-!
Cardinal comparison by an actual internal maximal partial injection. No
ground-model enumeration, checked-cardinal preservation, CH, or ideal is
assumed. The omega-two specialization concerns its concrete Hartogs name.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartialInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- If a maximal initial-segment injection has a proper domain, its range
must cover the entire codomain: otherwise adjoining one fresh pair extends it. -/
theorem maximal_range_covers_of_domain_mem {κ S f : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hf : Γ ≤ partialGraph κ S f)
    (Hmax : Γ ≤ ⨅ g, _root_.imp (partialGraph κ S g)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)))
    (Hproper : Γ ≤ graphDomain κ S f ∈ᴮ κ) :
    Γ ≤ S ⊆ᴮ image (graphDomain κ S f) S f := by
  let A := graphDomain κ S f
  have HA : Γ ≤ Ord A := partialGraph_domain_Ord Hκ Hf
  have Hfunc : Γ ≤ is_injective_function A S f := partialGraph_function Hf
  rw [subset_unfold']
  apply le_iInf
  intro y
  rw [← deduction]
  rw [← compl_compl (y ∈ᴮ image A S f), ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ y ∈ᴮ S) ⊓ (y ∈ᴮ image A S f)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hnotself : Δ ≤ (A ∈ᴮ A)ᶜ := by
    rw [← imp_bot, ← deduction]
    exact bot_of_mem_self' inf_le_right
  have Hextend : Δ ≤ is_injective_function (succ A) S
      (bSet.insert1 (pair A y) f) :=
    ErdosInjectionExtension.is_injective_function_insertPair (HΔ.trans Hfunc)
      Hnotself (inf_le_left.trans inf_le_right) inf_le_right
  have Hnew : Δ ≤ partialGraph κ S (bSet.insert1 (pair A y) f) :=
    partialGraph_of_ordinal_function (Ord_succ (HΔ.trans HA))
      (Ord.succ_le_of_lt (HΔ.trans Hκ) (HΔ.trans Hproper)) Hextend
  have Heq : Δ ≤ f =ᴮ bSet.insert1 (pair A y) f :=
    (le_inf ((le_inf
      (HΔ.trans (Hmax.trans (iInf_le _ (bSet.insert1 (pair A y) f))))
      Hnew).trans bv_imp_elim) ErdosInjectionExtension.subset_insertPair).trans
      bv_imp_elim
  have Hpair : Δ ≤ pair A y ∈ᴮ f :=
    mem_congr bv_refl (bv_symm Heq) ErdosInjectionExtension.pair_mem_insertPair
  exact bot_of_mem_self'
    (mem_domain_of_is_function Hpair (HΔ.trans (Hfunc.trans inf_le_left)))

theorem injection_back_of_range_covers {A S f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function A S f)
    (Hcover : Γ ≤ S ⊆ᴮ image A S f) : Γ ≤ injects_into S A := by
  have Hinv : Γ ≤ injection_into (image A S f) A :=
    le_iSup_of_le (injective_function_inverse Hf)
      (injective_function_inverse_is_injective_function (H_inj := Hf))
  exact injects_into_trans (injects_into_of_subset Hcover)
    (injects_into_of_injection_into Hinv)

/-- Every internal set either contains an injection of the prescribed
ordinal or injects into one of its strict predecessors. -/
theorem ordinal_cardinal_dichotomy {κ S : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) :
    Γ ≤ injects_into κ S ⊔ ⨆ A, (A ∈ᴮ κ) ⊓ injects_into S A := by
  have Hmax := exists_maximal_partialGraph (κ := κ) (S := S) (Γ := Γ)
  apply (le_inf (le_refl Γ) Hmax).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  let Δ := Γ ⊓ (partialGraph κ S f ⊓
    ⨅ g, _root_.imp (partialGraph κ S g) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)))
  have Hf : Δ ≤ partialGraph κ S f := inf_le_right.trans inf_le_left
  have Hmaxf : Δ ≤ ⨅ g, _root_.imp (partialGraph κ S g)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)) := inf_le_right.trans inf_le_right
  let A := graphDomain κ S f
  have HA : Δ ≤ Ord A := partialGraph_domain_Ord (inf_le_left.trans Hκ) Hf
  have Hfunc : Δ ≤ is_injective_function A S f := partialGraph_function Hf
  have Hcase : Δ ≤ A =ᴮ κ ⊔ A ∈ᴮ κ :=
    ErdosInitialSegments.eq_or_mem_of_ordinal_subset HA (inf_le_left.trans Hκ)
      graphDomain_subset
  apply (le_inf (le_refl Δ) Hcase).trans
  rw [inf_sup_left]
  apply sup_le
  · apply le_sup_of_le_left
    have Hinj : Δ ⊓ A =ᴮ κ ≤ injects_into A S :=
      injects_into_of_injection_into
        (le_iSup_of_le f (inf_le_left.trans Hfunc))
    exact bv_rw'' (ϕ := fun X => injects_into X S) inf_le_right Hinj
      B_ext_injects_into_left
  · apply le_sup_of_le_right
    apply le_iSup_of_le A
    refine le_inf inf_le_right ?_
    exact injection_back_of_range_covers (inf_le_left.trans Hfunc)
      (maximal_range_covers_of_domain_mem
        (inf_le_left.trans (inf_le_left.trans Hκ))
        (inf_le_left.trans Hf) (inf_le_left.trans Hmaxf) inf_le_right)

/-- The first Hartogs name gives the countable versus omega-one alternative. -/
theorem omegaOne_cardinal_dichotomy {S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ injects_into S bSet.omega ⊔ injects_into ErdosOmegaTwo.omegaOne S := by
  apply (ordinal_cardinal_dichotomy (S := S)
    (ErdosOmegaTwo.omegaOne_Ord (Γ := Γ))).trans
  apply sup_le
  · exact le_sup_right
  · apply iSup_le
    intro A
    apply le_sup_of_le_left
    exact injects_into_trans inf_le_right
      (ErdosOmegaTwo.omegaOne_member_injects inf_le_left)

/-- The actual Hartogs omega-two name compares with every internal set:
the set is at most omega-one sized, or contains a full omega-two injection. -/
theorem omegaTwo_cardinal_dichotomy {S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ injects_into S ErdosOmegaTwo.omegaOne ⊔
      injects_into ErdosOmegaTwo.omegaTwo S := by
  apply (ordinal_cardinal_dichotomy (S := S)
    (ErdosOmegaTwo.omegaTwo_Ord (Γ := Γ))).trans
  apply sup_le
  · exact le_sup_right
  · apply iSup_le
    intro A
    apply le_sup_of_le_left
    exact injects_into_trans inf_le_right
      (ErdosOmegaTwo.omegaTwo_member_injects inf_le_left)

end bSet.ErdosPartialInjection
