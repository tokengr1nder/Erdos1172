/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousFullGCH
public import Erdos1172.Part4ShioyaInternalProjectedWord
public import Erdos1172.Part4ShioyaInternalOrderMatrix

@[expose] public section

/-! # Single ordinal enumerations of small internally named forcing orders -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosPartialInjection Erdos1172LevyCohen Erdos1172CompleteSubalgebra ErdosRelationGraph

/-- A maximal initial-segment injection into P stops on the original guard
when H cannot embed in P. Its graph is then a bijection onto P. -/
theorem exists_ordinal_bijection {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {Γ : B} {H P : bSet B} (order : Γ ≤ Ord H) (small : Γ ≤ (injects_into H P)ᶜ) :
    ∃ A f : bSet B, Γ ≤ A ∈ᴮ H ∧ Γ ≤ is_injective_function A P f ∧ Γ ≤ is_surj A P f := by
  obtain ⟨f,hf⟩ := exists_convert (exists_maximal_partialMap (κ := H) (S := P) (Γ := Γ))
    (B_ext_inf B_ext_mem_left (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_imp (h₁ := B_ext_subset_left) (h₂ := B_ext_bv_eq_left)))))
  let A := graphDomain H P f
  have part := mem_partialMaps_iff.mp (hf.trans inf_le_left)
  have inj : Γ ≤ is_injective_function A P f := partialGraph_function part
  have alt := ErdosInitialSegments.eq_or_mem_of_ordinal_subset (partialGraph_domain_Ord order part) order graphDomain_subset
  have proper : Γ ≤ A ∈ᴮ H := by
    apply (le_inf le_rfl alt).trans
    rw [inf_sup_left]
    apply sup_le _ inf_le_right
    apply le_trans _ bot_le
    apply bv_absurd _ _ (inf_le_left.trans small)
    apply bv_rw'' (ϕ := fun x => injects_into x P) inf_le_right _ B_ext_injects_into_left
    exact injects_into_of_injection_into (le_iSup_of_le f (inf_le_left.trans inj))
  have maximal : Γ ≤ ⨅ g : bSet B, partialGraph H P g ⟹ ((f ⊆ᴮ g) ⟹ (f =ᴮ g)) := by
    apply le_iInf
    intro g
    rw [← deduction]
    exact (le_inf (inf_le_left.trans ((hf.trans inf_le_right).trans (iInf_le _ g)))
      (mem_partialMaps_iff.mpr inf_le_right)).trans bv_imp_elim
  have covers := maximal_range_covers_of_domain_mem order part maximal proper
  refine ⟨A,f,proper,inj,le_iInf fun y => ?_⟩
  rw [← deduction]
  exact (mem_image_iff.mp (mem_of_mem_subset (inf_le_left.trans covers) inf_le_right)).2

variable {κ θ : Cardinal.{u}}
local notation "A" => anonymousAlgebra κ

/-- Any family internally injecting into a ground cardinal below θ has
one ordinal enumeration below θ in the anonymous extension. -/
theorem anonymous_ordinal_bijection_of_bound (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    {μ : Cardinal.{u}} (hkμ : κ ≤ μ) (hμ : μ < θ) {Γ : A} {P : bSet (A)}
    (bound : Γ ≤ injects_into P (check (PSet.ordinalMk μ.ord))) :
    ∃ I f : bSet (A), Γ ≤ I ∈ᴮ check (PSet.ordinalMk θ.ord) ∧
      Γ ≤ is_injective_function I P f ∧ Γ ≤ is_surj I P f := by
  let H := (check (PSet.ordinalMk (Order.succ μ).ord) : bSet (A))
  have small : Γ ≤ (injects_into H P)ᶜ := by
    rw [← imp_bot,← deduction]
    exact (injects_into_trans inf_le_right (inf_le_left.trans bound)).trans_eq
      (anonymous_checked_successor_injects_base_eq_bot κ hκ μ hkμ)
  obtain ⟨I,f,hi,hf,hs⟩ := exists_ordinal_bijection (check_Ord (PSet.Ord_mk _)) small
  have member : Γ ≤ H ∈ᴮ check (PSet.ordinalMk θ.ord) :=
    check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr (hθ.isSuccLimit.succ_lt hμ)))
  exact ⟨I,f,mem_of_mem_subset (subset_of_mem_transitive ((check_Ord (PSet.Ord_mk θ.ord) : Γ ≤ _).trans inf_le_right)
    member) hi,hf,hs⟩

/-- Every internally selected family of subsets of a small name admits an
actual mixed ordinal carrier and one bijective graph on the given guard. -/
theorem anonymous_powerset_family_ordinal_bijection (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hk : κ < θ) {Γ : A} {P X : bSet (A)} (sub : Γ ≤ P ⊆ᴮ bv_powerset X)
    (size : Cardinal.mk X.type < θ) :
    ∃ I f : bSet (A), Γ ≤ I ∈ᴮ check (PSet.ordinalMk θ.ord) ∧
      Γ ≤ is_injective_function I P f ∧ Γ ≤ is_surj I P f := by
  have alg : Cardinal.mk (A) < θ :=
    (Cardinal.mk_le_of_injective (inclusion_injective (anonymousAlgebra κ))).trans_lt
      ((completion_cardinal_le_two_power κ hκ).trans_lt (hθ.isStrongPrelimit hk))
  let graph (b : X.type → A) : Set (X.type × A) := {t | b t.1 = t.2}
  have inj : Function.Injective graph := by
    intro b c eq
    exact _root_.funext fun i => (eq ▸ (show (i,b i) ∈ graph b from rfl) : (i,b i) ∈ graph c).symm
  have names : Cardinal.mk (X.type → A) < θ := by
    apply (Cardinal.mk_le_of_injective inj).trans_lt
    rw [Cardinal.mk_set,Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
    exact hθ.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le size alg)
  let μ := max κ (Cardinal.mk (X.type → A))
  apply anonymous_ordinal_bijection_of_bound hκ hθ (le_max_left _ _) (max_lt hk names)
  exact injects_into_trans (injects_into_of_subset sub) (le_top.trans
    (ErdosGroundIndexNameBound.powerset_injects_checked_cardinal_of_index_cardinal_le μ X (le_max_right _ _)))

/-- Countable partial assignments from H to X, represented by their graphs. -/
def countableCollapse {B : Type u} [NontrivialCompleteBooleanAlgebra B] (H X : bSet B) : bSet B :=
  comprehend (fun g => is_func g ⊓ injects_into g omega) (bv_powerset (prod H X))

theorem countableCollapse_mem {B : Type u} [NontrivialCompleteBooleanAlgebra B] {Γ : B} {g H X : bSet B} :
    Γ ≤ g ∈ᴮ countableCollapse H X ↔ Γ ≤ g ⊆ᴮ prod H X ∧ Γ ≤ is_func g ∧ Γ ≤ injects_into g omega := by
  rw [countableCollapse,mem_comprehend_and (B_ext_inf ErdosPrefixFunction.is_func_ext_graph B_ext_injects_into_left),
    mem_powerset_iff,le_inf_iff]

theorem anonymous_collapse_ordinal_bijection (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hk : κ < θ) {δ : Ordinal.{u}} (hδ : δ < θ.ord) :
    let P := countableCollapse (ordinalCarrier κ.ord) (ordinalCarrier δ)
    ∃ I f : bSet (A), (⊤ : A) ≤ I ∈ᴮ check (PSet.ordinalMk θ.ord) ∧
      (⊤ : A) ≤ is_injective_function I P f ∧ (⊤ : A) ≤ is_surj I P f := by
  intro P
  let X : bSet (A) := prod (ordinalCarrier κ.ord) (ordinalCarrier δ)
  have sub : (⊤ : A) ≤ P ⊆ᴮ bv_powerset X :=
    comprehend_subset (ϕ := fun g => is_func g ⊓ injects_into g omega) (bv_powerset X)
  have size : Cardinal.mk X.type < θ := by
    change Cardinal.mk ((ordinalCarrier κ.ord : bSet (A)).type × (ordinalCarrier δ : bSet (A)).type) < θ
    simp only [Cardinal.mk_prod, Cardinal.lift_id, ordinalCarrier, check_type', PSet.ordinalMk_type,
      Cardinal.mk_toType, Cardinal.card_ord]
    exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hk (Cardinal.lt_ord.mp hδ)
  exact anonymous_powerset_family_ordinal_bijection hκ hθ hk sub size

end bSet.ErdosShioyaInternal
