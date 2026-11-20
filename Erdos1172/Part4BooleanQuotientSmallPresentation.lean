/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientDenseSets
public import Erdos1172.Part4BooleanQuotientFactorization
public import Erdos1172.Part4ResidualNameDensity
public import Erdos1172.Part4GroundIndexNameBound

@[expose] public section

/-! # A small dense presentation of a named Boolean quotient over its source -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open bSet Lattice Erdos1172BooleanFactor Erdos1172PositiveBoolean Erdos1172BooleanNameIteration
open Erdos1172PosetCompletion Erdos1172Shioya.ForcingCover
namespace Erdos1172BooleanQuotient.SmallPresentation
variable {A C K : Type u} [NontrivialCompleteBooleanAlgebra A] [NontrivialCompleteBooleanAlgebra C]
variable (e : CompleteLatticeHom A C) (d : K → Positive C)

/-- A label from the chosen dense family is present precisely where its
Boolean value projects to the first-stage generic. -/
def labels : bSet A := .mk K (fun k => check (upperSetCode (d k))) (fun k => lowerProjection e (d k).val)

theorem subset : (⊤ : A) ≤ labels e d ⊆ᴮ quotientName e := by
  rw [subset_unfold]
  apply le_iInf
  intro k
  rw [← deduction]
  exact inf_le_right.trans (mem_mk' (quotientName e) (d k))

variable (dense : ∀ c : Positive C, ∃ k, d k ≤ c)
include dense in
private theorem lower_cover (p : Positive C) :
    lowerProjection e p.val ≤ ⨆ k : {k : K // d k ≤ p}, lowerProjection e (d k.val).val := by
  let rhs := ⨆ k : {k : K // d k ≤ p}, lowerProjection e (d k.val).val
  apply lowerProjection_le
  by_contra bad
  have pos : p.val ⊓ (e rhs)ᶜ ≠ ⊥ := fun eq => bad (disjoint_compl_right_iff.mp (disjoint_iff.mpr eq))
  obtain ⟨k,hk⟩ := dense ⟨_,pos⟩
  have hk' : (d k).val ≤ p.val ⊓ (e rhs)ᶜ := hk
  have le : lowerProjection e (d k).val ≤ rhs := le_iSup (fun t : {i : K // d i ≤ p} =>
    lowerProjection e (d t.val).val) ⟨k,hk'.trans inf_le_left⟩
  exact (d k).property (bot_unique ((le_inf ((lowerProjection_le_iff e).mp le)
    (hk'.trans inf_le_right)).trans inf_compl_eq_bot.le))

include dense in
theorem internal_dense : (⊤ : A) ≤ denseValue (quotientName e) (fun y => y ∈ᴮ labels e d) := by
  apply (denseValue_iff e _ B_ext_mem_left _).mpr
  intro p
  apply (inf_le_right.trans (lower_cover e d dense p)).trans
  apply iSup_le
  intro k
  exact le_iSup_of_le (⟨d k.val,k.property⟩ : {q : Positive C // q ≤ p})
    (le_inf le_rfl (mem_mk' (labels e d) k.val))

include dense in
theorem exists_enumeration (inj : Function.Injective e) (κ : Cardinal.{u}) (small : Cardinal.mk K ≤ κ) :
    ∃ f : bSet A, (⊤ : A) ≤ is_function (check (PSet.ordinalMk κ.ord)) (labels e d) f ⊓
      is_surj (check (PSet.ordinalMk κ.ord)) (labels e d) f := by
  let Q := labels e d
  have nonempty : (⊤ : A) ≤ ⨆ y : bSet A, y ∈ᴮ Q := by
    apply (lowerProjection_top e inj).ge.trans ((lower_cover e d dense (topLabel C)).trans ?_)
    exact iSup_le fun k => le_iSup_of_le (Q.func k.val) (mem_mk' Q k.val)
  have onto := surjects_onto_of_injects_into'
    (ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le κ Q small) nonempty
  apply exists_convert (exists_surjection_of_surjects_onto onto)
  apply B_ext_inf B_ext_is_function_right
  unfold is_surj
  exact B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))

def embed : Condition (labels e d) →o Condition (quotientName e) where
  toFun p := ⟨p.value,p.nonzero,d p.index,p.valid⟩
  monotone' _ _ h := h

theorem embed_reflect (p q : Condition (labels e d)) (le : embed e d p ≤ embed e d q) : p ≤ q := le

include dense in
theorem embed_dense (p : Condition (quotientName e)) : ∃ q, embed e d q ≤ p := by
  obtain ⟨k,hk⟩ := dense (iterationEvaluation e p)
  have le : (d k).val ≤ e p.value ⊓ (show Positive C from p.index).val := hk
  let q : Condition (labels e d) := ⟨lowerProjection e (d k).val,lowerProjection_ne_bot e (d k).property,k,le_rfl⟩
  exact ⟨q,(iteration_le_iff e _ _).mpr ⟨lowerProjection_le e (le.trans inf_le_left),le.trans inf_le_right⟩⟩

include dense in
theorem embed_lifts : Lifts (embed e d) := by
  intro p t ht
  obtain ⟨q,hq⟩ := embed_dense e d dense t
  exact ⟨q,embed_reflect e d _ _ (hq.trans ht),hq⟩

/-- Removing all nonselected quotient labels preserves its completion. -/
def completion : C ≃o Algebra (labels e d) :=
  (factorization e).trans (completionIso (embed e d) (embed_lifts e d dense)
    (fun p q h => ⟨p,le_rfl,embed_reflect e d p q h⟩) (embed_dense e d dense))

theorem completion_over_source (a : A) : completion e d dense (e a) = sourceHom (labels e d) a := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  change embed e d p ∈ (factorization e (e a)).val ↔ p.value ≤ a
  rw [factorization_image]
  rfl

end Erdos1172BooleanQuotient.SmallPresentation
