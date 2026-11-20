/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalProjectionGraph
public import Erdos1172.Part4ShioyaInternalShortInfima
public import Erdos1172.Part4ShioyaInternalOrder

@[expose] public section

/-! # Continuous partial projections and pointed word refinement in the Boolean universe -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

/-- The projected output sequence g agrees with F on all corresponding values
of the input sequence f. The function hypotheses on f, F, and g occur in the
projection and continuity predicates. -/
def projectionSequence (F f g : N) : B :=
  ⨅ i : N, ⨅ x : N, ⨅ y : N, (edge f i x ⊓ edge g i y) ⟹ edge F x y

def projectionClosed (K P R D : N) : B :=
  ⨅ A : N, ⨅ f : N, ⨅ p : N,
    (((A ∈ᴮ K) ⊓ is_function A D f ⊓ descendingValue A f R) ⊓ glbValue A f P R p) ⟹ (p ∈ᴮ D)

/-- Every existing short meet of domain elements is preserved. The graph g is
a named function even when the length, sequence, or projection is mixed. -/
def projectionContinuous (K P R Q S D F : N) : B :=
  ⨅ A : N, ⨅ f : N, ⨅ p : N, ⨅ q : N,
    (((A ∈ᴮ K) ⊓ is_function A D f ⊓ descendingValue A f R) ⊓ glbValue A f P R p ⊓ edge F p q) ⟹
      ⨆ g : N, is_function A Q g ⊓ projectionSequence F f g ⊓ glbValue A g Q S q

/-- K is the internal initial ordinal bounding sequence lengths. D and F
are the actual dense closed domain and function graph. -/
def partialProjectionValue (K P R Q S D F : N) : B :=
  ((D ⊆ᴮ P) ⊓ is_function D Q F) ⊓
    (projectionDense P R D ⊓ projectionMonotone R S F ⊓ projectionReaches Q S F ⊓ projectionLifts Q R S F) ⊓
    (projectionClosed K P R D ⊓ projectionContinuous K P R Q S D F)

/-- The domain and map of a witness range over all internal sets. The
source is the stronger condition and the target is the weaker condition. -/
def refinementValue (K P R p len bits Q S q oldLen oldBits : N) : B :=
  ⨆ D : N, ⨆ F : N, partialProjectionValue K P R Q S D F ⊓
    pointTest R S F p q ⊓ wordTest R F p len bits oldLen oldBits

theorem projectionIdentity_sequence {A P f : N} {Γ : B} (hf : Γ ≤ is_function A P f) :
    Γ ≤ projectionSequence (projectionIdentity P) f f := by
  refine le_iInf fun i => le_iInf fun x => le_iInf fun y => projection_imp.mpr ?_
  intro Δ hΔ h
  have funΔ := hΔ.trans hf
  have left := (mem_prod_iff.mp (mem_of_mem_subset (subset_prod_of_is_function funΔ) (h.trans inf_le_left))).2
  have right := (mem_prod_iff.mp (mem_of_mem_subset (subset_prod_of_is_function funΔ) (h.trans inf_le_right))).2
  exact projectionIdentity_pair.mpr ⟨left,right,eq_of_is_function_of_eq funΔ bv_refl
    (h.trans inf_le_left) (h.trans inf_le_right)⟩

theorem projectionIdentity_continuous (K P R : N) {Γ : B} :
    Γ ≤ projectionContinuous K P R P R P (projectionIdentity P) := by
  refine le_iInf fun A => le_iInf fun f => le_iInf fun p => le_iInf fun q => projection_imp.mpr ?_
  intro Δ _ h
  have hf : Δ ≤ is_function A P f := h.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have hglb : Δ ≤ glbValue A f P R p := h.trans (inf_le_left.trans inf_le_right)
  have he := (projectionIdentity_pair.mp (h.trans inf_le_right)).2.2
  exact le_iSup_of_le f (le_inf (le_inf hf (projectionIdentity_sequence hf))
    (bv_rw'' he hglb (glbValue_ext_point A f P R)))

theorem projectionIdentity_value (K P R : N) {Γ : B} (ho : Γ ≤ partialOrderValue P R) :
    Γ ≤ partialProjectionValue K P R P R P (projectionIdentity P) := by
  have refl {Δ : B} (h : Δ ≤ Γ) {p : N} (hp : Δ ≤ p ∈ᴮ P) : Δ ≤ edge R p p :=
    (projection_imp.mp (ho.trans (inf_le_right.trans inf_le_left) |>.trans (iInf_le _ p))) Δ h hp
  refine le_inf (le_inf (le_inf subset_self (projectionIdentity_is_function P)) (projectionIdentity_base P R refl))
    (le_inf ?_ (projectionIdentity_continuous K P R))
  exact le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => projection_imp.mpr fun _ _ h =>
    h.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))

theorem refinementValue_refl (K P R p len bits : N) {Γ : B} (ho : Γ ≤ partialOrderValue P R) :
    Γ ≤ refinementValue K P R p len bits P R p len bits :=
  le_iSup_of_le P (le_iSup_of_le (projectionIdentity P) (le_inf
    (le_inf (projectionIdentity_value K P R ho) (projectionIdentity_point P R p))
    (projectionIdentity_word P R p len bits)))

end bSet.ErdosShioyaInternal
