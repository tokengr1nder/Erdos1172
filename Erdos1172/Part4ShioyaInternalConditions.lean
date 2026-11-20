/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCarrierSize
public import Erdos1172.Part4ShioyaInternalOrder
public import Erdos1172.Part4ShioyaInternalShortInfima

@[expose] public section

/-! # The named Shioya condition set over a preparing Boolean algebra -/

set_option autoImplicit false
noncomputable section
universe u
open bSet Lattice ErdosOmegaTwo Erdos1172LevyCohen
open scoped Flypitch
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B] {θ κ : Cardinal.{u}}
local notation "N" => bSet B

theorem Fields.code_eq_iff (s t : Fields B) {Γ : B} :
    Γ ≤ s.code =ᴮ t.code ↔ (Γ ≤ s.carrier =ᴮ t.carrier) ∧ (Γ ≤ s.order =ᴮ t.order) ∧
      (Γ ≤ s.point =ᴮ t.point) ∧ (Γ ≤ s.length =ᴮ t.length) ∧ (Γ ≤ s.bits =ᴮ t.bits) := by
  constructor
  · intro h
    have rest := eq_of_eq_pair_right' h
    have tail := eq_of_eq_pair_right' rest
    have last := eq_of_eq_pair_right' tail
    exact ⟨eq_of_eq_pair_left' h,eq_of_eq_pair_left' rest,eq_of_eq_pair_left' tail,
      eq_of_eq_pair_left' last,eq_of_eq_pair_right' last⟩
  · rintro ⟨hP,hR,hp,hL,hM⟩
    exact pair_congr hP (pair_congr hR (pair_congr hp (pair_congr hL hM)))

theorem Fields.transport_shape (s t : Fields B) (H : N) {Γ : B} (he : Γ ≤ s.code =ᴮ t.code)
    (h : Γ ≤ s.shape H) : Γ ≤ t.shape H := by
  obtain ⟨hP,hR,hp,hL,hM⟩ := (Fields.code_eq_iff s t).mp he
  have rest := h.trans inf_le_right
  have tail := rest.trans inf_le_right
  have last := tail.trans inf_le_right
  exact le_inf (mem_congr hP bv_refl (h.trans inf_le_left)) (le_inf (mem_congr hL bv_refl (rest.trans inf_le_left))
    (le_inf (mem_congr hp hP (tail.trans inf_le_left)) (le_inf
      (subset_trans' (subset_of_eq (bv_symm hR)) (subset_trans' (last.trans inf_le_left) (subset_of_eq (prod_congr hP hP))))
      (subset_trans' (subset_of_eq (bv_symm hM)) (subset_trans' (last.trans inf_le_right) (subset_of_eq (prod_congr hP hL)))))))

/-- All four requirements, including short completeness and regular open
columns, are evaluated on internal sets in the preparing universe. -/
def conditionLaw (K : N) (t : Fields B) : B :=
  partialOrderValue t.carrier t.order ⊓ (separativeValue t.carrier t.order ⊓
    (shortInfimaValue K t.carrier t.order ⊓ regularColumnsValue t.carrier t.order t.length t.bits))

theorem transport_conditionLaw (K : N) (s t : Fields B) {Γ : B} (he : Γ ≤ s.code =ᴮ t.code)
    (h : Γ ≤ conditionLaw K s) : Γ ≤ conditionLaw K t := by
  obtain ⟨p,r,_,l,m⟩ := (Fields.code_eq_iff s t).mp he
  have tail := h.trans inf_le_right
  have last := tail.trans inf_le_right
  refine le_inf ?_ (le_inf ?_ (le_inf ?_ ?_))
  · exact bv_rw'' r (bv_rw'' p (h.trans inf_le_left) (partialOrderValue_ext id_congr (const_congr _)))
      (partialOrderValue_ext (const_congr _) id_congr)
  · exact bv_rw'' r (bv_rw'' p (tail.trans inf_le_left) (separativeValue_ext id_congr (const_congr _)))
      (separativeValue_ext (const_congr _) id_congr)
  · exact bv_rw'' r (bv_rw'' p (last.trans inf_le_left) (shortInfimaValue_ext_carrier _ _))
      (shortInfimaValue_ext_order _ _)
  · apply bv_rw'' m _ (regularColumnsValue_ext (const_congr _) (const_congr _) (const_congr _) id_congr)
    apply bv_rw'' l _ (regularColumnsValue_ext (const_congr _) (const_congr _) id_congr (const_congr _))
    apply bv_rw'' r _ (regularColumnsValue_ext (const_congr _) id_congr (const_congr _) (const_congr _))
    exact bv_rw'' p (last.trans inf_le_right) (regularColumnsValue_ext id_congr (const_congr _) (const_congr _) (const_congr _))

def conditionSet (K : N) (θ : Cardinal.{u}) : N := namedCarrier θ (conditionLaw K)

/-- Exact membership for arbitrary mixed input fields, including after any
localization of the preparing forcing. -/
theorem code_mem_conditionSet (K : N) (θ : Cardinal.{u}) (t : Fields B) :
    (t.code ∈ᴮ conditionSet K θ) = t.shape (check (PSet.ordinalMk θ.ord)) ⊓ conditionLaw K t := by
  rw [conditionSet,mem_namedCarrier]
  apply le_antisymm (iSup_le fun s => ?_) (le_iSup_of_le t (le_inf bv_refl le_rfl))
  exact le_inf (Fields.transport_shape s t _ (bv_symm inf_le_left) (inf_le_right.trans inf_le_left))
    (transport_conditionLaw K s t (bv_symm inf_le_left) (inf_le_right.trans inf_le_right))

/-- The condition carrier is computed in the actual anonymous extension
where the critical ordinal becomes its first uncountable ordinal. -/
def anonymousConditions (κ θ : Cardinal.{u}) : bSet (anonymousAlgebra κ) := conditionSet omegaOne θ

theorem anonymousConditions_injects (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    (⊤ : anonymousAlgebra κ) ≤ injects_into (anonymousConditions κ θ) (check (PSet.ordinalMk θ.ord)) :=
  anonymous_namedCarrier_injects hk hκ hθ _

end bSet.ErdosShioyaInternal
