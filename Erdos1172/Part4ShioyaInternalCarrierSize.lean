/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCarrier
public import Erdos1172.Part4GroundIndexNameBound
public import Erdos1172.Part4LevyAnonymousSmallAuxiliary

@[expose] public section

/-! # Cardinal bounds for Shioya conditions named over the anonymous collapse -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal bSet Erdos1172LevyCohen Erdos1172CompleteSubalgebra
open scoped Flypitch
namespace bSet.ErdosShioyaInternal
variable {B : Type u} {θ κ : Cardinal.{u}}

private theorem function_small {V : Type u} (hθ : θ.IsInaccessible) (hV : #V < θ) (hB : #B < θ) :
    #(V → B) < θ := by
  let graph (f : V → B) : Set (V × B) := {p | f p.1 = p.2}
  have inj : Function.Injective graph := by
    intro f g he
    funext i
    exact (he ▸ (show (i,f i) ∈ graph f from rfl) : (i,f i) ∈ graph g).symm
  apply (Cardinal.mk_le_of_injective inj).trans_lt
  rw [Cardinal.mk_set,Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
  exact hθ.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hV hB)

private theorem entry_small (hθ : θ.IsInaccessible) (hB : #B < θ) {α β : Ordinal.{u}}
    (ha : α < θ.ord) (hb : β < θ.ord) :
    #(α.ToType × ((PSet.pSet_prod (PSet.ordinalMk α) (PSet.ordinalMk α)).Type → B) ×
      ((PSet.pSet_prod (PSet.ordinalMk α) (PSet.ordinalMk β)).Type → B)) < θ := by
  have mul {x y : Cardinal.{u}} (hx : x < θ) (hy : y < θ) := Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hx hy
  have row (γ : Ordinal.{u}) (hg : γ < θ.ord) :
      #((PSet.pSet_prod (PSet.ordinalMk α) (PSet.ordinalMk γ)).Type → B) < θ := by
    apply function_small hθ _ hB
    change #((PSet.ordinalMk α).Type × (PSet.ordinalMk γ).Type) < θ
    simp only [Cardinal.mk_prod,Cardinal.lift_id,PSet.ordinalMk_type,Cardinal.mk_toType]
    exact mul (Cardinal.lt_ord.mp ha) (Cardinal.lt_ord.mp hg)
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  exact mul (by simpa only [Cardinal.mk_toType] using (Cardinal.lt_ord.mp ha)) (mul (row _ ha) (row _ hb))

/-- Across all ordinal carriers and string lengths, allowing the preparing
forcing to supply both the order and the incidences still costs at most θ. -/
theorem table_cardinal_le (hθ : θ.IsInaccessible) (hB : #B < θ) : #(Table B θ) ≤ θ := by
  have sum_bound (f : θ.ord.ToType → Cardinal.{u}) (h : ∀ i, f i ≤ θ) : Cardinal.sum f ≤ θ := by
    apply (Cardinal.sum_le_sum f (fun _ => θ) h).trans
    rw [Cardinal.sum_const',Cardinal.mk_ord_toType,Cardinal.mul_eq_self hθ.aleph0_lt.le]
  simp only [Table,Cardinal.mk_sigma]
  exact sum_bound _ fun i => sum_bound _ fun j => (entry_small hθ hB i.toOrd.property j.toOrd.property).le

theorem namedCarrier_injects [NontrivialCompleteBooleanAlgebra B] (hθ : θ.IsInaccessible) (hB : #B < θ)
    (law : Fields B → B) : (⊤ : B) ≤ injects_into (namedCarrier θ law) (check (PSet.ordinalMk θ.ord)) :=
  ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le θ _ (table_cardinal_le hθ hB)

theorem anonymous_table_bound (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    #(Table (anonymousAlgebra κ) θ) ≤ θ := by
  apply table_cardinal_le hθ
  exact (Cardinal.mk_le_of_injective (inclusion_injective (anonymousAlgebra κ))).trans_lt
    ((completion_cardinal_le_two_power κ hκ).trans_lt (hθ.isStrongPrelimit hk))

/-- The injection is internal to the genuine anonymous algebra and covers
all conditions represented by arbitrary mixed tuples satisfying the law. -/
theorem anonymous_namedCarrier_injects (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (law : Fields (anonymousAlgebra κ) → anonymousAlgebra κ) :
    (⊤ : anonymousAlgebra κ) ≤ injects_into (namedCarrier θ law) (check (PSet.ordinalMk θ.ord)) :=
  ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le θ _ (anonymous_table_bound hk hκ hθ)

end bSet.ErdosShioyaInternal
