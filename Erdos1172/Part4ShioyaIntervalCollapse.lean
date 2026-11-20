/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaStringCoding
public import Erdos1172.Part4ShioyaCollapseSurjection
public import Erdos1172.Part4ShioyaGenericMatrixSurjection
public import Erdos1172.Part4ShioyaDenseCollapse

@[expose] public section

/-! # Collapse matrices in the dual Shioya forcing

Below any condition, include a small partial-function collapse in its presentation
and record its generic graph in fresh positions of the string. The row and column
identities hold in the Boolean completion of this enlarged presentation.
-/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion
open scoped Flypitch
universe u

namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)]

private theorem map_cover {B C I : Type u} [CompleteLattice B] [CompleteLattice C]
    (e : CompleteLatticeHom B C) (f : I → B) (hf : (⨆ i, f i) = ⊤) :
    (⨆ i, e (f i)) = ⊤ := by rw [← map_iSup, hf, map_top]

private theorem map_disjoint {B C : Type u} [CompleteLattice B] [CompleteLattice C]
    (e : CompleteLatticeHom B C) (x y : B) (h : x ⊓ y = ⊥) :
    e x ⊓ e y = ⊥ := by rw [← map_inf, h, map_bot]

theorem exists_collapse_matrix (p : Condition κ θ) (α : Ordinal.{u}) [Nontrivial α.ToType]
    (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible) (hα : α < θ.ord) :
    ∃ w : Condition κ θ, w ≤ p ∧
      ∃ slot : (κ.ord.ToType × α.ToType) ↪ w.length.toOrd.val.ToType,
        (∀ i, (⨆ x, w.bits (slot (i,x))) = ⊤) ∧
        (∀ x, (⨆ i, w.bits (slot (i,x))) = ⊤) ∧
        ∀ i x y, x ≠ y → w.bits (slot (i,x)) ⊓ w.bits (slot (i,y)) = ⊥ := by
  have hαcard : Cardinal.mk α.ToType < θ := by
    rw [Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp hα
  have hT : Cardinal.mk (κ.ord.ToType × α.ToType) < θ := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_ord_toType]
    exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hκθ hαcard
  have hω : Cardinal.aleph0 ≤ κ := (Fact.out : Cardinal.aleph0 < κ).le
  let q : Collapse.Condition κ α.ToType := Collapse.empty (Cardinal.aleph0_pos.trans_le hω)
  obtain ⟨v, e, _, _, hv⟩ := Condition.exists_product_refinement p q
    (Collapse.cardinal_lt hθ hκθ hαcard) hθ (Collapse.separative hω) (Collapse.shortInfima hκ)
  let π := productProjection (κ := κ) (e.trans OrderIso.prodComm) p.point
  let payload (t : κ.ord.ToType × α.ToType) : v.Algebra := π.booleanHom (Collapse.entry κ t.1 t.2)
  let slots := tailSlots v.length hθ.aleph0_lt.le hT
  let w := v.append slots payload
  refine ⟨w, (show w ≤ v from v.append_refines slots payload).trans hv, slots.slot, ?_, ?_, ?_⟩
  · intro i
    change (⨆ x, (v.append slots payload).bits (slots.slot (i,x))) = ⊤
    simp only [Condition.append_at, payload]
    exact map_cover π.booleanHom (fun x : α.ToType => Collapse.entry κ i x) (Collapse.entry_row κ hω i)
  · intro x
    change (⨆ i, (v.append slots payload).bits (slots.slot (i,x))) = ⊤
    simp only [Condition.append_at, payload]
    exact map_cover π.booleanHom (fun i => Collapse.entry κ i x) (Collapse.entry_column κ hω x)
  · intro i x y hxy
    change (v.append slots payload).bits (slots.slot (i,x)) ⊓
      (v.append slots payload).bits (slots.slot (i,y)) = ⊥
    simp only [Condition.append_at, payload]
    exact map_disjoint π.booleanHom _ _ (Collapse.entry_disjoint κ i hxy)

variable [Nonempty (Condition κ θ)]

theorem dense_collapse_surjections (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible) :
    DenseCheckedSurjections κ θ := by
  intro α hl hu p
  have : Nontrivial α.ToType := Cardinal.one_lt_iff_nontrivial.mp (by
    rw [Cardinal.mk_toType]
    exact Cardinal.one_lt_aleph0.trans_le ((Fact.out : Cardinal.aleph0 < κ).le.trans
      (Cardinal.ord_le.mp hl.le)))
  obtain ⟨w, hwp, slot, hrow, hcol, hdisj⟩ := exists_collapse_matrix p α hκ hκθ hθ hu
  let s := fun (i : κ.ord.ToType) (x : α.ToType) => slot (i,x)
  have hg := genericMatrixGraph_surjection κ.ord α w s
    (fun i => le_top.trans_eq (hrow i).symm)
    (fun x => le_top.trans_eq (hcol x).symm)
    (fun i x y h => by
      change condition w.point ⊓ (w.bits (slot (i,x)) ⊓ w.bits (slot (i,y))) = ⊥
      exact bot_unique (inf_le_right.trans (hdisj i x y h).le))
  exact ⟨w, hwp, le_iSup_of_le (genericMatrixGraph κ.ord α w s)
    (le_inf (hg.trans (inf_le_left.trans inf_le_left)) (hg.trans inf_le_right))⟩

/-- Every ordinal below the ground inaccessible injects into the ground κ
in the Boolean-valued universe of the dual Shioya forcing. -/
theorem interval_collapse (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible) :
    (⊤ : Algebra κ θ) ≤ ⨅ x, _root_.imp (x ∈ᴮ check (PSet.ordinalMk θ.ord))
      (injects_into x (check (PSet.ordinalMk κ.ord))) :=
  mixed_below_injects_of_dense_surjections κ θ (dense_collapse_surjections hκ hκθ hθ)

end Erdos1172Shioya
