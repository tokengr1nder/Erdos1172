/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalRegularColumns
public import Erdos1172.Part4ShioyaInternalConditions
public import Erdos1172.Part4BooleanFunctionTransport

@[expose] public section

/-! # Absolute order and word predicates for internal ordinal presentations -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosNameTransport
variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def Fields.map (e : CompleteLatticeHom B C) (s : Fields B) : Fields C :=
  ⟨mapNames e s.carrier,mapNames e s.order,mapNames e s.point,mapNames e s.length,mapNames e s.bits⟩

theorem Fields.map_code (e : CompleteLatticeHom B C) (s : Fields B) :
    mapNames e s.code = (s.map e).code := by simp only [Fields.code,Fields.map,map_pair]

theorem Fields.map_shape (e : CompleteLatticeHom B C) (s : Fields B) (H : bSet B) :
    e (s.shape H) = (s.map e).shape (mapNames e H) := by
  simp only [Fields.shape,Fields.map,map_inf,map_mem,map_subset,ErdosNameTransport.map_prod]

theorem map_checkedEdge (e : CompleteLatticeHom B C) {α β : Ordinal.{u}} (R : bSet B)
    (i : α.ToType) (j : β.ToType) : e (checkedEdge R i j) = checkedEdge (mapNames e R) i j := by
  simp only [checkedEdge,edge,ordinalLabel,map_mem,map_pair,map_check]

theorem map_partialOrder_checked (e : CompleteLatticeHom B C) (α : Ordinal.{u}) (R : bSet B) :
    e (partialOrderValue (ordinalCarrier α) R) = partialOrderValue (ordinalCarrier α) (mapNames e R) := by
  rw [partialOrderValue_checked,partialOrderValue_checked]
  simp only [matrixOrder,map_inf,map_iInf,map_imp,map_checkedEdge,
    map_subset,ErdosNameTransport.map_prod,ordinalCarrier,map_check,apply_ite e,map_top,map_bot]

theorem map_separative_checked (e : CompleteLatticeHom B C) (α : Ordinal.{u}) (R : bSet B) :
    e (separativeValue (ordinalCarrier α) R) = separativeValue (ordinalCarrier α) (mapNames e R) := by
  simp only [separativeValue_checked,matrixSeparative,matrixCompatible,map_iInf,map_iSup,map_imp,
    map_inf,map_compl',map_checkedEdge]

theorem map_regularColumns_checked (e : CompleteLatticeHom B C) (α β : Ordinal.{u}) (R w : bSet B) :
    e (regularColumnsValue (ordinalCarrier α) R (ordinalCarrier β) w) =
      regularColumnsValue (ordinalCarrier α) (mapNames e R) (ordinalCarrier β) (mapNames e w) := by
  rw [regularColumnsValue_checked,regularColumnsValue_checked]
  simp only [matrixRegularColumn,matrixDenseBelow,map_iInf,map_iSup,
    map_imp,map_inf,map_checkedEdge,map_subset,ErdosNameTransport.map_prod,ordinalCarrier,map_check]

def boundedLaws (s : Fields B) : B := partialOrderValue s.carrier s.order ⊓
  (separativeValue s.carrier s.order ⊓ regularColumnsValue s.carrier s.order s.length s.bits)

private theorem boundedLaws_checked {Γ : B} (s : Fields B) {α β : Ordinal.{u}}
    (hc : Γ ≤ s.carrier =ᴮ ordinalCarrier α) (hl : Γ ≤ s.length =ᴮ ordinalCarrier β) :
    Γ ≤ boundedLaws s ↔ Γ ≤ partialOrderValue (ordinalCarrier α) s.order ⊓
      (separativeValue (ordinalCarrier α) s.order ⊓ regularColumnsValue (ordinalCarrier α) s.order (ordinalCarrier β) s.bits) := by
  have pc (x : bSet B) := partialOrderValue_ext (B := B) id_congr (const_congr x)
  have sc (x : bSet B) := separativeValue_ext (B := B) id_congr (const_congr x)
  have rc (r l w : bSet B) := regularColumnsValue_ext (B := B) id_congr (const_congr r) (const_congr l) (const_congr w)
  have rl (p r w : bSet B) := regularColumnsValue_ext (B := B) (const_congr p) (const_congr r) id_congr (const_congr w)
  constructor
  · intro h
    exact le_inf (bv_rw'' hc (h.trans inf_le_left) (pc _)) (le_inf
      (bv_rw'' hc (h.trans (inf_le_right.trans inf_le_left)) (sc _))
      (bv_rw'' (ϕ := fun l => regularColumnsValue (ordinalCarrier α) s.order l s.bits) hl
        (bv_rw'' hc (h.trans (inf_le_right.trans inf_le_right)) (rc s.order s.length s.bits)) (rl _ _ _)))
  · intro h
    exact le_inf (bv_rw'' (bv_symm hc) (h.trans inf_le_left) (pc _)) (le_inf
      (bv_rw'' (bv_symm hc) (h.trans (inf_le_right.trans inf_le_left)) (sc _))
      (bv_rw'' (ϕ := fun l => regularColumnsValue s.carrier s.order l s.bits) (bv_symm hl)
        (bv_rw'' (bv_symm hc) (h.trans (inf_le_right.trans inf_le_right)) (rc s.order (ordinalCarrier β) s.bits))
        (rl _ _ _)))

theorem ordinalCarrier_cases {Γ b : B} {x : bSet B} {o : Ordinal.{u}} (hx : Γ ≤ x ∈ᴮ ordinalCarrier o)
    (branch : ∀ (i : o.ToType) (Δ : B), Δ ≤ Γ → Δ ≤ x =ᴮ ordinalLabel i → Δ ≤ b) : Γ ≤ b := by
  have decomp : (x ∈ᴮ ordinalCarrier o) = ⨆ i : o.ToType, x =ᴮ ordinalLabel i := by
    unfold ordinalCarrier
    rw [PSet.ordinalMk_eq_def o,check_unfold,mem_unfold]
    exact iSup_congr fun _ => top_inf_eq _
  apply ((inf_eq_left.mpr hx).symm.le.trans_eq (congrArg (Γ ⊓ ·) decomp)).trans
  rw [inf_iSup_eq]
  exact iSup_le fun i => branch i _ inf_le_left inf_le_right

/-- At the entire shape guard, all three bounded laws of arbitrary mixed
fields remain valid after any complete Boolean change of base. -/
theorem map_boundedLaws (e : CompleteLatticeHom B C) (θ : Cardinal.{u}) (s : Fields B) {Γ : B}
    (shape : Γ ≤ s.shape (ordinalCarrier θ.ord)) (valid : Γ ≤ boundedLaws s) :
    e Γ ≤ boundedLaws (s.map e) := by
  let target := boundedLaws (s.map e)
  suffices h : Γ ≤ ⨆ a : {a : B // e a ≤ target}, a.val by
    exact ((OrderHomClass.mono e h).trans_eq (map_iSup e _)).trans (iSup_le fun a => a.property)
  apply ordinalCarrier_cases (shape.trans inf_le_left)
  intro i d hd hi
  apply ordinalCarrier_cases (hd.trans (shape.trans (inf_le_right.trans inf_le_left)))
  intro j b hb hj
  have hc := hb.trans hi
  have val := (boundedLaws_checked s hc hj).mp ((hb.trans hd).trans valid)
  have mapped := OrderHomClass.mono e val
  simp only [map_inf,map_partialOrder_checked,map_separative_checked,map_regularColumns_checked] at mapped
  have me (x : bSet B) (o : Ordinal.{u}) (h : b ≤ x =ᴮ ordinalCarrier o) :
      e b ≤ mapNames e x =ᴮ ordinalCarrier o := by
    simpa only [map_bv_eq,ordinalCarrier,map_check] using OrderHomClass.mono e h
  exact le_iSup_of_le ⟨b,(boundedLaws_checked (s.map e) (me _ _ hc) (me _ _ hj)).mpr mapped⟩ le_rfl

end bSet.ErdosShioyaInternal
