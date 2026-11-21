/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerStageGraphs

@[expose] public section

/-! # Names for lifted strings over the actual image ordinal -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion bSet
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I P : Type u} (U : Ultrafilter I) {θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]

def ordinalImage (o : Ordinal.{u}) : Ordinal.{u} := (boundedGroundEmbedding U θ a o.toZFSet).val.rank

theorem ordinalImage_code (o : Ordinal.{u}) :
    (ordinalImage U a o).toZFSet = (boundedGroundEmbedding U θ a o.toZFSet).val :=
  (boundedCollapse_isOrdinal_of_eventually U θ a (boundedConst U θ a o.toZFSet)
    (fun _ => o.toZFSet) rfl (Eventually.of_forall fun _ => ZFSet.isOrdinal_toZFSet o)).toZFSet_rank_eq

def ordinalLabel {o : Ordinal.{u}} (t : o.ToType) := t.toOrd.val.toZFSet

theorem label_injective (o : Ordinal.{u}) : Function.Injective (@ordinalLabel o) :=
  fun _ _ h => Ordinal.ToType.mk.symm.injective (Subtype.ext (Ordinal.toZFSet_injective h))

theorem label_range (o : Ordinal.{u}) : ZFSet.range (@ordinalLabel o) = o.toZFSet := by
  ext z
  rw [ZFSet.mem_range,Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨_,t.toOrd.property,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨Ordinal.ToType.mk ⟨b,hb⟩,congrArg (fun v : Set.Iio o => v.val.toZFSet)
      (Ordinal.ToType.mk.symm_apply_apply _)⟩

theorem allOrdinal (o : Ordinal.{u}) (p : Point U a o.ToType) :
    pointCode U a ordinalLabel p ∈ (ordinalImage U a o).toZFSet := by
  rw [ordinalImage_code,← label_range o,mem_image_carrier_iff]
  exact ⟨p,rfl⟩

def toIndex (o : Ordinal.{u}) (p : Point U a o.ToType) : (ordinalImage U a o).ToType :=
  let h := Ordinal.mem_toZFSet_iff.mp (allOrdinal U a o p)
  Ordinal.ToType.mk ⟨h.choose,h.choose_spec.1⟩

theorem index_label (o : Ordinal.{u}) (p : Point U a o.ToType) :
    ordinalLabel (toIndex U a o p) = pointCode U a ordinalLabel p := by
  let h := Ordinal.mem_toZFSet_iff.mp (allOrdinal U a o p)
  exact (congrArg (fun z : Set.Iio (ordinalImage U a o) => z.val.toZFSet)
    (Ordinal.ToType.mk.symm_apply_apply ⟨h.choose,h.choose_spec.1⟩)).trans h.choose_spec.2

def indexEquiv (o : Ordinal.{u}) : Point U a o.ToType ≃ (ordinalImage U a o).ToType :=
  Equiv.ofBijective (toIndex U a o) ⟨fun p q h =>
    pointCode_injective U a (label_injective o) ((index_label U a o p).symm.trans
      ((congrArg ordinalLabel h).trans (index_label U a o q))),by
    intro t
    have hm : ordinalLabel t ∈ (ordinalImage U a o).toZFSet :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr t.toOrd.property
    rw [ordinalImage_code,← label_range o,mem_image_carrier_iff] at hm
    obtain ⟨p,hp⟩ := hm
    exact ⟨p,label_injective _ ((index_label U a o p).trans hp)⟩⟩

theorem indexEquiv_label (o : Ordinal.{u}) (p : Point U a o.ToType) :
    ordinalLabel (indexEquiv U a o p) = pointCode U a ordinalLabel p := index_label U a o p

variable [PartialOrder P] [Nonempty P]

end Erdos1172Shioya.UltrapowerStage
