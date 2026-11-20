/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerBits
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

theorem ordinalImage_strictMono : StrictMono (ordinalImage U a) := by
  intro v w h
  apply Ordinal.toZFSet_mem_toZFSet_iff.mp
  rw [ordinalImage_code,ordinalImage_code,boundedGroundEmbedding_val,boundedGroundEmbedding_val,
    boundedCollapse_mem_boundedCollapse_iff]
  exact Eventually.of_forall (fun _ => Ordinal.toZFSet_mem_toZFSet_iff.mpr h)

theorem indexEquiv_include {v w : Ordinal.{u}} (h : v ≤ w) (k : Point U a v.ToType) :
    indexEquiv U a w (map U a (StringName.includeIndex h) k) =
      StringName.includeIndex ((ordinalImage_strictMono U a).monotone h) (indexEquiv U a v k) := by
  apply label_injective _
  rw [indexEquiv_label,pointCode_map]
  have he (x : v.ToType) : ordinalLabel (StringName.includeIndex h x) = ordinalLabel x :=
    congrArg Ordinal.toZFSet (StringName.includeIndex_toOrd h x)
  rw [show ordinalLabel ∘ StringName.includeIndex h = @ordinalLabel v from funext he,
    ← indexEquiv_label]
  exact (congrArg Ordinal.toZFSet (StringName.includeIndex_toOrd _ _)).symm

variable [PartialOrder P] [Nonempty P]

local instance pointNonempty : Nonempty (Point U a P) := ⟨diagonal U a (Classical.choice inferInstance)⟩

instance completionAlgebra : NontrivialCompleteBooleanAlgebra (Completion (Point U a P)) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

def liftedString (o : Ordinal.{u}) (b : o.ToType → Completion P) :
    StringName (Completion (Point U a P)) (ordinalImage U a o) :=
  StringName.ofBits _ (fun j => stringBit U a b ((indexEquiv U a o).symm j))

theorem liftedString_bit (o : Ordinal.{u}) (b : o.ToType → Completion P) (j : Point U a o.ToType) :
    (liftedString U a o b).bits (indexEquiv U a o j) = stringBit U a b j := by
  simp only [liftedString,StringName.bits_ofBits,Equiv.symm_apply_apply]

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
private theorem map_comp {V X Y : Type u} (g : X → Y) (f : V → X) (z : Point U a V) :
    map U a g (map U a f z) = map U a (g ∘ f) z := Subtype.ext (Germ.map_map g f z.val)

theorem liftedString_extension {Q : Type u} [PartialOrder Q] [Nonempty Q] {κ : Cardinal.{u}}
    (π : PartialProjection κ P Q) (hθ : θ.IsRegular) (fine : FineOn U a) (normal : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hP : ShortInfima κ P) (p : P) {v w : Ordinal.{u}} (h : v ≤ w)
    (s : v.ToType → Completion Q) (t : w.ToType → Completion P)
    (agree : ∀ i, condition p ⊓ π.booleanHom (s i) = condition p ⊓ t (StringName.includeIndex h i)) :
    condition (diagonal U a p) ≤ extensionValue (projection U a π hθ fine normal ht hP).booleanHom
      (liftedString U a v s) (liftedString U a w t) := by
  apply extensionValue_of_bits _ _ _ ((ordinalImage_strictMono U a).monotone h)
  intro j
  obtain ⟨k,rfl⟩ := (indexEquiv U a v).surjective j
  rw [← indexEquiv_include U a h,liftedString_bit,liftedString_bit]
  unfold stringBit
  rw [← booleanValue_projection,map_comp,map_comp]
  exact stringBit_local U a (π.booleanHom ∘ s) (t ∘ StringName.includeIndex h) p agree k

/-- Each ground uniformization edge supplies a genuine target-name
extension in the lifted stage, at its diagonal designated source. -/
theorem edge_extension {κ : Cardinal.{u}} {p q : Condition κ θ} (E : Uniformization.Edge p q)
    (hθ : θ.IsRegular) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    condition (diagonal U a E.source) ≤
      extensionValue (projection U a E.projection hθ fine normal ht q.complete).booleanHom
        (liftedString U a _ p.bits) (liftedString U a _ q.bits) := by
  obtain ⟨h,hs⟩ := (extensionValue_iff_bits E.projection.booleanHom p.name q.name
    (condition_ne_bot E.source)).mp E.string_le
  apply liftedString_extension U a (P := q.Poset) (Q := p.Poset) E.projection
    hθ fine normal ht q.complete E.source h
  intro i
  have bound := hs i
  rw [show p.name.bits i = p.bits i from StringName.bits_ofBits _ _,
    show q.name.bits (StringName.includeIndex h i) = q.bits (StringName.includeIndex h i) from
      StringName.bits_ofBits _ _] at bound
  exact bound

omit [CountableInterFilter (U : Filter I)] in
theorem edge_point {κ : Cardinal.{u}} {p q : Condition κ θ} (E : Uniformization.Edge p q)
    (hθ : θ.IsRegular) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    condition (diagonal U a E.source) ≤
      (projection U a E.projection hθ fine normal ht q.complete).booleanHom (condition (diagonal U a p.point)) := by
  rw [← booleanValue_condition U a (diagonal U a E.source),
    ← booleanValue_condition U a (diagonal U a p.point),← booleanValue_projection]
  exact booleanValue_mono U a ((diagonal U a (P := q.Algebra)).monotone E.point_le)

end Erdos1172Shioya.UltrapowerStage
