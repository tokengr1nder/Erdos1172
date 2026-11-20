/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BoundedEmbeddingSmallRange
public import Erdos1172.Part4LevyInitialGenericLift

@[expose] public section

/-! # Finite Lévy condition graphs under the ground elementary embedding -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
open scoped Erdos1172LevyCollapse
universe u
namespace Erdos1172LevyCollapse
variable {κ θ : Cardinal.{u}}

/-- A graph entry gives the coordinate, the finite position and its ordinal value. -/
def entryTriple (α : Ordinal.{u}) (n : ℕ) (β : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.pair α.toZFSet (ZFSet.pair (n : Ordinal.{u}).toZFSet β.toZFSet)

def conditionGraph (p : BelowCondition κ) : ZFSet.{u} := by
  classical
  exact ZFSet.range (fun t : Σ i : p.support, Fin (p i.val).entries.length =>
    entryTriple t.1.val.toOrd.val t.2.val ((p t.1.val).entries.get t.2).val.toOrd.val)

theorem mem_conditionGraph_iff (z : ZFSet.{u}) (p : BelowCondition κ) :
    z ∈ conditionGraph p ↔ ∃ (i : κ.ord.ToType) (n : ℕ) (hn : n < (p i).entries.length),
      entryTriple i.toOrd.val n ((p i).entries[n]).val.toOrd.val = z := by
  classical
  rw [conditionGraph,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨i,n⟩,rfl⟩
    exact ⟨i.val,n.val,n.isLt,rfl⟩
  · rintro ⟨i,n,hn,rfl⟩
    have hi : i ∈ p.support := DFinsupp.mem_support_iff.mpr (by
      intro h
      rw [h] at hn
      exact Nat.not_lt_zero _ hn)
    exact ⟨⟨⟨i,hi⟩,⟨n,hn⟩⟩,rfl⟩

private theorem typein_toType_eq_toOrd {o : Ordinal.{u}} (x : o.ToType) :
    (Ordinal.typein (· < ·)) x = x.toOrd.val := by
  rw [← Ordinal.type_Iio_lt x]
  let bOrd : Ordinal.{u} := x.toOrd.val
  have hbOrd : bOrd < o := Set.mem_Iio.mp x.toOrd.property
  let E : Set.Iio x ≃o Set.Iio bOrd := {
    toFun := fun z => ⟨z.val.toOrd.val, Set.mem_Iio.mpr (Subtype.mk_lt_mk.mp (Ordinal.ToType.mk.symm.lt_iff_lt.mpr z.property))⟩
    invFun := fun z =>
      let q : o.ToType := Ordinal.ToType.mk ⟨z.val, Set.mem_Iio.mpr ((Set.mem_Iio.mp z.property).trans hbOrd)⟩
      ⟨q, Ordinal.ToType.mk.symm.lt_iff_lt.mp (by
        change Ordinal.ToType.mk.symm q < Ordinal.ToType.mk.symm x
        rw [Ordinal.ToType.mk.symm_apply_apply]
        exact Subtype.mk_lt_mk.mpr (Set.mem_Iio.mp z.property))⟩
    left_inv := fun z => Subtype.ext (Ordinal.ToType.mk.apply_symm_apply z.val)
    right_inv := fun z => Subtype.ext (by
      change (Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨z.val, _⟩)).val = z.val
      rw [Ordinal.ToType.mk.symm_apply_apply])
    map_rel_iff' := fun {_ _} => Subtype.mk_le_mk.trans Ordinal.ToType.mk.symm.le_iff_le }
  exact (E.trans Ordinal.ToType.mk).toRelIsoLT.ordinalType_congr.trans (Ordinal.type_toType bOrd)

theorem initialCoordinate_ordinal (h : κ ≤ θ) (i : κ.ord.ToType) :
    (initialCoordinate h i).toOrd.val = i.toOrd.val :=
  (typein_toType_eq_toOrd _).symm.trans ((Ordinal.typein_apply (initialCoordinate h) i).trans (typein_toType_eq_toOrd i))

private theorem initialAlphabet_ordinal (h : κ ≤ θ) (i : κ.ord.ToType) (x : Set.Iio i) :
    ((initialAlphabet h i x).val).toOrd.val = x.val.toOrd.val := initialCoordinate_ordinal h x.val

theorem conditionGraph_zeroExtension (h : κ ≤ θ) (p : BelowCondition κ) :
    conditionGraph (zeroExtension h p) = conditionGraph p := by
  classical
  ext z
  rw [mem_conditionGraph_iff,mem_conditionGraph_iff]
  constructor
  · rintro ⟨k,n,hn,hz⟩
    by_cases hk : k ∈ Set.range (initialCoordinate h)
    · obtain ⟨i,rfl⟩ := hk
      have hr := zeroExtension_entries h p i
      have hn' : n < (p i).entries.length := by simpa only [hr,List.length_map] using hn
      refine ⟨i,n,hn',?_⟩
      simpa only [hr,List.getElem_map,initialAlphabet_ordinal,initialCoordinate_ordinal] using hz
    · rw [zeroExtension_off h p hk] at hn
      exact (Nat.not_lt_zero _ hn).elim
  · rintro ⟨i,n,hn,hz⟩
    have hr := zeroExtension_entries h p i
    have hn' : n < ((zeroExtension h p) (initialCoordinate h i)).entries.length := by simpa only [hr,List.length_map]
    refine ⟨initialCoordinate h i,n,hn',?_⟩
    simpa only [hr,List.getElem_map,initialAlphabet_ordinal,initialCoordinate_ordinal] using hz

theorem boundedGroundEmbedding_conditionGraph {I : Type u} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ] [Nonempty θ.ord.ToType]
    (hκ : Cardinal.aleph0 ≤ κ) (h : κ ≤ θ) (p : BelowCondition κ) :
    (boundedGroundEmbedding U θ a (conditionGraph p)).val = conditionGraph (zeroExtension h p) := by
  classical
  rw [conditionGraph_zeroExtension h,conditionGraph,boundedGroundEmbedding_small_range U κ θ a (Cardinal.mk_lt_aleph0.trans_le hκ)]
  apply congrArg ZFSet.range
  funext t
  have hn : (t.2.val : Ordinal.{u}) < κ.ord :=
    (Ordinal.natCast_lt_omega0 _).trans_le (by simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hκ)
  unfold entryTriple
  rw [boundedGroundEmbedding_pair U κ θ a hκ,boundedGroundEmbedding_pair U κ θ a hκ,
    boundedGroundEmbedding_fix_below U κ θ a _ t.1.val.toOrd.property,
    boundedGroundEmbedding_fix_below U κ θ a _ hn,boundedGroundEmbedding_fix_below U κ θ a _]
  exact ((p t.1.val).entries.get t.2).val.toOrd.property

private theorem entryTriple_inj {α β α' β' : Ordinal.{u}} {n m : ℕ}
    (h : entryTriple α n β = entryTriple α' m β') : α = α' ∧ n = m ∧ β = β' := by
  obtain ⟨ha,ht⟩ := ZFSet.pair_inj.mp h
  obtain ⟨hn,hb⟩ := ZFSet.pair_inj.mp ht
  exact ⟨Ordinal.toZFSet_injective ha,Nat.cast_injective (R := Ordinal.{u}) (Ordinal.toZFSet_injective hn),
    Ordinal.toZFSet_injective hb⟩

/-- The graph encoding carries the actual extension relation into reverse inclusion. -/
theorem conditionGraph_subset_iff (p q : BelowCondition κ) :
    conditionGraph p ⊆ conditionGraph q ↔ q ≤ p := by
  constructor
  · intro sub i
    have one (n : ℕ) (hn : n < (p i).entries.length) :
        ∃ hm : n < (q i).entries.length, (q i).entries[n] = (p i).entries[n] := by
      have mem := sub ((mem_conditionGraph_iff _ p).mpr ⟨i,n,hn,rfl⟩)
      obtain ⟨k,m,hm,he⟩ := (mem_conditionGraph_iff _ q).mp mem
      obtain ⟨hi,hmn,hv⟩ := entryTriple_inj he
      have hki : k = i := Ordinal.ToType.mk.symm.injective (Subtype.ext hi)
      subst k
      subst m
      exact ⟨hm,Subtype.ext (Ordinal.ToType.mk.symm.injective (Subtype.ext hv))⟩
    apply List.prefix_iff_getElem.mpr
    have hlen : (p i).entries.length ≤ (q i).entries.length := by
      by_contra! hn
      exact (Nat.lt_irrefl _) (one _ hn).choose
    exact ⟨hlen,fun n hn => (one n hn).choose_spec.symm⟩
  · intro hp z hz
    obtain ⟨i,n,hn,rfl⟩ := (mem_conditionGraph_iff _ p).mp hz
    have hr : (p i).entries <+: (q i).entries := hp i
    refine (mem_conditionGraph_iff _ q).mpr ⟨i,n,hn.trans_le hr.length_le,?_⟩
    rw [← hr.getElem hn]

theorem conditionGraph_injective : Function.Injective (conditionGraph (κ := κ)) := by
  intro p q h
  exact le_antisymm ((conditionGraph_subset_iff q p).mp (h ▸ le_rfl))
    ((conditionGraph_subset_iff p q).mp (h ▸ le_rfl))

open scoped Flypitch
open bSet ErdosNameTransport Erdos1172PosetCompletion

/-- Names the generic using the set-theoretic condition codes acted on by the embedding. -/
def conditionGraphGeneric (κ : Cardinal.{u}) : bSet (Completion (BelowCondition κ)) :=
  .mk (BelowCondition κ) (fun p => check (conditionGraph p).out) condition

theorem conditionGraphGeneric_mem (p : BelowCondition κ) :
    check (conditionGraph p).out ∈ᴮ conditionGraphGeneric κ = condition p := by
  apply le_antisymm _ (mem_mk' (conditionGraphGeneric κ) p)
  rw [mem_unfold]
  apply iSup_le
  intro q
  change BelowCondition κ at q
  change condition q ⊓ (check (conditionGraph p).out =ᴮ check (conditionGraph q).out) ≤ condition p
  by_cases h : p = q
  · subst q
    exact inf_le_left
  · have hn : ¬ PSet.Equiv (conditionGraph p).out (conditionGraph q).out := by
      intro he
      exact h (conditionGraph_injective (by simpa only [ZFSet.mk_out] using ZFSet.sound he))
    exact (inf_le_right.trans_eq (check_bv_eq_bot_of_not_equiv hn)).trans bot_le

theorem initial_generic_image_condition {I : Type u} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ] [Nonempty θ.ord.ToType]
    (hκ : Cardinal.aleph0 ≤ κ) (h : κ ≤ θ) (p : BelowCondition κ) :
    initialCollapseHom h (check (conditionGraph p).out ∈ᴮ conditionGraphGeneric κ) =
      (check (boundedGroundEmbedding U θ a (conditionGraph p)).val.out ∈ᴮ conditionGraphGeneric θ) := by
  rw [boundedGroundEmbedding_conditionGraph U a hκ h,conditionGraphGeneric_mem,conditionGraphGeneric_mem,
    initialCollapseHom_condition]

/-- The entire pointwise image of the lower generic in the upper collapse
universe. Each image condition carries its original generic truth value. -/
def initialGenericImage {I : Type u} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] (h : κ ≤ θ) :
    bSet (Completion (BelowCondition θ)) :=
  .mk (BelowCondition κ) (fun p => check (boundedGroundEmbedding U θ a (conditionGraph p)).val.out)
    (fun p => initialCollapseHom h (condition p))

theorem initialGenericImage_subset {I : Type u} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ] [Nonempty θ.ord.ToType]
    (hκ : Cardinal.aleph0 ≤ κ) (h : κ ≤ θ) :
    (⊤ : Completion (BelowCondition θ)) ≤ initialGenericImage U a h ⊆ᴮ conditionGraphGeneric θ := by
  rw [subset_unfold]
  apply le_iInf
  intro p
  change BelowCondition κ at p
  rw [← deduction,top_inf_eq]
  change initialCollapseHom h (condition p) ≤ check (boundedGroundEmbedding U θ a (conditionGraph p)).val.out ∈ᴮ _
  exact (congrArg (initialCollapseHom h) (conditionGraphGeneric_mem p).symm).le.trans
    (initial_generic_image_condition U a hκ h p).le

end Erdos1172LevyCollapse
