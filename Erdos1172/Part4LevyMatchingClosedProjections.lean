/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingClosedStages
public import Erdos1172.Part4LevyInitialBoundedNames

@[expose] public section

/-! # Coherent inclusions of the closed coordinate stages into the full collapse -/

set_option autoImplicit false
noncomputable section
universe u
open Erdos1172PosetCompletion Erdos1172PosetProjection Erdos1172PosetGeneric
open scoped Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching

variable {I J : Type u} (A : J → Type u) (f : I ↪ J)

/-- Read the indicated coordinates in a finite-support product. -/
def coordinateProjection : ProductCondition A →o ProductCondition (fun i => A (f i)) where
  toFun := DFinsupp.comapDomain f f.injective
  monotone' _ _ h i := h (f i)

theorem coordinateProjection_lifts : ExactLifts (coordinateProjection A f) := by
  classical
  intro p q h
  let data (j : J) := if hj : ∃ i, f i = j then
    (cast (congrArg (fun k => Erdos1172Collapse.Condition (A k)) hj.choose_spec) (q hj.choose)) else p j
  have on (i : I) : data (f i) = q i := by
    have hi : ∃ k, f k = f i := ⟨i,rfl⟩
    dsimp only [data]
    rw [dif_pos hi]
    have move (k l : I) (hk : k = l) (e : f k = f l) :
        cast (congrArg (fun j => Erdos1172Collapse.Condition (A j)) e) (q k) = q l := by subst l; rfl
    exact move _ _ (f.injective hi.choose_spec) hi.choose_spec
  let S := (q.support.map f) ∪ p.support
  let r : ProductCondition A := DFinsupp.mk S (fun j => data j.val)
  have val (j : J) : r j = data j := by
    by_cases hj : j ∈ S
    · exact DFinsupp.mk_of_mem hj
    rw [show r j = 0 from DFinsupp.mk_of_notMem hj]
    by_cases hjf : ∃ i, f i = j
    · obtain ⟨i,rfl⟩ := hjf
      exact (DFinsupp.notMem_support_iff.mp (fun hi => hj (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i,hi,rfl⟩)))).symm.trans (on i).symm
    · rw [show data j = p j from dif_neg hjf]
      exact (DFinsupp.notMem_support_iff.mp (fun hp => hj (Finset.mem_union_right _ hp))).symm
  refine ⟨r,?_,DFinsupp.ext (fun i => (val (f i)).trans (on i))⟩
  intro j
  rw [val]
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i,rfl⟩ := hj
    exact (on i).le.trans (h i)
  · exact (dif_neg hj : data j = p j).le

theorem coordinateProjection_surjective : Function.Surjective (coordinateProjection A f) := by
  intro p
  obtain ⟨r,_,hr⟩ := coordinateProjection_lifts A f (⊤ : ProductCondition A) p (fun _ => le_top)
  exact ⟨r,hr⟩

def coordinateHom : CompleteLatticeHom (Completion (ProductCondition (fun i => A (f i))))
    (Completion (ProductCondition A)) := completionHom _ (coordinateProjection_lifts A f)

theorem coordinateHom_injective : Function.Injective (coordinateHom A f) :=
  completionHom_injective _ _ (coordinateProjection_surjective A f)

variable {θ : Cardinal.{u}}

def closedHom {i j : θ.ord.ToType} (h : i ≤ j) : CompleteLatticeHom (ClosedStage i) (ClosedStage j) :=
  coordinateHom (fun a : Set.Iic j => Set.Iio a.val) (Set.embeddingOfSubset _ _ (Set.Iic_subset_Iic.mpr h))

def fullClosedHom (i : θ.ord.ToType) : CompleteLatticeHom (ClosedStage i) (Completion (BelowCondition θ)) :=
  coordinateHom (fun a : θ.ord.ToType => Set.Iio a) (Function.Embedding.subtype (· ∈ Set.Iic i))

theorem closedHom_injective {i j : θ.ord.ToType} (h : i ≤ j) : Function.Injective (closedHom h) :=
  coordinateHom_injective _ _

theorem fullClosedHom_injective (i : θ.ord.ToType) : Function.Injective (fullClosedHom i) :=
  coordinateHom_injective _ _

theorem fullClosedHom_commute {i j : θ.ord.ToType} (h : i ≤ j) (x : ClosedStage i) :
    fullClosedHom j (closedHom h x) = fullClosedHom i x := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  let q : ClosedCondition j := DFinsupp.comapDomain Subtype.val Subtype.val_injective p
  let f := Set.embeddingOfSubset _ _ (Set.Iic_subset_Iic.mpr h)
  have eq : DFinsupp.comapDomain f f.injective q = (DFinsupp.comapDomain Subtype.val Subtype.val_injective p : ClosedCondition i) :=
    DFinsupp.ext fun _ => rfl
  change DFinsupp.comapDomain f f.injective q ∈ x.val ↔
    (DFinsupp.comapDomain Subtype.val Subtype.val_injective p : ClosedCondition i) ∈ x.val
  exact Iff.of_eq (congrArg (fun r : ClosedCondition i => r ∈ x.val) eq)

theorem closedHom_id (i : θ.ord.ToType) (x : ClosedStage i) : closedHom (le_refl i) x = x :=
  fullClosedHom_injective i (fullClosedHom_commute _ x)

theorem closedHom_comp {i j k : θ.ord.ToType} (h : i ≤ j) (h' : j ≤ k) (x : ClosedStage i) :
    closedHom (h.trans h') x = closedHom h' (closedHom h x) := by
  apply fullClosedHom_injective k
  rw [fullClosedHom_commute,fullClosedHom_commute,fullClosedHom_commute]

/-- A principal cone supported through i is already in the bounded range. -/
theorem fullClosedHom_condition (i : θ.ord.ToType) (p : BelowCondition θ) (hp : SupportedOn (Set.Iic i) p) :
    fullClosedHom i (condition (DFinsupp.comapDomain Subtype.val Subtype.val_injective p : ClosedCondition i)) = condition p := by
  apply (completionHom_condition_eq_iSup _ (coordinateProjection_lifts (fun a : θ.ord.ToType => Set.Iio a)
    (Function.Embedding.subtype (· ∈ Set.Iic i))) _).trans
  apply le_antisymm
  · apply iSup_le
    intro q
    apply condition_mono
    intro j
    by_cases hj : j ∈ Set.Iic i
    · exact q.property ⟨j,hj⟩
    · rw [hp j hj]
      exact le_top
  · exact le_iSup_of_le ⟨p,le_rfl⟩ le_rfl

end Erdos1172LevyCollapse.Matching
