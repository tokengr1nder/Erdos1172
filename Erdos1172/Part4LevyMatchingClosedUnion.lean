/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingClosedProjections
public import Erdos1172.Part4LevyMatchingUnion

@[expose] public section

/-! # Amalgamating the closed stages into a complete embedding of Col(ω,<θ) -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PosetCompletion
open scoped Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching

variable {θ : Cardinal.{u}}

def cardinalStage {μ : Cardinal.{u}} (hm : μ < θ) : θ.ord.ToType :=
  Ordinal.ToType.mk ⟨μ.ord,Cardinal.ord_lt_ord.mpr hm⟩

theorem cardinalStage_rank {μ : Cardinal.{u}} (hm : μ < θ) : (cardinalStage hm).toOrd.val = μ.ord :=
  congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

private theorem initial_in_closed {μ : Cardinal.{u}} (hm : μ < θ) (x : Completion (BelowCondition μ)) :
    ∃ y : ClosedStage (cardinalStage hm), fullClosedHom _ y = initialCollapseHom hm.le x := by
  let i := cardinalStage hm
  obtain ⟨A,_,_,hA⟩ := exists_condition_antichain_sup x
  let p (a : A) := zeroExtension hm.le a.val
  let q (a : A) : ClosedCondition i := DFinsupp.comapDomain Subtype.val Subtype.val_injective (p a)
  have support (a : A) : SupportedOn (Set.Iic i) (p a) := by
    intro j hj
    apply zeroExtension_off
    rintro ⟨l,rfl⟩
    apply hj
    apply Set.mem_Iic.mpr
    apply (Ordinal.ToType.mk.symm.le_iff_le).mp
    change (initialCoordinate hm.le l).toOrd.val ≤ (cardinalStage hm).toOrd.val
    rw [initialCoordinate_ordinal,cardinalStage_rank]
    exact l.toOrd.property.le
  refine ⟨⨆ a, condition (q a),?_⟩
  rw [map_iSup,← hA,map_iSup]
  exact iSup_congr fun a => (fullClosedHom_condition i (p a) (support a)).trans (initialCollapseHom_condition hm.le a.val).symm

/-- The cardinal initial stage really is a complete subalgebra of the larger
stage including its terminal coordinate, with the same embedding into the full algebra. -/
theorem exists_initial_to_closed {μ : Cardinal.{u}} (hm : μ < θ) :
    ∃ k : CompleteLatticeHom (Completion (BelowCondition μ)) (ClosedStage (cardinalStage hm)),
      Function.Injective k ∧ ∀ x, fullClosedHom _ (k x) = initialCollapseHom hm.le x := by
  choose f hf using initial_in_closed hm
  let F := fullClosedHom (cardinalStage hm)
  let g := initialCollapseHom hm.le
  have rep (x) : F (f x) = g x := hf x
  have map (S : Set (Completion (BelowCondition μ))) : F '' (f '' S) = g '' S := by
    rw [Set.image_image]
    exact Set.image_congr' rep
  have sup (S) : f (sSup S) = sSup (f '' S) := by
    apply fullClosedHom_injective (cardinalStage hm)
    change F (f (sSup S)) = F (sSup (f '' S))
    rw [rep,map_sSup,map_sSup,map]
  have inf (S) : f (sInf S) = sInf (f '' S) := by
    apply fullClosedHom_injective (cardinalStage hm)
    change F (f (sInf S)) = F (sInf (f '' S))
    rw [rep,map_sInf,map_sInf,map]
  let k : CompleteLatticeHom (Completion (BelowCondition μ)) (ClosedStage (cardinalStage hm)) :=
    {toFun := f, map_sSup' := sup, map_sInf' := inf}
  exact ⟨k,fun x y he => initialCollapseHom_injective hm.le ((hf x).symm.trans ((congrArg F he).trans (hf y))),hf⟩

/-- Any coherent family of complete embeddings on the terminal-coordinate
stages gives an embedding of the full Lévy collapse. -/
theorem exists_closed_union_embedding {E : Type u} [CompleteBooleanAlgebra E] (hθ : θ.IsInaccessible)
    (k : ∀ i : θ.ord.ToType, CompleteLatticeHom (ClosedStage i) E) (kin : ∀ i, Function.Injective (k i))
    (coh : ∀ {i j} (h : i ≤ j) (x : ClosedStage i), k j (closedHom h x) = k i x) :
    ∃ K : CompleteLatticeHom (Completion (BelowCondition θ)) E,
      Function.Injective K ∧ ∀ (i : θ.ord.ToType) (x : ClosedStage i), K (fullClosedHom i x) = k i x := by
  have common {i j : θ.ord.ToType} (x : ClosedStage i) (y : ClosedStage j) (he : fullClosedHom i x = fullClosedHom j y) :
      k i x = k j y := by
    let m := max i j
    have a : i ≤ m := le_max_left _ _
    have d : j ≤ m := le_max_right _ _
    have eq := fullClosedHom_injective m ((fullClosedHom_commute a x).trans (he.trans (fullClosedHom_commute d y).symm))
    exact (coh a x).symm.trans ((congrArg (k m) eq).trans (coh d y))
  choose h hin hval using fun μ (hm : μ < θ) => exists_initial_to_closed hm
  let u (μ : Cardinal.{u}) (hm : μ < θ) := (k (cardinalStage hm)).comp (h μ hm)
  have agrees : AgreeOnOverlap u :=
    fun μ ν hm hn x y he => common _ _ ((hval μ hm x).trans (he.trans (hval ν hn y).symm))
  obtain ⟨K,hn,hK,_⟩ := exists_limit_embedding hθ u agrees (fun μ hm => (kin _).comp (hin μ hm))
  refine ⟨K,hn,?_⟩
  intro i x
  obtain ⟨μ,hm,_,v,hv⟩ := exists_initial_reading hθ (J := ULift.{u} Unit)
    (Cardinal.mk_lt_aleph0.trans hθ.aleph0_lt) (fun _ => fullClosedHom i x) hθ.aleph0_lt
  let z := v ⟨()⟩
  have read : initialCollapseHom hm.le z = fullClosedHom i x := hv _
  exact (congrArg K read.symm).trans ((hK μ hm z).trans (common _ _ ((hval μ hm z).trans read)))

end Erdos1172LevyCollapse.Matching
