/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingAnchoredArrays
public import Erdos1172.Part4LevyPreparationCohenMaster

@[expose] public section

/-! # Matching over a common preparatory collapse and lifting lower Cohen conditions -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172BooleanUltrapower Erdos1172LevyCohen
open bSet ErdosOmegaTwo ErdosNameTransport Erdos1172GroundUltrapower Filter
open scoped Flypitch Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching
variable {κ θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R]
  {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
  (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (g : ∀ i, CompleteLatticeHom (B i) R)
local notation "A" => FirstAlgebra κ
local notation "Z" => FirstAlgebra θ
local notation "E" => JointForcing R θ.ord.ToType
local notation "src" => jointSourceHom (R := R) θ.ord.ToType

private theorem liftHom {P Q R' : Type u} [CompleteLattice P] [CompleteLattice Q] [CompleteLattice R']
    (p : CompleteLatticeHom P R') (q : CompleteLatticeHom Q R') (qi : Function.Injective q)
    (f : P → Q) (eq : ∀ a, q (f a) = p a) : ∃ F : CompleteLatticeHom P Q, ∀ a, q (F a) = p a := by
  have im (S : Set P) : q '' (f '' S) = p '' S := by
    rw [Set.image_image]
    exact Set.image_congr' eq
  refine ⟨{ toFun := f, map_sSup' := fun S => qi ?_, map_sInf' := fun S => qi ?_ },eq⟩
  · change q (f (sInf S)) = q (sInf (f '' S))
    rw [eq,map_sInf,map_sInf,im]
  · change q (f (sSup S)) = q (sSup (f '' S))
    rw [eq,map_sSup,map_sSup,im]

/-- A supplied complete embedding of the lower collapse is preserved
everywhere. Its entire Boolean algebra fits in one source stage. -/
theorem exists_levy_matching_over_preparation (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (cc : StrictCC R θ) (dense : DenseStageUnion g) (good : RegularCollapsingStages B)
    (ginj : ∀ i, Function.Injective (g i)) (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x)
    (u : CompleteLatticeHom A R) (uinj : Function.Injective u) :
    ∃ K : CompleteLatticeHom Z E, Function.Injective K ∧ (∀ x, K (initialCollapseHom hk.le x) = src (u x)) ∧
      (∀ (X : Type u), #X < θ → ∀ x : X → R, ArrayRead (src) K x) ∧
      (∀ (X : Type u), #X < θ → ∀ x : X → Z, ArrayRead K (src) x) := by
  have size := below_completion_cardinal_le κ hκ
  obtain ⟨i,f,agree⟩ := source_array_from_stage b g gg hθ cc dense (size.trans_lt hk) u
  obtain ⟨p,comp⟩ := liftHom u (g i) (ginj i) f agree
  let ξ := max κ i.toOrd.val.card
  obtain ⟨μ,hm,big,unc,reg,⟨d,hd⟩,collapsed⟩ := good ξ (max_lt hk (Cardinal.lt_ord.mp i.toOrd.property))
  let s := cardinalStage hm
  have km : κ < μ := (le_max_left _ _).trans_lt big
  have before : i ≤ s := by
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    change i.toOrd.val ≤ (cardinalStage hm).toOrd.val
    rw [cardinalStage_rank]
    exact (Cardinal.lt_ord.mpr ((le_max_right _ _).trans_lt big)).le
  let old := (b before).comp p
  have oldeq (x : A) : g s (old x) = u x := (gg before _).trans (comp _)
  have oldinj : Function.Injective old := fun x y eq => uinj ((oldeq x).symm.trans ((congrArg (g s) eq).trans (oldeq y)))
  obtain ⟨lo,linj,lc⟩ := exists_initial_to_closed hk
  have kle : cardinalStage hk ≤ s := by
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    change (cardinalStage hk).toOrd.val ≤ (cardinalStage hm).toOrd.val
    rw [cardinalStage_rank,cardinalStage_rank]
    exact (Cardinal.ord_lt_ord.mpr km).le
  let other := (closedHom kle).comp lo
  have othereq (x : A) : fullClosedHom s (other x) = initialCollapseHom hk.le x :=
    (fullClosedHom_commute kle _).trans (lc x)
  obtain ⟨⟨v,hv⟩,collapse'⟩ := closedStage_matching_data _ unc.le (cardinalStage_rank hm)
  have small : #(Positive A) < μ := (Cardinal.mk_subtype_le _).trans_lt (size.trans_lt km)
  obtain ⟨ψ,commutes⟩ := exists_stage_amalgamation old oldinj other ((closedHom_injective kle).comp linj)
    μ unc reg (id : Positive A → Positive A) small (fun x => ⟨x,le_rfl⟩) d hd v hv collapsed collapse'
  obtain ⟨K,kin,anchor,forward,back⟩ := exists_anchored_levy_matching b g hθ cc dense good ginj gg ⟨s,ψ⟩
  refine ⟨K,kin,fun x => ?_,forward,back⟩
  exact (congrArg K ((othereq x).symm.trans (congrArg (fullClosedHom s) (commutes x).symm))).trans
    ((anchor (old x)).trans (congrArg (src) (oldeq x)))

end Erdos1172LevyCollapse.Matching
