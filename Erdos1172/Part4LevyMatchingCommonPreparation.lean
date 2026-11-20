/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingAnchoredArrays
public import Erdos1172.Part4LevyPreparationCohenMaster
public import Erdos1172.Part4LevyContinuumHypothesis

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

/-- For a source containing the lower collapse--Cohen iteration, the full
collapse embedding fixes the common collapse. Densely in the joint forcing
one actual upper Cohen condition extends every prepared lower condition
on the Boolean cone selecting it. -/
theorem exists_matching_cohen_master {I : Type u} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (cc : StrictCC R θ) (dense : DenseStageUnion g) (good : RegularCollapsingStages B)
    (ginj : ∀ i, Function.Injective (g i)) (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x)
    (u : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) R) (uinj : Function.Injective u) :
    ∃ K : CompleteLatticeHom Z E, Function.Injective K ∧
      (∀ x, K (initialCollapseHom hk.le x) = src (u (Erdos1172LevyCohen.firstStageHom κ x))) ∧
      (⊤ : E) ≤ ⨆ z : {z : E × bSet Z //
        (⊤ : Z) ≤ ErdosCohen.condition omegaOne z.2 ∧ ∀ p : Erdos1172CohenIteration.Conditions (omegaOne : bSet A),
        z.1 ⊓ src (u (condition p)) ≤ mapNames K (Preparation.preparedName U a hk.le hf hn ht
          (Erdos1172BooleanNameIteration.name p)) ⊆ᴮ mapNames K z.2}, z.val.1 := by
  let lower := Erdos1172LevyCohen.firstStageHom κ
  let l := (src).comp u
  obtain ⟨K,kin,square,forward,_⟩ := exists_levy_matching_over_preparation b g hk hκ hθ cc dense good ginj gg
    (u.comp lower) (uinj.comp (Erdos1172LevyCohen.firstStageHom_injective κ))
  refine ⟨K,kin,square,?_⟩
  let T := (PSet.ordinalMk κ.ord).Type
  let bit (i : T) := Erdos1172CohenIteration.bitValue (omegaOne : bSet A)
    (check ((PSet.ordinalMk κ.ord).Func i)) 1
  have size : #T < θ := by simpa only [T,PSet.ordinalMk_type,Cardinal.mk_ord_toType] using hk
  apply (forward T size (fun i => u (bit i))).trans (iSup_le fun z => ?_)
  obtain ⟨m,hm,onCones⟩ := Preparation.exists_joint_cohen_master U a hk hf hn ht hκ.isRegular hκ.aleph0_lt hθ.isRegular
    l K (fun x => (square x).symm) z.val.1 z.val.2 z.property
  exact le_iSup_of_le ⟨(z.val.1,m),hm,onCones⟩ le_rfl
end Erdos1172LevyCollapse.Matching
