/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingPowerset

@[expose] public section

/-! # Extending a prescribed stage match while reading whole short arrays -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PosetCompletion Erdos1172BooleanUltrapower
open scoped Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching

/-- Above every part of the joint forcing, a single positive refinement reads
all the coefficients of the array in the indicated algebra. -/
def ArrayRead {V Z E : Type u} [CompleteBooleanAlgebra V] [CompleteBooleanAlgebra Z] [CompleteBooleanAlgebra E]
    (f : CompleteLatticeHom V E) (g : CompleteLatticeHom Z E) {J : Type u} (x : J → V) : Prop :=
  (⊤ : E) ≤ ⨆ w : {w : E × (J → Z) // ∀ i, w.1 ⊓ f (x i) = w.1 ⊓ g (w.2 i)}, w.val.1

variable {θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R]
  {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
  (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (g : ∀ i, CompleteLatticeHom (B i) R)
local notation "J" => θ.ord.ToType
local notation "E" => JointForcing R θ.ord.ToType
local notation "Z" => Completion (BelowCondition θ)
local notation "src" => jointSourceHom (R := R) θ.ord.ToType

/-- The same full embedding extends the chosen isomorphism and reads every
short coefficient array in both directions, on covers of the joint forcing. -/
theorem exists_anchored_levy_matching (hθ : θ.IsInaccessible) (cc : StrictCC R θ) (dense : DenseStageUnion g)
    (good : RegularCollapsingStages B) (ginj : ∀ i, Function.Injective (g i))
    (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x) (start : StageMatch B ClosedStage) :
    ∃ K : CompleteLatticeHom Z E, Function.Injective K ∧
      (∀ x, K (fullClosedHom start.1 (start.2 x)) = src (g start.1 x)) ∧
      (∀ (A : Type u), #A < θ → ∀ x : A → R, ArrayRead (src) K x) ∧
      (∀ (A : Type u), #A < θ → ∀ x : A → Z, ArrayRead K (src) x) := by
  classical
  have bin {i j : J} (h : i ≤ j) : Function.Injective (b h) :=
    fun x y eq => ginj i ((gg h x).symm.trans ((congrArg (g j) eq).trans (gg h y)))
  have bid (i : J) (x : B i) : b (le_refl i) x = x := ginj i (gg _ x)
  have bc {i j l : J} (h : i ≤ j) (h' : j ≤ l) (x : B i) : b (h.trans h') x = b h' (b h x) :=
    ginj l ((gg _ _).trans ((gg _ _).symm.trans (gg h' (b h x)).symm))
  let pairs := fun i t => (exists_collapsing_pairs b bin good i t).some
  obtain ⟨V,k,init,ki,kc,loc⟩ := exists_joint_stage_embeddings_from b closedHom bin closedHom_injective bid closedHom_id bc
    closedHom_comp pairs start g ginj gg
  obtain ⟨K,kn,Kk⟩ := exists_closed_union_embedding hθ k ki kc
  refine ⟨K,kn,?_,?_,?_⟩
  · intro x
    have old := loc 0 start le_rfl (start.2 x)
    rw [top_unique init,closedHom_id,OrderIso.symm_apply_apply] at old
    erw [top_inf_eq,top_inf_eq] at old
    exact (Kk _ _).trans old
  · intro A small x
    obtain ⟨i,y,hy⟩ := source_array_from_stage b g gg hθ cc dense small x
    apply (V.covers i).trans (iSup_le fun n => iSup_le fun s => ?_)
    let h := s.property
    let z (a : A) := s.val.2 (b h (y a))
    have eq (a : A) : V.weight n s.val ⊓ src (x a) = V.weight n s.val ⊓ K (fullClosedHom s.val.1 (z a)) := by
      rw [Kk,loc n s.val le_rfl,closedHom_id,show s.val.2.symm (z a) = b h (y a) from s.val.2.symm_apply_apply _,gg,hy]
    exact le_iSup_of_le ⟨(V.weight n s.val,fun a => fullClosedHom s.val.1 (z a)),eq⟩ le_rfl
  · intro A small x
    obtain ⟨μ,hm,_,v,hv⟩ := exists_initial_reading hθ small x hθ.aleph0_lt
    obtain ⟨F,_,hF⟩ := exists_initial_to_closed hm
    let i := cardinalStage hm
    have read (a : A) : K (x a) = k i (F (v a)) := (congrArg K ((hv a).symm.trans (hF _).symm)).trans (Kk i _)
    apply (V.covers i).trans (iSup_le fun n => iSup_le fun s => ?_)
    let z (a : A) := g s.val.1 (s.val.2.symm (closedHom s.property (F (v a))))
    have eq (a : A) : V.weight n s.val ⊓ K (x a) = V.weight n s.val ⊓ src (z a) := by
      rw [read]
      exact loc n s.val s.property (F (v a))
    exact le_iSup_of_le ⟨(V.weight n s.val,z),eq⟩ le_rfl

end Erdos1172LevyCollapse.Matching
