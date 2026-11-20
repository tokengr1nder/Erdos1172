/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingTowerReading

@[expose] public section

/-! # Equality of the two transported sets of reals in the joint forcing -/

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
universe u
open Cardinal Erdos1172PosetCompletion Erdos1172BooleanUltrapower
open bSet bSet.ErdosNameTransport Erdos1172CohenIteration Lattice
open scoped Flypitch Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching

private theorem mapped_real_mem {V E : Type u} [NontrivialCompleteBooleanAlgebra V] [NontrivialCompleteBooleanAlgebra E]
    (e : CompleteLatticeHom V E) (v : ℕ → V) :
    (⊤ : E) ≤ mapNames e (realName v) ∈ᴮ mapNames e (bv_powerset omega) := by
  rw [← map_mem,← map_top e]
  exact OrderHomClass.mono e (mem_powerset_iff.mpr (realName_subset v))

private theorem mapped_powerset_subset {V E : Type u} [NontrivialCompleteBooleanAlgebra V] [NontrivialCompleteBooleanAlgebra E]
    (e : CompleteLatticeHom V E) (Z : bSet E) (mem : ∀ x : bSet V, e (x ⊆ᴮ omega) ≤ mapNames e x ∈ᴮ Z) :
    (⊤ : E) ≤ mapNames e (bv_powerset omega) ⊆ᴮ Z := by
  rw [subset_unfold]
  change (⊤ : E) ≤ ⨅ f : (omega : bSet V).type → V,
    _root_.imp (e (set_of_indicator (u := omega) f ⊆ᴮ omega)) (mapNames e (set_of_indicator (u := omega) f) ∈ᴮ Z)
  apply le_iInf
  intro f
  rw [← deduction]
  exact inf_le_right.trans (mem _)

variable {θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R]
  {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
  (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (g : ∀ i, CompleteLatticeHom (B i) R)

/-- In the source forcing times the external collapse of the stage index
there is a complete embedding of the full Lévy collapse. Its hereditary
image of the powerset of omega equals the source's hereditary image of that
powerset. The source assumptions concern its ground stages and chain condition. -/
theorem exists_levy_embedding_matching_reals
    (hθ : θ.IsInaccessible) (cc : StrictCC R θ) (dense : DenseStageUnion g)
    (good : RegularCollapsingStages B)
    (hin : ∀ i, Function.Injective (g i))
    (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x) :
    ∃ K : CompleteLatticeHom (Completion (BelowCondition θ)) (JointForcing R θ.ord.ToType),
      Function.Injective K ∧ (⊤ : JointForcing R θ.ord.ToType) ≤
        mapNames (jointSourceHom θ.ord.ToType) (bv_powerset (omega : bSet R)) =ᴮ mapNames K (bv_powerset omega) := by
  classical
  let e := jointSourceHom (R := R) θ.ord.ToType
  have bin {i j : θ.ord.ToType} (h : i ≤ j) : Function.Injective (b h) := fun x y he =>
    hin i ((gg h x).symm.trans ((congrArg (g j) he).trans (gg h y)))
  have bid (i : θ.ord.ToType) (x : B i) : b (le_refl i) x = x := hin _ (gg _ x)
  have bc {i j l : θ.ord.ToType} (h : i ≤ j) (h' : j ≤ l) (x : B i) :
      b (h.trans h') x = b h' (b h x) :=
    hin l ((gg _ _).trans ((gg _ _).symm.trans (gg h' (b h x)).symm))
  let pairs := fun i t => (exists_collapsing_pairs b bin good i t).some
  obtain ⟨s⟩ := exists_start_match hθ.aleph0_lt good
  obtain ⟨k,ki,kc,lr,rl⟩ := exists_joint_stage_embeddings b closedHom bin closedHom_injective bid closedHom_id bc
    closedHom_comp pairs s g hin gg
  obtain ⟨K,kn,Kk⟩ := exists_closed_union_embedding hθ k ki kc
  refine ⟨K,kn,subset_ext (mapped_powerset_subset e _ ?_) (mapped_powerset_subset K _ ?_)⟩
  · intro x
    obtain ⟨i,v,hv⟩ := source_real_from_stage b g gg hθ cc dense x
    have eq := OrderHomClass.mono e hv
    rw [map_bv_eq,← mapNames_comp] at eq
    apply bv_rw' eq (h_congr := B_ext_mem_left)
    apply le_top.trans
    have h := lr i (realName v)
    rw [realName_subset_value,map_top,map_top] at h
    apply h.trans (iSup_le fun j => iSup_le fun w => ?_)
    have heq : mapNames (k j) (realName w) = mapNames K (realName (fun n => fullClosedHom j (w n))) := by
      rw [map_realName,map_realName]
      exact congrArg realName (funext fun n => (Kk _ _).symm)
    rw [heq]
    apply bv_rw' le_rfl (h_congr := B_ext_mem_left)
    exact le_top.trans (mapped_real_mem K _)
  · intro x
    obtain ⟨μ,hm,_,v,hread⟩ := realName_from_initial hθ x (le_refl _) hθ.aleph0_lt
    obtain ⟨F,_,Fh⟩ := exists_initial_to_closed hm
    let i := cardinalStage hm
    let w (n : ℕ) := F (v n)
    have reads : mapNames K (mapNames (initialCollapseHom hm.le) (realName v)) = mapNames (k i) (realName w) := by
      rw [map_realName,map_realName,map_realName]
      exact congrArg realName (funext fun n => (congrArg K (Fh (v n)).symm).trans (Kk i (w n)))
    have eq := OrderHomClass.mono K hread
    rw [map_bv_eq,reads] at eq
    apply bv_rw' eq (h_congr := B_ext_mem_left)
    apply le_top.trans
    have h := rl i (realName w)
    rw [realName_subset_value,map_top] at h
    apply h.trans (iSup_le fun j => iSup_le fun z => ?_)
    rw [mapNames_comp,map_realName (g j)]
    apply bv_rw' le_rfl (h_congr := B_ext_mem_left)
    exact le_top.trans (mapped_real_mem e _)

end Erdos1172LevyCollapse.Matching
