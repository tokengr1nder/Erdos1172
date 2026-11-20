/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingCohenGraphReading
public import Erdos1172.Part4LevyMatchingCommonPreparation
public import Erdos1172.Part4BooleanQuotientDenseSets

@[expose] public section

/-! # Source Cohen conditions meeting upper dense tests after matching -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal bSet Lattice ErdosNameTransport ErdosOmegaTwo Erdos1172LevyCohen
open Erdos1172BooleanQuotient Erdos1172BooleanUltrapower
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching
variable {κ θ : Cardinal.{u}} {R E : Type u}
    [NontrivialCompleteBooleanAlgebra R] [NontrivialCompleteBooleanAlgebra E]
local notation "Z" => FirstAlgebra θ
local notation "Coh" => ErdosCohen.condition omegaOne
local notation "Pos" => ErdosCohen.conditions omegaOne

variable (g : CompleteLatticeHom R E) (K : CompleteLatticeHom (FirstAlgebra θ) E)

/-- Every member of a named dense test used as a witness below an arbitrary
upper Cohen condition can be realized by a genuine Cohen condition from the
source on a Boolean cover. The test itself may have arbitrarily many names. -/
theorem upper_cohen_dense_extension
    (read : ∀ q : bSet Z, K (Coh q) ≤ ⨆ y : bSet R, g (Coh y) ⊓ (mapNames K q =ᴮ mapNames g y))
    (D q : bSet Z) :
    K ((Coh q) ⊓ denseValue Pos (fun x => x ∈ᴮ D)) ≤ ⨆ y : bSet R,
      g (Coh y) ⊓ ((mapNames g y ∈ᴮ mapNames K D) ⊓ (mapNames K q ⊆ᴮ mapNames g y)) := by
  let d := (Coh q) ⊓ denseValue (Pos : bSet Z) (fun x => x ∈ᴮ D)
  let s (x : bSet Z) := (x ∈ᴮ Pos) ⊓ ((q ⊆ᴮ x) ⊓ (x ∈ᴮ D))
  have dense : d ≤ ⨆ x : bSet Z, s x := (le_inf (inf_le_right.trans (iInf_le _ q))
    (ErdosCohen.mem_conditions_iff.mpr inf_le_left)).trans bv_imp_elim
  apply ((OrderHomClass.mono K dense).trans_eq (map_iSup K _)).trans
  apply iSup_le
  intro x
  have valid : K (s x) ≤ K (Coh x) := OrderHomClass.mono K (ErdosCohen.mem_conditions_iff.mp inf_le_left)
  have cover := valid.trans (read x)
  apply ((inf_eq_left.mpr cover).symm.trans (inf_iSup_eq _ _)).le.trans (iSup_le fun y => ?_)
  let p := K (s x) ⊓ (g (Coh y) ⊓ (mapNames K x =ᴮ mapNames g y))
  have eq : p ≤ mapNames K x =ᴮ mapNames g y := inf_le_right.trans inf_le_right
  have hit : p ≤ mapNames K x ∈ᴮ mapNames K D :=
    inf_le_left.trans ((OrderHomClass.mono K (show s x ≤ x ∈ᴮ D from inf_le_right.trans inf_le_right)).trans_eq (map_mem K _ _))
  have ext : p ≤ mapNames K q ⊆ᴮ mapNames K x :=
    inf_le_left.trans ((OrderHomClass.mono K (show s x ≤ q ⊆ᴮ x from inf_le_right.trans inf_le_left)).trans_eq (map_subset K _ _))
  exact le_iSup_of_le y (le_inf (inf_le_right.trans inf_le_left)
    (le_inf (mem_congr eq bv_refl hit) (subset_trans' ext (subset_of_eq eq))))

variable {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
    (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
    (gStage : ∀ i, CompleteLatticeHom (B i) R)
local notation "J" => JointForcing R θ.ord.ToType
local notation "src" => jointSourceHom (R := R) θ.ord.ToType

/-- One embedding over the prescribed common preparation works for all
upper mixed Cohen conditions and every named dense test. -/
theorem exists_matching_over_preparation_with_cohen_tests (hk : κ < θ)
    (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) (cc : StrictCC R θ)
    (dense : DenseStageUnion gStage) (good : RegularCollapsingStages B)
    (ginj : ∀ i, Function.Injective (gStage i))
    (gg : ∀ {i j : θ.ord.ToType} (h : i ≤ j) x, gStage j (b h x) = gStage i x)
    (u : CompleteLatticeHom (FirstAlgebra κ) R) (ui : Function.Injective u) :
    ∃ K : CompleteLatticeHom Z J, Function.Injective K ∧
      (∀ a, K (initialCollapseHom hk.le a) = src (u a)) ∧
      (∀ q : bSet Z, K (Coh q) ≤ ⨆ y : bSet R, src (Coh y) ⊓ (mapNames K q =ᴮ mapNames (src) y)) ∧
      ∀ D q : bSet Z, K ((Coh q) ⊓ denseValue Pos (fun x => x ∈ᴮ D)) ≤ ⨆ y : bSet R,
        src (Coh y) ⊓ ((mapNames (src) y ∈ᴮ mapNames K D) ⊓ (mapNames K q ⊆ᴮ mapNames (src) y)) := by
  obtain ⟨K,inj,over,_,back⟩ := exists_levy_matching_over_preparation b gStage hk hκ hθ cc dense good ginj gg u ui
  have read := upper_cohen_graph_reading (src) K back (source_bounded_ordinal_mem_omegaOne gStage good) hθ
  exact ⟨K,inj,over,read,upper_cohen_dense_extension (src) K read⟩

end Erdos1172LevyCollapse.Matching
