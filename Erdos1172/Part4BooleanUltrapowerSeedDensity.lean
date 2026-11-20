/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerCriticalIdeal

@[expose] public section

/-! # Dense critical-seed values of weighted subsets

A ground family of Boolean coefficients gives a subset name of the checked
critical ordinal. In the target algebra, membership of the critical seed
in its lift has precisely the given germ as its value. The regular
completion therefore has a dense family of such membership values.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower Erdos1172PosetCompletion Erdos1172PositiveBoolean
open Erdos1172LevyCohen Erdos1172BooleanFactor bSet.ErdosIdeal bSet.ErdosSeedKernel bSet.ErdosOmegaTwo
open scoped Flypitch

universe u v

namespace Erdos1172BooleanUltrapower

section Density

variable {I : Type u} {B : Type v} [BooleanAlgebra B] (U : Ultrafilter I)

theorem germValue_positive (p : Positive (Germ (U : Filter I) B)) :
    germValue U p.val = condition p := by
  apply Heyting.Regular.coe_injective
  have hcone : LowerSet.Iic p = (germValue U p.val).val := by
    apply SetLike.ext
    intro q
    rfl
  change (germValue U p.val).val = (LowerSet.Iic p)ᶜᶜ
  rw [hcone, (germValue U p.val).prop.eq]

theorem exists_positive_value_le {d : Algebra U B} (hd : d ≠ ⊥) :
    ∃ f : I → B, value U f ≠ ⊥ ∧ value U f ≤ d := by
  obtain ⟨q, hq⟩ := exists_condition_le hd
  obtain ⟨f, hf⟩ : ∃ f : I → B, Germ.ofFun f = q.val :=
    Germ.inductionOn q.val fun f => ⟨f, rfl⟩
  have he : value U f = condition q :=
    (congrArg (germValue U) hf).trans (germValue_positive U q)
  exact ⟨f, he ▸ condition_ne_bot q, he.le.trans hq⟩

end Density

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B] (κ : Cardinal.{u})

def criticalSeedCode (f : κ.ord.ToType → B) : bSet B :=
  .mk κ.ord.ToType (fun i => check (PSet.ordinalMk i.toOrd.val)) f

theorem criticalSeedCode_subset (f : κ.ord.ToType → B) :
    (⊤ : B) ≤ criticalSeedCode κ f ⊆ᴮ check (PSet.ordinalMk κ.ord) := by
  rw [subset_unfold]
  apply le_iInf
  intro i
  change (⊤ : B) ≤ _root_.imp (f i)
    (check (PSet.ordinalMk i.toOrd.val) ∈ᴮ check (PSet.ordinalMk κ.ord))
  rw [← deduction]
  exact le_top.trans (check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property))

theorem criticalSeedCode_mem (f : κ.ord.ToType → B) (i : κ.ord.ToType) :
    ((check (PSet.ordinalMk i.toOrd.val) : bSet B) ∈ᴮ criticalSeedCode κ f) = f i := by
  classical
  rw [mem_unfold]
  change (⨆ j : κ.ord.ToType, f j ⊓
    ((check (PSet.ordinalMk i.toOrd.val) : bSet B) =ᴮ check (PSet.ordinalMk j.toOrd.val))) = _
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hij : i = j
    · subst j
      exact inf_le_left
    · have hne : ¬ PSet.Equiv (PSet.ordinalMk i.toOrd.val) (PSet.ordinalMk j.toOrd.val) :=
        fun he => hij (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv he)))
      rw [check_bv_eq_bot_of_not_equiv hne, inf_bot_eq]
      exact bot_le
  · apply le_iSup_of_le i
    rw [bv_eq_refl, inf_top_eq]

variable (U : Ultrafilter κ.ord.ToType)

section CountablyComplete

variable [CountableInterFilter (U : Filter κ.ord.ToType)]
variable (hN : NormalRegressive κ U) (hT : ContainsStrictTails κ U)

include hN hT in
theorem criticalSeed_trace (X : bSet B) :
    ((check (PSet.ordinalMk κ.ord) : bSet (Algebra U B)) ∈ᴮ
      hereditary U (fun _ => X)) =
      value U (fun i : κ.ord.ToType => check (PSet.ordinalMk i.toOrd.val) ∈ᴮ X) := by
  let ord (i : κ.ord.ToType) := PSet.ordinalMk i.toOrd.val
  have hseed : (⊤ : Algebra U B) ≤ hereditary U (fun i => check (ord i) : _ → bSet B)
      =ᴮ check (PSet.ordinalMk κ.ord) :=
    bv_trans (liftName_checked U ord) (check_bv_eq (groundPSet_seed_equiv κ U hN hT))
  calc
    _ = hereditary U (fun i => check (ord i) : _ → bSet B) ∈ᴮ hereditary U (fun _ => X) :=
      bv_rw (top_unique hseed) (fun y => y ∈ᴮ hereditary U (fun _ => X)) (h_congr := B_ext_mem_left)
    _ = value U (fun i => check (ord i) ∈ᴮ X) := (value_name_mem U _ _).symm

include hN hT in
theorem criticalSeedCode_trace (f : κ.ord.ToType → B) :
    ((check (PSet.ordinalMk κ.ord) : bSet (Algebra U B)) ∈ᴮ
      hereditary U (fun _ => criticalSeedCode κ f)) = value U f :=
  (criticalSeed_trace κ U hN hT (criticalSeedCode κ f)).trans
    (value_eq_of_eventuallyEq U (Eventually.of_forall (criticalSeedCode_mem κ f)))

include hN hT in
theorem exists_criticalSeed_trace_iff {d : Algebra U B} :
    (∃ X : bSet B, (⊤ : B) ≤ X ⊆ᴮ check (PSet.ordinalMk κ.ord) ∧
      ((check (PSet.ordinalMk κ.ord) : bSet (Algebra U B)) ∈ᴮ hereditary U (fun _ => X)) = d) ↔
      ∃ f : κ.ord.ToType → B, value U f = d := by
  constructor
  · rintro ⟨X, _, hX⟩
    exact ⟨_, (criticalSeed_trace κ U hN hT X).symm.trans hX⟩
  · rintro ⟨f, hf⟩
    exact ⟨criticalSeedCode κ f, criticalSeedCode_subset κ f, (criticalSeedCode_trace κ U hN hT f).trans hf⟩

include hN hT in
theorem exists_positive_criticalSeedCode_below {d : Algebra U B} (hd : d ≠ ⊥) :
    ∃ f : κ.ord.ToType → B,
      let t := (check (PSet.ordinalMk κ.ord) : bSet (Algebra U B)) ∈ᴮ
        hereditary U (fun _ => criticalSeedCode κ f)
      t ≠ ⊥ ∧ t ≤ d := by
  obtain ⟨f, hf, hfd⟩ := exists_positive_value_le U hd
  exact ⟨f, by simpa only [criticalSeedCode_trace κ U hN hT f] using And.intro hf hfd⟩

end CountablyComplete

section Collapse

variable [CardinalInterFilter (U : Filter κ.ord.ToType) κ]
variable (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ)

include hκ hunc in
theorem firstCollapse_criticalSeedCode_subset (f : κ.ord.ToType → FirstAlgebra κ) :
    (⊤ : FirstAlgebra κ) ≤ criticalSeedCode κ f ⊆ᴮ omegaOne :=
  subset_trans' (criticalSeedCode_subset κ f)
    (subset_of_eq (Erdos1172LevyCollapse.below_checked_upper_eq_omegaOne κ hκ hunc))

theorem firstCollapse_criticalSeedCode_positive (hN : NormalRegressive κ U)
    (hT : ContainsStrictTails κ U) (f : κ.ord.ToType → FirstAlgebra κ) :
    positive omegaOne (firstCollapseCriticalIdeal κ U hκ hunc) (criticalSeedCode κ f) =
      lowerProjection (firstCollapseConstantHom U κ hκ hunc) (value U f) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  unfold firstCollapseCriticalIdeal
  rw [positive_seedKernelName _ _ _ (fun x y => (firstCollapseLift_eq κ U hκ hunc x y).le),
    top_unique (firstCollapse_criticalSeedCode_subset κ hκ hunc f), top_inf_eq]
  exact congrArg _ (criticalSeedCode_trace κ U hN hT f)

theorem firstCollapse_criticalSeedCode_loss_iff (hN : NormalRegressive κ U)
    (hT : ContainsStrictTails κ U) (f : κ.ord.ToType → FirstAlgebra κ)
    (X : bSet (FirstAlgebra κ)) (Γ : FirstAlgebra κ) :
    Γ ≤ difference (criticalSeedCode κ f) X ∈ᴮ firstCollapseCriticalIdeal κ U hκ hunc ↔
      firstCollapseConstantHom U κ hκ hunc Γ ⊓ value U f ≤
        value U (fun i : κ.ord.ToType => check (PSet.ordinalMk i.toOrd.val) ∈ᴮ X) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  have hsub : Γ ≤ difference (criticalSeedCode κ f) X ⊆ᴮ omegaOne :=
    subset_trans' difference_subset (le_top.trans (firstCollapse_criticalSeedCode_subset κ hκ hunc f))
  unfold firstCollapseCriticalIdeal
  rw [mem_seedKernelName_iff _ _ _ (fun x y => (firstCollapseLift_eq κ U hκ hunc x y).le),
    and_iff_right hsub]
  change _ ⊓ (_ ∈ᴮ hereditary U (fun _ => difference (criticalSeedCode κ f) X)) = ⊥ ↔ _
  rw [criticalSeed_trace κ U hN hT]
  simp only [mem_difference, criticalSeedCode_mem, value_inf, value_compl]
  have hbool {T : Type u} [BooleanAlgebra T] (a b c : T) :
      a ⊓ (b ⊓ cᶜ) = ⊥ ↔ a ⊓ b ≤ c := by
    rw [← inf_assoc, ← disjoint_iff, disjoint_compl_right_iff]
  exact hbool _ _ _

theorem firstCollapse_criticalSeedCodes_dense (hN : NormalRegressive κ U)
    (hT : ContainsStrictTails κ U) (X : bSet (FirstAlgebra κ)) :
    positive omegaOne (firstCollapseCriticalIdeal κ U hκ hunc) X ≤
      ⨆ f : κ.ord.ToType → FirstAlgebra κ,
        positive omegaOne (firstCollapseCriticalIdeal κ U hκ hunc) (criticalSeedCode κ f) ⊓
        (difference (criticalSeedCode κ f) X ∈ᴮ firstCollapseCriticalIdeal κ U hκ hunc) := by
  let := CardinalInterFilter.toCountableInterFilter (U : Filter κ.ord.ToType) hunc
  let f (i : κ.ord.ToType) := check (PSet.ordinalMk i.toOrd.val) ∈ᴮ X
  apply le_iSup_of_le f
  apply le_inf
  · rw [firstCollapse_criticalSeedCode_positive κ U hκ hunc hN hT]
    unfold firstCollapseCriticalIdeal
    rw [positive_seedKernelName _ _ _ (fun x y => (firstCollapseLift_eq κ U hκ hunc x y).le)]
    exact inf_le_right.trans_eq (congrArg _ (criticalSeed_trace κ U hN hT X))
  · exact (firstCollapse_criticalSeedCode_loss_iff κ U hκ hunc hN hT f X _).mpr inf_le_right

end Collapse

end Erdos1172BooleanUltrapower
