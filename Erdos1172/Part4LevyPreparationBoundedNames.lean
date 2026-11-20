/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationBoundedSelection

@[expose] public section

/-! # The preparation lift through the bounded almost-huge ultrapower -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter bSet ErdosNameTransport Erdos1172GroundUltrapower
open Erdos1172LevyCohen Erdos1172BooleanUltrapower
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)]
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "T" => Erdos1172BooleanUltrapower.Algebra U A

/-- Only children drawn from one bounded part of the fine seed occur. -/
def boundedName : (I → bSet A) → bSet T :=
  (familyChild_wf U).fix fun X rec => .mk (BoundedChildren U a X)
    (fun t => rec (child U X t.val) (child_lt U X t.val)) (fun t => value U (weight U X t.val))

theorem boundedName_unfold (X : I → bSet A) :
    boundedName U a X = .mk (BoundedChildren U a X)
      (fun t => boundedName U a (child U X t.val)) (fun t => value U (weight U X t.val)) :=
  WellFounded.fix_eq _ _ _

variable [Nonempty θ.ord.ToType] (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
variable (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
local notation "liftF" => boundedName (κ := κ) U a
local notation "φ" => collapseCompletionIso U a hk hf hn ht
local notation "hom" => ((φ) : CompleteLatticeHom T B)

def half {D : Type u} [NontrivialCompleteBooleanAlgebra D]
    (x y : bSet D) (r : bSet D → bSet D → D) : D :=
  ⨅ k, x.bval k ⟹ ⨆ l, y.bval l ⊓ r (x.func k) (y.func l)

private theorem eq_halves {D : Type u} [NontrivialCompleteBooleanAlgebra D] (x y : bSet D) :
    (x =ᴮ y) = half x y bv_eq ⊓ half y x (fun w v => v =ᴮ w) := by cases x; cases y; rfl

include hk hf hn ht hκ in
private theorem bounded_half (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y)
    (r : bSet A → bSet A → A) :
    value U (fun i => half (X i) (Y i) r) =
      ⨅ t : BoundedChildren U a X, value U (weight U X t.val) ⟹
        ⨆ s : BoundedChildren U a Y, value U (weight U Y s.val) ⊓
          value U (fun i => r (child U X t.val i) (child U Y s.val i)) := by
  unfold half
  let P (y : bSet A) (v : bSet A) := ⨆ l, y.bval l ⊓ r v (y.func l)
  apply (bounded_child_forall U a hk hf hn ht hκ X (fun i => P (Y i)) hX (hY.map P)).trans
  apply iInf_congr
  intro t
  exact congrArg (imp _) (bounded_child_exists U a hk hf hn ht hκ Y (fun i => r (child U X t.val i)) hY (t.property.map r))

omit [Nonempty θ.ord.ToType] in
private theorem lifted_half (X Y : I → bSet A) (r : bSet T → bSet T → T) :
    half (liftF X) (liftF Y) r =
      ⨅ t : BoundedChildren U a X, value U (weight U X t.val) ⟹
        ⨆ s : BoundedChildren U a Y, value U (weight U Y s.val) ⊓
          r (liftF (child U X t.val)) (liftF (child U Y s.val)) := by
  conv_lhs => rw [boundedName_unfold (κ := κ) U a X,boundedName_unfold (κ := κ) U a Y]
  rfl

include hk hf hn ht hκ in
theorem boundedName_eq (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    value U (fun i => X i =ᴮ Y i) = (liftF X =ᴮ liftF Y) := by
  let goal (X : I → bSet A) := ∀ Y : I → bSet A, Supported U a X → Supported U a Y →
    value U (fun i => X i =ᴮ Y i) = (liftF X =ᴮ liftF Y)
  suffices all : ∀ X, goal X from all X Y hX hY
  intro X
  apply (familyChild_wf («B» := A) U).induction X
  intro X ih
  show goal X
  intro Y hX hY
  rw [eq_halves (liftF X) (liftF Y), lifted_half (κ := κ) U a X Y, lifted_half (κ := κ) U a Y X]
  simp only [eq_halves (X _) (Y _),value_inf,bounded_half U a hk hf hn ht hκ X Y hX hY,
    bounded_half U a hk hf hn ht hκ Y X hY hX]
  apply congrArg₂ (· ⊓ ·)
  · apply iInf_congr
    intro t
    apply congrArg (imp _)
    apply iSup_congr
    intro s
    exact congrArg (_ ⊓ ·) (ih _ (child_lt U X t.val) _ t.property s.property)
  · apply iInf_congr
    intro s
    apply congrArg (imp _)
    apply iSup_congr
    intro t
    exact congrArg (_ ⊓ ·) (ih _ (child_lt U X t.val) _ t.property s.property)

include hk hf hn ht hκ in
theorem boundedName_mem (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    value U (fun i => X i ∈ᴮ Y i) = (liftF X ∈ᴮ liftF Y) := by
  simp only [mem_unfold]
  apply (bounded_child_exists U a hk hf hn ht hκ Y (fun i y => X i =ᴮ y) hY (hX.map bv_eq)).trans
  conv_rhs => rw [boundedName_unfold (κ := κ) U a Y]
  apply iSup_congr
  intro t
  exact congrArg (_ ⊓ ·) (boundedName_eq U a hk hf hn ht hκ X _ hX t.property)

include hk hf hn ht hκ in
theorem boundedName_subset (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    value U (fun i => X i ⊆ᴮ Y i) = (liftF X ⊆ᴮ liftF Y) := by
  simp only [subset_unfold]
  apply (bounded_child_forall U a hk hf hn ht hκ X (fun i x => x ∈ᴮ Y i) hX (hY.map (fun y x => x ∈ᴮ y))).trans
  conv_rhs => rw [boundedName_unfold (κ := κ) U a X]
  apply iInf_congr
  intro t
  exact congrArg (imp _) (boundedName_mem U a hk hf hn ht hκ _ Y t.property hY)

def boundedPreparedName (X : bSet A) : bSet B := mapNames hom (liftF (fun _ => X))

variable [CardinalInterFilter (U : Filter I) κ]
local notation "j" => boundedPreparedName U a hk hf hn ht

include hκ in
theorem boundedPrepared_mem (X Y : bSet A) : (j X ∈ᴮ j Y) = initialCollapseHom hk (X ∈ᴮ Y) := by
  unfold boundedPreparedName
  apply (map_mem hom _ _).symm.trans
  apply (congrArg (fun d => (φ) d) (boundedName_mem U a hk hf hn ht hκ (fun _ => X) (fun _ => Y)
    (Supported.const _) (Supported.const _)).symm).trans
  exact collapseCompletionIso_constant U a hk hf hn ht hκ.isRegular hκ.aleph0_lt _

end Erdos1172LevyCollapse.Preparation
