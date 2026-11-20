/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationBoundedRepresentatives

@[expose] public section

/-! # Bounded child selections for arbitrary prepared names -/

set_option autoImplicit false
noncomputable section
open Filter bSet Erdos1172GroundUltrapower Erdos1172Shioya.UltrapowerStage
open Erdos1172LevyCohen Erdos1172BooleanUltrapower
open scoped Flypitch
universe u v w z
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)

def Supported {V : Type v} (f : I → V) : Prop :=
  ∃ η : θ.ord.ToType, ∃ g : Set θ.ord.ToType → V, (fun i => g (boundedFiber θ a η i)) =ᶠ[U] f

namespace Supported
variable {U a} {V : Type v} {W : Type w} {Z : Type z}

theorem const [Nonempty θ.ord.ToType] (c : V) : Supported U a (fun _ => c) :=
  ⟨Classical.choice inferInstance, fun _ => c, EventuallyEq.rfl⟩

theorem congr {f g : I → V} (hf : Supported U a f) (he : f =ᶠ[U] g) : Supported U a g :=
  let ⟨η,h,hh⟩ := hf
  ⟨η,h,hh.trans he⟩

theorem map {f : I → V} (hf : Supported U a f) (g : V → W) : Supported U a (fun i => g (f i)) :=
  let ⟨η,h,hh⟩ := hf
  ⟨η,fun S => g (h S), hh.mono fun _ hi => congrArg g hi⟩

theorem combine {f : I → V} {g : I → W} (hf : Supported U a f) (hg : Supported U a g)
    (op : V → W → Z) : Supported U a (fun i => op (f i) (g i)) := by
  obtain ⟨η,F,hF⟩ := hf
  obtain ⟨ν,G,hG⟩ := hg
  refine ⟨max η ν,fun S => op (F (S ∩ Set.Iio η)) (G (S ∩ Set.Iio ν)),?_⟩
  filter_upwards [hF,hG] with i hi hj
  rw [boundedFiber_restrict θ a (le_max_left η ν), boundedFiber_restrict θ a (le_max_right η ν),hi,hj]

end Supported

variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "T" => Erdos1172BooleanUltrapower.Algebra U A

def badChild (x : bSet A) (P : bSet A → A) (b : A) : Prop :=
  ∃ k : x.type, Not (x.bval k ⊓ P (x.func k) ≤ b)

abbrev BoundedChildren (X : I → bSet A) := {t : Children U X // Supported U a (child U X t)}

variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] (hκ : κ.IsInaccessible)

include hk hf hn ht hκ in
theorem exists_supported_value (c : T) : ∃ f : I → A, Supported U a f ∧ value U f = c := by
  let φ := collapseCompletionIso U a hk hf hn ht
  obtain ⟨t,he⟩ := exists_bounded_coefficient U a hk hf hn ht hκ (φ c)
  obtain ⟨η,F,hF⟩ := t.property
  exact ⟨repr U a t,⟨η,F,Germ.coe_eq.mp (hF.trans (repr_eq U a t).symm)⟩,φ.injective he⟩

include hk hf hn ht hκ in
/-- For bounded parameters the Skolem choice separating a proposed upper
bound from the existential truth value depends on one bounded fiber. -/
theorem bounded_child_exists (X : I → bSet A) (P : I → bSet A → A)
    (hX : Supported U a X) (hP : Supported U a P) :
    value U (fun i => ⨆ k, (X i).bval k ⊓ P i ((X i).func k)) =
      ⨆ t : BoundedChildren U a X,
        value U (weight U X t.val) ⊓ value U (fun i => P i (child U X t.val i)) := by
  classical
  let C (t : Children U X) := value U (weight U X t) ⊓ value U (fun i => P i (child U X t i))
  let v := ⨆ t : BoundedChildren U a X, C t.val
  obtain ⟨d,hd,he⟩ := exists_supported_value U a hk hf hn ht hκ v
  apply le_antisymm
  · change _ ≤ v
    rw [← he, value_le_value_iff]
    by_contra no
    have bad : ∀ᶠ i in U, badChild (X i) (P i) (d i) := (U.eventually_not.mpr no).mono fun i hi => by
      by_contra all
      exact hi (iSup_le fun k => by_contra fun nk => all ⟨k,nk⟩)
    let t : Children U X := ⟨{i | badChild (X i) (P i) (d i)},bad,fun i => i.property.choose⟩
    let pick (x : bSet A) (p : bSet A → A) (b : A) := if h : badChild x p b then x.func h.choose else ∅
    have sel : Supported U a (child U X t) := by
      apply ((hX.combine hP (fun x p => (x,p))).combine hd (fun z b => pick z.1 z.2 b)).congr
      filter_upwards [bad] with i hi
      simp only [pick,dif_pos hi,child,t,Set.mem_ofPred_eq]
    have leq : C t ≤ value U d := (le_iSup (fun s : BoundedChildren U a X => C s.val) ⟨t,sel⟩).trans_eq he.symm
    rw [show C t = value U (fun i => weight U X t i ⊓ P i (child U X t i)) from (value_inf U _ _).symm] at leq
    obtain ⟨i,hi,hle⟩ := (bad.and ((value_le_value_iff U).mp leq)).exists
    apply hi.choose_spec
    change weight U X t i ⊓ P i (child U X t i) ≤ d i at hle
    simpa only [weight,selected,child,t,Set.mem_ofPred_eq,dif_pos hi] using hle
  · exact (iSup_le fun t : BoundedChildren U a X => le_iSup C t.val).trans_eq (value_bounded_exists U X P).symm

include hk hf hn ht hκ in
theorem bounded_child_forall (X : I → bSet A) (P : I → bSet A → A)
    (hX : Supported U a X) (hP : Supported U a P) :
    value U (fun i => ⨅ k, (X i).bval k ⟹ P i ((X i).func k)) =
      ⨅ t : BoundedChildren U a X,
        value U (weight U X t.val) ⟹ value U (fun i => P i (child U X t.val i)) := by
  apply compl_injective
  rw [← value_compl]
  simp only [compl_iInf, _root_.imp, compl_sup, compl_compl]
  exact (bounded_child_exists U a hk hf hn ht hκ X (fun i y => (P i y)ᶜ) hX (hP.map (fun p y => (p y)ᶜ))).trans
    (iSup_congr fun t => congrArg (_ ⊓ ·) (value_compl U (fun i => P i (child U X t.val i))))

end Erdos1172LevyCollapse.Preparation
