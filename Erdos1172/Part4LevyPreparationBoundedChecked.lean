/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationBoundedNames

@[expose] public section

/-! # The bounded preparation lift agrees with the bounded ground embedding -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter bSet ErdosNameTransport Erdos1172GroundUltrapower
open Erdos1172LevyCohen Erdos1172BooleanUltrapower
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
variable (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "T" => Erdos1172BooleanUltrapower.Algebra U A
local notation "liftF" => boundedName (κ := κ) U a

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
private theorem supportedZF {F : I → ZFSet.{u}} (hF : Supported U a F) : BoundedSupport U θ a (Germ.ofFun F) :=
  let ⟨η,f,h⟩ := hF
  ⟨η,f,Germ.coe_eq.mpr h⟩

include hk hf hn ht hκ in
private theorem bounded_congr {X Y : I → bSet A} (hx : Supported U a X) (hy : Supported U a Y)
    (he : ∀ᶠ i in U, (X i =ᴮ Y i) = ⊤) : (⊤ : T) ≤ liftF X =ᴮ liftF Y := by
  rw [← boundedName_eq U a hk hf hn ht hκ _ _ hx hy,value_eq_of_eventuallyEq U (g := fun _ => ⊤) he,value_top]

include hk hf hn ht hκ in
theorem bounded_checked_family (v : BoundedHull U θ a) :
    ∀ (F : I → PSet.{u}), Supported U a F → Germ.ofFun (fun i => ZFSet.mk (F i)) = v.val →
      (⊤ : T) ≤ liftF (fun i => check (F i)) =ᴮ check (boundedCollapse U θ a v).out := by
  classical
  induction v using (boundedMem_wf U θ a).induction with
  | h v ih =>
    intro F hF hv
    let X (i : I) : bSet A := check (F i)
    have hx : Supported U a X := hF.map check
    apply subset_ext
    · rw [boundedName_unfold (κ := κ) U a (fun i => check (F i)),subset_unfold]
      apply le_iInf
      intro t
      rw [← deduction,top_inf_eq]
      let t' : BoundedChildren U a X := t
      let ch := child U X t'.val
      let good (x : bSet A) (P : PSet.{u}) := ∃ H : PSet.{u}, x = check H ∧ H ∈ P
      let get (x : bSet A) (P : PSet.{u}) := if h : good x P then h.choose else ∅
      let D (i : I) := get (ch i) (F i)
      have hd : Supported U a D := t'.property.combine hF get
      have ok : ∀ᶠ i in U, ch i = check (D i) ∧ D i ∈ F i := by
        filter_upwards [t'.val.large] with i hi
        have g : good (ch i) (F i) := by
          change good (child U X t'.val i) (F i)
          rw [child,dif_pos hi]
          let k := t'.val.pick ⟨i,hi⟩
          exact ⟨(F i).Func (check_cast k),check_func,PSet.func_mem _ _⟩
        simpa only [D,get,dif_pos g] using g.choose_spec
      let w : BoundedHull U θ a := ⟨Germ.ofFun (fun i => ZFSet.mk (D i)),supportedZF U a (hd.map ZFSet.mk)⟩
      have mem : boundedMem U θ a w v := by
        change memRel U _ v.val
        rw [← hv]
        exact ok.mono fun _ hi => ZFSet.mk_mem_iff.mpr hi.2
      have hc := bounded_congr U a hk hf hn ht hκ t'.property (hd.map check)
        (ok.mono fun i hi => by rw [show child U X t'.val i = check (D i) from hi.1]; exact top_unique bv_refl)
      have eq := bv_trans hc (ih w mem D hd rfl)
      have hw : (boundedCollapse U θ a w).out ∈ (boundedCollapse U θ a v).out := by
        apply PSet.mem_iff.mpr
        simpa only [ZFSet.mk_out] using (mem_boundedCollapse_iff U θ a _ _).mpr ⟨w,mem,rfl⟩
      exact subst_congr_mem_left' (bv_symm (le_top.trans eq)) (check_mem hw)
    · rw [subset_unfold]
      apply le_iInf
      intro k
      rw [← deduction,top_inf_eq]
      let x := (boundedCollapse U θ a v).out.Func (check_cast k)
      have hx' : ZFSet.mk x ∈ boundedCollapse U θ a v := by
        have h := PSet.mem_iff.mp (PSet.func_mem (boundedCollapse U θ a v).out (check_cast k))
        simpa only [ZFSet.mk_out] using h
      obtain ⟨w,hm,he⟩ := (mem_boundedCollapse_iff U θ a _ _).mp hx'
      obtain ⟨η,g,hg⟩ := w.property
      let D (i : I) := (g (boundedFiber θ a η i)).out
      have hd : Supported U a D := ⟨η,fun S => (g S).out,EventuallyEq.rfl⟩
      have hw : Germ.ofFun (fun i => ZFSet.mk (D i)) = w.val := by simpa only [D,ZFSet.mk_out] using hg
      have truth : ∀ᶠ i in U, D i ∈ F i := by
        change memRel U w.val v.val at hm
        rw [← hw,← hv] at hm
        exact hm.mono fun _ hi => ZFSet.mk_mem_iff.mp hi
      have hit : (⊤ : T) ≤ liftF (fun i => check (D i)) ∈ᴮ liftF X := by
        rw [← boundedName_mem U a hk hf hn ht hκ _ _ (hd.map check) hx]
        rw [value_eq_of_eventuallyEq U (g := fun _ => ⊤) (truth.mono fun _ hi => check_mem_iff.mp hi),value_top]
      have topEq := ih w hm D hd hw
      have groundEq : PSet.Equiv (boundedCollapse U θ a w).out x := PSet.equiv_iff_eq.mpr ((ZFSet.mk_out _).trans he)
      have eq := bv_trans topEq (check_bv_eq groundEq)
      rw [show (check (boundedCollapse U θ a v).out : bSet T).func k = check x from check_func]
      exact le_top.trans (subst_congr_mem_left' eq hit)

include hκ in
/-- The concrete actual upper-collapse image of an arbitrary checked set
is the check of its image under the bounded ordinal-support embedding. -/
theorem boundedPrepared_checked (x : PSet.{u}) : (⊤ : B) ≤ boundedPreparedName U a hk hf hn ht (check x) =ᴮ
    check (boundedCollapse U θ a (boundedConst U θ a (ZFSet.mk x))).out := by
  let φ : CompleteLatticeHom T B := collapseCompletionIso U a hk hf hn ht
  have h := OrderHomClass.mono φ (bounded_checked_family U a hk hf hn ht hκ (boundedConst U θ a (ZFSet.mk x))
    (fun _ => x) (Supported.const _) rfl)
  rw [TopHomClass.map_top φ,map_bv_eq φ,map_check] at h
  exact h

end Erdos1172LevyCollapse.Preparation
