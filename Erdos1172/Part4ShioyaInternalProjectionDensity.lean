/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalProjectionLaws
public import Erdos1172.Part4ShioyaInternalOmegaInfima

@[expose] public section

/-! # Density of the pullback domain of two mixed continuous partial projections -/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosBoundedFunctionValue ErdosOmegaSequence
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

private theorem atPoint {Γ : B} {P p : N} {f : N → B} (h : Γ ≤ allIn P f) (hp : Γ ≤ p ∈ᴮ P) :
    Γ ≤ f p := (le_inf (h.trans (iInf_le _ p)) hp).trans bv_imp_elim

theorem internalOrder_trans {Γ : B} {P R a b c : N} (h : Γ ≤ partialOrderValue P R)
    (ab : Γ ≤ edge R a b) (bc : Γ ≤ edge R b c) : Γ ≤ edge R a c := by
  have hab := mem_prod_iff.mp (mem_of_mem_subset (h.trans inf_le_left) ab)
  have hbc := mem_prod_iff.mp (mem_of_mem_subset (h.trans inf_le_left) bc)
  exact (le_inf (atPoint (atPoint (atPoint (h.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    hab.1) hab.2) hbc.2) (le_inf ab bc)).trans bv_imp_elim

private theorem desc_of_steps {Γ : B} {P R : N} {v : ℕ → N} (order : Γ ≤ partialOrderValue P R)
    (step : ∀ n, Γ ≤ edge R (v (n+1)) (v n)) (m n : ℕ) (h : m < n) :
    Γ ≤ edge R (v n) (v m) := by
  induction n, h using Nat.le_induction with
  | base => exact step m
  | succ n _ ih => exact internalOrder_trans order (step n) ih

/-- The two descending sequences of mixed target values interleave. Their greatest lower
bounds agree under every further Boolean restriction, including for mixed lower bounds. -/
private theorem interleaved_glb {Γ : B} {Q S g p : N} {v w : ℕ → N}
    (order : Γ ≤ partialOrderValue Q S) (fg : Γ ≤ is_function omega Q g)
    (vals : ∀ n, Γ ≤ edge g (of_nat n) (v n)) (glb : Γ ≤ glbValue omega g Q S p)
    (hw : ∀ n, Γ ≤ w n ∈ᴮ Q) (before : ∀ n, Γ ≤ edge S (w n) (v n))
    (after : ∀ n, Γ ≤ edge S (v (n+1)) (w n)) : Γ ≤ glbValue omega (sequenceGraph w) Q S p := by
  obtain ⟨hp,lb,gr⟩ := (glb_numeral_iff fg vals).mp glb
  apply (glb_numeral_iff (sequenceGraph_is_function hw) (fun _ => sequenceGraph_pair)).mpr
  refine ⟨hp,fun n => internalOrder_trans order (lb (n+1)) (after n),?_⟩
  intro Δ t hd ht low
  exact gr Δ t hd ht (fun n => internalOrder_trans (hd.trans order) (low n) (hd.trans (before n)))

/-- Starting below an arbitrary mixed point, alternately enter the second domain and
lift along the first projection. Closure and continuity place the single limiting
source point in the actual pullback domain at the original guard. -/
theorem projection_pullback_dense {Γ : B} {K P R Q S T V D F E G : N}
    (hk : Γ ≤ omega ∈ᴮ K) (hP : Γ ≤ partialOrderValue P R) (hQ : Γ ≤ partialOrderValue Q S)
    (complete : Γ ≤ shortInfimaValue K P R) (π : Γ ≤ partialProjectionValue K P R Q S D F)
    (σ : Γ ≤ partialProjectionValue K Q S T V E G) :
    Γ ≤ projectionDense P R (projectionPullback D F E) := by
  let piL := projectionLaws_iff.mp π
  let sigL := projectionLaws_iff.mp σ
  apply projectionDense_iff.mpr
  intro Δ hΔ p hp
  let X := {s : N × N // Δ ≤ edge F s.1 s.2}
  have range (x : X) : Δ ≤ x.val.2 ∈ᴮ Q := (projection_function_bounds (hΔ.trans piL.func) x.property).2
  choose target target_mem target_le using fun x : X => sigL.dense hΔ (range x)
  choose nextP nextQ next_pair next_src next_tgt using fun x : X => piL.lifts hΔ x.property
    (mem_of_mem_subset (hΔ.trans sigL.sub) (target_mem x)) (target_le x)
  let next (x : X) : X := ⟨(nextP x,nextQ x),next_pair x⟩
  obtain ⟨x₀,hx₀,hx₀p⟩ := piL.dense hΔ hp
  let a₀ : X := ⟨(x₀,graphValue Q F x₀),graphValue_pair_mem (hΔ.trans piL.func) hx₀⟩
  let a (n : ℕ) := next^[n] a₀
  have step (n : ℕ) : a (n+1) = next (a n) := Function.iterate_succ_apply' _ _ _
  let x (n : ℕ) := (a n).val.1
  let y (n : ℕ) := (a n).val.2
  let z (n : ℕ) := target (a n)
  have hx (n : ℕ) : Δ ≤ x n ∈ᴮ D := (projection_function_bounds (hΔ.trans piL.func) (a n).property).1
  have hxP (n : ℕ) := mem_of_mem_subset (hΔ.trans piL.sub) (hx n)
  have hz (n : ℕ) : Δ ≤ z n ∈ᴮ E := target_mem (a n)
  have hzQ (n : ℕ) := mem_of_mem_subset (hΔ.trans sigL.sub) (hz n)
  have xstep (n : ℕ) : Δ ≤ edge R (x (n+1)) (x n) := by
    change Δ ≤ edge R (a (n+1)).val.1 _
    rw [step]
    exact next_src (a n)
  have after (n : ℕ) : Δ ≤ edge S (y (n+1)) (z n) := by
    change Δ ≤ edge S (a (n+1)).val.2 _
    rw [step]
    exact next_tgt (a n)
  have desc := desc_of_steps (hΔ.trans hP) xstep
  have xdesc := sequence_descending desc
  obtain ⟨t,ht⟩ := exists_sequence_glb (hΔ.trans hk) (hΔ.trans complete) x hxP desc
  have fD := sequenceGraph_is_function hx
  have htD := piL.closed hΔ (hΔ.trans hk) fD xdesc ht
  let b := graphValue Q F t
  have hFb : Δ ≤ edge F t b := graphValue_pair_mem (hΔ.trans piL.func) htD
  obtain ⟨g,hg,seq,hbg⟩ := piL.continuous hΔ (hΔ.trans hk) fD xdesc ht hFb
  have vals (n : ℕ) : Δ ≤ edge g (of_nat n) (y n) := by
    let u := graphValue Q g (of_nat n)
    have hu : Δ ≤ edge g (of_nat n) u := graphValue_pair_mem hg of_nat_mem_omega
    have hFu : Δ ≤ edge F (x n) u := projectionSequence_apply seq sequenceGraph_pair hu
    have eq := eq_of_is_function_of_eq (hΔ.trans piL.func) bv_refl hFu (a n).property
    exact bv_rw'' eq hu B_ext_pair_mem_right
  have hbz := interleaved_glb (hΔ.trans hQ) hg vals hbg hzQ (fun n => target_le (a n)) after
  have zstep (n : ℕ) : Δ ≤ edge S (z (n+1)) (z n) :=
    internalOrder_trans (hΔ.trans hQ) (target_le (a (n+1))) (after n)
  have hbE := sigL.closed hΔ (hΔ.trans hk) (sequenceGraph_is_function hz)
    (sequence_descending (desc_of_steps (hΔ.trans hQ) zstep)) hbz
  have low := ((glb_numeral_iff (sequenceGraph_is_function hxP) (fun _ => sequenceGraph_pair)).mp ht).2.1 0
  exact ⟨t,projectionPullback_mem.mpr ⟨htD,b,hFb,hbE⟩,internalOrder_trans (hΔ.trans hP) low hx₀p⟩

end bSet.ErdosShioyaInternal
