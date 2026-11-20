/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetProjectionCompletion
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

/-! # Continuous projections on closed dense domains

These definitions follow §§2–3 of Eskew and Hayut, *Dense Ideals*.
Lifting a strengthening is allowed to strengthen its image further.
The pullback of a closed dense domain is dense by an alternating
countable descent. This gives the domain for composing two projections.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya

variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- All descending sequences of ordinal length less than κ have infima.
An empty sequence asks for a greatest element. -/
def ShortInfima (κ : Cardinal.{u}) (P : Type u) [PartialOrder P] : Prop :=
  ∀ (L : Type u) [LinearOrder L] [WellFoundedLT L], Cardinal.mk L < κ →
    ∀ f : L → P, Antitone f → ∃ p, IsGLB (Set.range f) p

structure PartialProjection (κ : Cardinal.{u}) (P Q : Type u) [PartialOrder P] [PartialOrder Q] where
  dom : Set P
  dense : ∀ p : P, ∃ x : dom, x.val ≤ p
  proj : dom →o Q
  reaches : ∀ q : Q, ∃ x : dom, proj x ≤ q
  lifts : ∀ x : dom, ∀ q ≤ proj x, ∃ y : dom, y ≤ x ∧ proj y ≤ q
  closed : ∀ (L : Type u) [LinearOrder L] [WellFoundedLT L], Cardinal.mk L < κ →
    ∀ (f : L → dom), Antitone f → ∀ p, IsGLB (Set.range (fun i => (f i).val)) p → p ∈ dom
  continuous : ∀ (L : Type u) [LinearOrder L] [WellFoundedLT L], Cardinal.mk L < κ →
    ∀ (f : L → dom), Antitone f → ∀ p : dom, IsGLB (Set.range (fun i => (f i).val)) p.val →
      IsGLB (Set.range (fun i => proj (f i))) (proj p)

namespace PartialProjection

variable {κ : Cardinal.{u}}

def identity : PartialProjection κ P P where
  dom := Set.univ
  dense p := ⟨⟨p, Set.mem_univ p⟩, le_rfl⟩
  proj := ⟨Subtype.val, fun _ _ h => h⟩
  reaches p := ⟨⟨p, Set.mem_univ p⟩, le_rfl⟩
  lifts _ q h := ⟨⟨q, Set.mem_univ q⟩, h, le_rfl⟩
  closed _ _ _ _ _ _ p _ := Set.mem_univ p
  continuous _ _ _ _ _ _ _ hg := hg

variable (π : PartialProjection κ P Q) (σ : PartialProjection κ Q R)

def compDom : Set P := {p | ∃ h : p ∈ π.dom, π.proj ⟨p, h⟩ ∈ σ.dom}

def source (x : compDom π σ) : π.dom := ⟨x.val, x.property.choose⟩
def middle (x : compDom π σ) : σ.dom := ⟨π.proj (source π σ x), x.property.choose_spec⟩

private theorem ranges_glb {L : Type*} {T : Type*} [PartialOrder T] (f : L → T) (t : T) :
    IsGLB (Set.range f) t ↔ (∀ i, t ≤ f i) ∧ (∀ t', (∀ i, t' ≤ f i) → t' ≤ t) := by
  constructor
  · intro h
    exact ⟨fun i => h.1 (Set.mem_range_self i), fun t' ht => h.2 (Set.forall_mem_range.mpr ht)⟩
  · rintro ⟨h, h'⟩
    exact ⟨Set.forall_mem_range.mpr h, fun t' ht => h' t' (Set.forall_mem_range.mp ht)⟩

/-- The alternating chains interleave, so their greatest lower bounds agree. -/
theorem compDom_dense (hκ : Cardinal.aleph0 < κ) (hP : ShortInfima κ P) (p : P) :
    ∃ x : compDom π σ, x.val ≤ p := by
  classical
  choose y hy using fun x : π.dom => σ.dense (π.proj x)
  choose next hn hm using fun x : π.dom => π.lifts x (y x).val (hy x)
  obtain ⟨x₀, hx₀⟩ := π.dense p
  let x : ℕ → π.dom := fun n => next^[n] x₀
  have hstep (n : ℕ) : x (n+1) = next (x n) := Function.iterate_succ_apply' _ _ _
  have hx : Antitone x := antitone_nat_of_succ_le (fun n => (hstep n) ▸ hn (x n))
  let L := ULift.{u} ℕ
  let f (i : L) := x i.down
  let g (i : L) := y (f i)
  have hf : Antitone f := fun _ _ h => hx h
  have hg' : Antitone (fun n => y (x n)) := antitone_nat_of_succ_le (fun n =>
    show (y (x (n+1))).val ≤ (y (x n)).val from (hy _).trans ((hstep n) ▸ hm (x n)))
  have hg : Antitone g := fun _ _ h => hg' h
  have hL : Cardinal.mk L < κ := by simpa [L] using hκ
  obtain ⟨t, ht⟩ := hP L hL (fun i => (f i).val) hf
  let z : π.dom := ⟨t, π.closed L hL f hf t ht⟩
  have hz := (ranges_glb _ _).mp (π.continuous L hL f hf z ht)
  have hY : IsGLB (Set.range (fun i => (g i).val)) (π.proj z) := by
    apply (ranges_glb _ _).mpr
    constructor
    · intro i
      apply (hz.1 (ULift.up (i.down+1))).trans
      change π.proj (x (i.down+1)) ≤ (y (x i.down)).val
      rw [hstep]
      exact hm (x i.down)
    · intro q hq
      exact hz.2 q (fun i => (hq i).trans (hy (f i)))
  exact ⟨⟨t, z.property, σ.closed L hL g hg _ hY⟩, ((ranges_glb _ _).mp ht).1 (ULift.up 0) |>.trans hx₀⟩

def comp (hκ : Cardinal.aleph0 < κ) (hP : ShortInfima κ P) : PartialProjection κ P R where
  dom := compDom π σ
  dense := compDom_dense π σ hκ hP
  proj := ⟨fun x => σ.proj (middle π σ x), fun _ _ h => σ.proj.monotone (π.proj.monotone h)⟩
  reaches r := by
    obtain ⟨q, hq⟩ := σ.reaches r
    obtain ⟨p, hp⟩ := π.reaches q.val
    obtain ⟨x, hx⟩ := compDom_dense π σ hκ hP p.val
    exact ⟨x, (σ.proj.monotone (show middle π σ x ≤ q from (π.proj.monotone hx).trans hp)).trans hq⟩
  lifts x r hr := by
    obtain ⟨q, hq, hqr⟩ := σ.lifts (middle π σ x) r hr
    obtain ⟨p, hp, hpq⟩ := π.lifts (source π σ x) q.val hq
    obtain ⟨y, hy⟩ := compDom_dense π σ hκ hP p.val
    exact ⟨y, hy.trans hp, (σ.proj.monotone
      (show middle π σ y ≤ q from (π.proj.monotone hy).trans hpq)).trans hqr⟩
  closed L _ _ hL f hf p hglb := by
    let g := fun i => source π σ (f i)
    have hg : Antitone g := fun _ _ h => hf h
    have hp := π.closed L hL g hg p hglb
    exact ⟨hp, σ.closed L hL (fun i => middle π σ (f i)) (fun _ _ h => π.proj.monotone (hf h))
      _ (π.continuous L hL g hg ⟨p, hp⟩ hglb)⟩
  continuous L _ _ hL f hf p hglb :=
    σ.continuous L hL _ (fun _ _ h => π.proj.monotone (hf h)) (middle π σ p)
      (π.continuous L hL _ (fun _ _ h => hf h) (source π σ p) hglb)

end PartialProjection
end Erdos1172Shioya
