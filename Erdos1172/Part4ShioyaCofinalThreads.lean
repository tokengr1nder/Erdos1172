/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInverseSystemDomains

@[expose] public section

/-! # Countable fusion of threads on increasing subsystems -/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172Shioya.InverseSystem

variable {κ : Cardinal.{u}} {I : Type u} [PartialOrder I] (Q : I → Type u) [∀ i, PartialOrder (Q i)]
variable (π : ∀ {i j : I}, i < j → PartialProjection κ (Q j) (Q i))

/-- Values on a cofinal subsystem determine all comparisons of threads. -/
theorem restrictThread_le_iff {x y : Set I} (h : x ⊆ y)
    (cofinal : ∀ i : y, ∃ j : x, i.val ≤ j.val) (s t : Thread Q π y) :
    restrictThread Q π h s ≤ restrictThread Q π h t ↔ s ≤ t := by
  refine ⟨?_,fun hst i => hst ⟨i.val,h i.property⟩⟩
  intro hst i
  obtain ⟨j,hj⟩ := cofinal i
  let k : y := ⟨j.val,h j.property⟩
  have hk : i ≤ k := hj
  rcases hk.lt_or_eq with hik | rfl
  · obtain ⟨hs,es⟩ := s.property i k hik
    obtain ⟨ht,et⟩ := t.property i k hik
    exact es ▸ et ▸ (π hik).proj.monotone
      (show (⟨s.val k,hs⟩ : (π hik).dom) ≤ ⟨t.val k,ht⟩ from hst j)
  · exact hst j

/-- Descending threads on growing domains have a single common thread on
their union. At each coordinate its value is the infimum of all subsequent
approximations there. Closure and continuity of each partial projection
ensure those independently computed infima form a thread. -/
theorem exists_thread_on_countable_union (hκ : Cardinal.aleph0 < κ) (hQ : ∀ i, ShortInfima κ (Q i))
    (x : Set I) (s : ℕ → Set I) (hs : Monotone s) (inside : ∀ n, s n ⊆ x)
    (cover : ∀ i : x, ∃ n, i.val ∈ s n) (t : ∀ n, Thread Q π (s n))
    (step : ∀ n m (h : n ≤ m) (i : s n), (t m).val ⟨i.val,hs h i.property⟩ ≤ (t n).val i) :
    ∃ r : Thread Q π x, ∀ n (i : s n), r.val ⟨i.val,inside n i.property⟩ ≤ (t n).val i := by
  let N := ULift.{u} ℕ
  let active (i : x) : Set N := {n | i.val ∈ s n.down}
  let valAt (i : x) (n : active i) : Q i.val := (t n.val.down).val ⟨i.val,n.property⟩
  have small (A : Set N) : Cardinal.mk A < κ :=
    (Cardinal.mk_set_le A).trans_lt (show Cardinal.mk N < κ by simpa [N] using hκ)
  have dec (i : x) : Antitone (valAt i) := by
    intro n m h
    exact step n.val.down m.val.down h ⟨i.val,n.property⟩
  choose r hr using fun i : x => hQ i.val (active i) (small _) (valAt i) (dec i)
  have glb_on {i : x} (A : Set N) (ha : A ⊆ active i)
      (later : ∀ n : active i, ∃ m : A, n.val ≤ m.val) :
      IsGLB (Set.range (fun n : A => valAt i ⟨n.val,ha n.property⟩)) (r i) := by
    refine ⟨Set.forall_mem_range.mpr (fun n : A => (hr i).1
      (Set.mem_range_self (⟨n.val,ha n.property⟩ : active i))),?_⟩
    intro z hz
    have lower (n : active i) : z ≤ valAt i n := by
      obtain ⟨m,hm⟩ := later n
      exact (hz (Set.mem_range_self m)).trans (dec i (show n ≤ ⟨m.val,ha m.property⟩ from hm))
    exact (hr i).2 (show z ∈ lowerBounds (Set.range (valAt i)) from Set.forall_mem_range.mpr lower)
  have together (i j : x) (n : active i) :
      ∃ m : (active i ∩ active j : Set N), n.val ≤ m.val := by
    obtain ⟨k,hk⟩ := cover j
    let m : N := ⟨max n.val.down k⟩
    exact ⟨⟨m,hs (le_max_left _ _) n.property,hs (le_max_right _ _) hk⟩,le_max_left _ _⟩
  have thread (i j : x) (hij : i < j) :
      ∃ h : r j ∈ (π hij).dom, (π hij).proj ⟨r j,h⟩ = r i := by
    let A := active i ∩ active j
    let vi (n : A) := valAt i ⟨n.val,n.property.1⟩
    let vj (n : A) := valAt j ⟨n.val,n.property.2⟩
    have hv (n : A) : ∃ h : vj n ∈ (π hij).dom, (π hij).proj ⟨vj n,h⟩ = vi n :=
      (t n.val.down).property ⟨i.val,n.property.1⟩ ⟨j.val,n.property.2⟩ hij
    let f (n : A) : (π hij).dom := ⟨vj n,(hv n).choose⟩
    have hf : Antitone f := fun a b hab =>
      dec j (show (⟨a.val,a.property.2⟩ : active j) ≤ ⟨b.val,b.property.2⟩ from hab)
    have hi := glb_on (i := i) A Set.inter_subset_left (together i j)
    have hj := glb_on (i := j) A Set.inter_subset_right (fun n => by
      obtain ⟨m,hm⟩ := together j i n
      exact ⟨⟨m.val,m.property.2,m.property.1⟩,hm⟩)
    have hd := (π hij).closed A (small A) f hf (r j) hj
    refine ⟨hd,?_⟩
    have hp := (π hij).continuous A (small A) f hf ⟨r j,hd⟩ hj
    have he : (fun n : A => (π hij).proj (f n)) = vi := funext fun n => (hv n).choose_spec
    rw [he] at hp
    exact hp.unique hi
  exact ⟨⟨r,thread⟩,fun n i => (hr ⟨i.val,inside n i.property⟩).1
    (Set.mem_range_self (⟨⟨n⟩,i.property⟩ : active ⟨i.val,inside n i.property⟩))⟩

end Erdos1172Shioya.InverseSystem
