/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRadoCHAsymmetric
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-! Generic finite-coordinate membership certificates. These basic
closure laws do not depend on the finite-power cover construction. -/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalCoverSupport

open ErdosRadoCHAsym (W1)

def FinitelySupported {I X : Type} (C : (I → W1) → Set X) : Prop :=
  ∀ f : I → W1, ∀ x ∈ C f, ∃ s : Finset I,
    ∀ g : I → W1, (∀ i ∈ s, f i ≤ g i) → x ∈ C g

theorem constant_supported {I X : Type} (A : Set X) :
    FinitelySupported (fun _ : I → W1 => A) := by
  intro f x hx
  exact ⟨∅, fun _ _ => hx⟩

theorem precompose_supported {I J X : Type} (e : J → I) (C : (J → W1) → Set X)
    (hC : FinitelySupported C) : FinitelySupported (fun f : I → W1 => C (f ∘ e)) := by
  classical
  intro f x hx
  obtain ⟨s, hs⟩ := hC (f ∘ e) x hx
  refine ⟨s.image e, fun g hg => hs (g ∘ e) ?_⟩
  exact fun j hj => hg (e j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

theorem image_supported {I X Y : Type} (C : (I → W1) → Set X) (hC : FinitelySupported C)
    (map : X → Y) : FinitelySupported (fun f => map '' C f) := by
  intro f y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨s, hs⟩ := hC f x hx
  exact ⟨s, fun g hg => ⟨x, hs g hg, rfl⟩⟩

theorem union_supported {I X : Type} (C D : (I → W1) → Set X)
    (hC : FinitelySupported C) (hD : FinitelySupported D) :
    FinitelySupported (fun f => C f ∪ D f) := by
  intro f x hx
  rcases hx with hx | hx
  · obtain ⟨s, hs⟩ := hC f x hx
    exact ⟨s, fun g hg => Or.inl (hs g hg)⟩
  · obtain ⟨s, hs⟩ := hD f x hx
    exact ⟨s, fun g hg => Or.inr (hs g hg)⟩

theorem iUnion_supported {I J X : Type} (C : J → (I → W1) → Set X)
    (hC : ∀ j, FinitelySupported (C j)) : FinitelySupported (fun f => ⋃ j, C j f) := by
  intro f x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs⟩ := hC j f x hj
  exact ⟨s, fun g hg => Set.mem_iUnion.mpr ⟨j, hs g hg⟩⟩

end Erdos1172Part3CofinalCoverSupport
