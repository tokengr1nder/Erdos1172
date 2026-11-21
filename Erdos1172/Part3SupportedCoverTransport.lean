/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SupportedCoverRealization

@[expose] public section

/-! Finite certificates survive coordinate transport and finite assembly.
These lemmas compare actual membership at every refinement. They require
neither countable closure nor a ground function dominating a name. -/

open Set

namespace Erdos1172Part3SupportedCoverTransport

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3SupportedCoverRealization

variable {P X Y Z : Type} [Preorder P]

theorem holds_of_family_subset {F : FunctionDecisions P W1 W1}
    {C D : (W1 → W1) → Set X} (hCD : ∀ f, C f ⊆ D f)
    {p : P} {x : X} (hx : (coverName F C).holds p x) :
    (coverName F D).holds p x := by
  intro q hqp
  obtain ⟨r, hrq, f, s, hd, hc⟩ := hx q hqp
  exact ⟨r, hrq, f, s, hd, fun g hg => hCD g (hc g hg)⟩

/-- Two certificates for one name have compatible values on overlapping
supports. Decide their finite union and use the actual common values. -/
theorem certificate_combine {F : FunctionDecisions P W1 W1}
    {C : (W1 → W1) → Set X} {D : (W1 → W1) → Set Y}
    {A : (W1 → W1) → Set Z} {p : P} {x : X} {y : Y} {z : Z}
    (hc : Certificate F C p x) (hd : Certificate F D p y)
    (hcombine : ∀ f, x ∈ C f → y ∈ D f → z ∈ A f) :
    (coverName F A).holds p z := by
  classical
  obtain ⟨f, s, hfs, hC⟩ := hc
  obtain ⟨g, t, hgt, hD⟩ := hd
  intro q hqp
  obtain ⟨r, hrq, hvalues⟩ := exists_finite_decisions F (s ∪ t) q
  let value (i : ↥(s ∪ t)) : W1 := (hvalues i.val i.property).choose
  let h (i : W1) : W1 := if hi : i ∈ s ∪ t then value ⟨i, hi⟩ else f i
  have hdec (i : W1) (hi : i ∈ s ∪ t) : F.decides r i (h i) := by
    simpa only [h, dif_pos hi, value] using (hvalues i hi).choose_spec
  refine ⟨r, hrq, h, s ∪ t, hdec, ?_⟩
  intro k hk
  apply hcombine k
  · apply hC k
    intro i hi
    have hfi : f i = h i := F.unique
      (F.persistent (hrq.trans hqp) (hfs i hi)) (hdec i (Finset.mem_union_left t hi))
    exact hfi.le.trans (hk i (Finset.mem_union_left t hi))
  · apply hD k
    intro i hi
    have hgi : g i = h i := F.unique
      (F.persistent (hrq.trans hqp) (hgt i hi)) (hdec i (Finset.mem_union_right s hi))
    exact hgi.le.trans (hk i (Finset.mem_union_right s hi))

theorem holds_combine {F : FunctionDecisions P W1 W1}
    {C : (W1 → W1) → Set X} {D : (W1 → W1) → Set Y}
    {A : (W1 → W1) → Set Z} {p : P} {x : X} {y : Y} {z : Z}
    (hc : (coverName F C).holds p x) (hd : (coverName F D).holds p y)
    (hcombine : ∀ f, x ∈ C f → y ∈ D f → z ∈ A f) :
    (coverName F A).holds p z := by
  apply (coverName F A).of_dense p z
  intro q hqp
  obtain ⟨r, hrq, hC⟩ := hc q hqp
  obtain ⟨s, hsr, hD⟩ := hd r (hrq.trans hqp)
  exact ⟨s, hsr.trans hrq, certificate_combine (certificate_persistent hsr hC) hD hcombine⟩

/-- A coordinate map need not be injective: common decisions themselves
ensure the comparisons needed on its finite image support. -/
theorem precompose_holds_of_certificate
    {F H : FunctionDecisions P W1 W1} {C : (W1 → W1) → Set X}
    (e : W1 → W1) {p : P} {x : X}
    (hbelow : ∀ q : P, q ≤ p → ∀ i v w, F.decides q i v → H.decides q (e i) w → v ≤ w)
    (hc : Certificate F C p x) :
    (coverName H (fun f => C (f ∘ e))).holds p x := by
  classical
  obtain ⟨f, s, hdecF, hcover⟩ := hc
  intro q hqp
  obtain ⟨r, hrq, hvalues⟩ := exists_finite_decisions H (s.image e) q
  let value (i : ↥(s.image e)) : W1 := (hvalues i.val i.property).choose
  let h (i : W1) : W1 := if hi : i ∈ s.image e then value ⟨i, hi⟩ else f i
  have hdecH (i : W1) (hi : i ∈ s.image e) : H.decides r i (h i) := by
    simpa only [h, dif_pos hi, value] using (hvalues i hi).choose_spec
  refine ⟨r, hrq, h, s.image e, hdecH, ?_⟩
  intro k hk
  apply hcover (k ∘ e)
  intro i hi
  have hei : e i ∈ s.image e := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  exact (hbelow r (hrq.trans hqp) i (f i) (h (e i))
    (F.persistent (hrq.trans hqp) (hdecF i hi)) (hdecH (e i) hei)).trans (hk (e i) hei)

theorem holds_precompose
    {F H : FunctionDecisions P W1 W1} {C : (W1 → W1) → Set X}
    (e : W1 → W1) {p : P} {x : X}
    (hbelow : ∀ q : P, q ≤ p → ∀ i v w, F.decides q i v → H.decides q (e i) w → v ≤ w)
    (hc : (coverName F C).holds p x) :
    (coverName H (fun f => C (f ∘ e))).holds p x := by
  apply (coverName H (fun f => C (f ∘ e))).of_dense p x
  intro q hqp
  obtain ⟨r, hrq, hr⟩ := hc q hqp
  exact ⟨r, hrq, precompose_holds_of_certificate e
    (fun s hsr i v w hv hw => hbelow s (hsr.trans (hrq.trans hqp)) i v w hv hw) hr⟩

end Erdos1172Part3SupportedCoverTransport
