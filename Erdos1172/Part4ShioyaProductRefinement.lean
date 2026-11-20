/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4DualShioyaForcing
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! # Refining a dual Shioya condition by a product

An arbitrary small separative, completely κ-closed forcing can be added
as a second factor of the presentation. The new condition has the
translated string and can choose a point of the new factor.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}} {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem glbRange {T L : Type u} [PartialOrder T] (f : L → T) (p : T) :
    IsGLB (Set.range f) p ↔ (∀ i, p ≤ f i) ∧ (∀ t, (∀ i, t ≤ f i) → t ≤ p) :=
  ⟨fun h => ⟨fun i => h.1 (Set.mem_range_self i), fun _ hl => h.2 (Set.forall_mem_range.mpr hl)⟩,
    fun h => ⟨Set.forall_mem_range.mpr h.1, fun _ hl => h.2 _ (Set.forall_mem_range.mp hl)⟩⟩

theorem glb_image {L : Type u} (e : P ≃o Q) (f : L → P) (p : P) :
    IsGLB (Set.range (fun i => e (f i))) (e p) ↔ IsGLB (Set.range f) p := by
  change IsGLB (Set.range (e ∘ f)) (e p) ↔ _
  rw [Set.range_comp, e.isGLB_image']

/-- Present any small partial order on an ordinal strictly below θ. -/
theorem exists_small_presentation (P : Type u) [PartialOrder P] (hP : Cardinal.mk P < θ) :
    ∃ A : Presentation θ, Nonempty (A.Carrier ≃o P) := by
  let a : θ.ord.ToType := Ordinal.ToType.mk ⟨(Cardinal.mk P).ord, Cardinal.ord_lt_ord.mpr hP⟩
  have ha : a.toOrd.val = (Cardinal.mk P).ord :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  let e : a.toOrd.val.ToType ≃ P := (Cardinal.eq.mp (by rw [ha, Cardinal.mk_ord_toType])).some
  let A : Presentation θ := ⟨a, PartialOrder.lift e e.injective⟩
  exact ⟨A, ⟨{ toEquiv := e, map_rel_iff' := Iff.rfl }⟩⟩

theorem shortInfima_of_iso (e : P ≃o Q) (hQ : ShortInfima κ Q) : ShortInfima κ P := by
  intro L _ _ hL f hf
  obtain ⟨q, hq⟩ := hQ L hL (fun i => e (f i)) (e.monotone.comp_antitone hf)
  exact ⟨e.symm q, (glb_image e f _).mp (by simpa only [e.apply_symm_apply] using hq)⟩

theorem separative_of_iso (e : P ≃o Q) (hQ : Separative Q) : Separative P := by
  intro p q hpq
  obtain ⟨r, hr, h⟩ := hQ (e p) (e q) (by simpa using hpq)
  refine ⟨e.symm r, (e.symm_apply_le).2 hr, ?_⟩
  rintro ⟨t, ht, htq⟩
  exact h ⟨e t, e.le_symm_apply.mp ht, e.monotone htq⟩

theorem shortInfima_prod (hP : ShortInfima κ P) (hQ : ShortInfima κ Q) : ShortInfima κ (P × Q) := by
  intro L _ _ hL f hf
  obtain ⟨p, hp⟩ := hP L hL (fun i => (f i).1) (fun _ _ h => (hf h).1)
  obtain ⟨q, hq⟩ := hQ L hL (fun i => (f i).2) (fun _ _ h => (hf h).2)
  have h₁ := (glbRange _ _).mp hp
  have h₂ := (glbRange _ _).mp hq
  exact ⟨(p,q), (glbRange _ _).mpr ⟨fun i => ⟨h₁.1 i, h₂.1 i⟩,
    fun t h => ⟨h₁.2 t.1 (fun i => (h i).1), h₂.2 t.2 (fun i => (h i).2)⟩⟩⟩

theorem separative_prod (hP : Separative P) (hQ : Separative Q) : Separative (P × Q) := by
  intro p q hn
  by_cases h : p.1 ≤ q.1
  · obtain ⟨r, hr, hi⟩ := hQ p.2 q.2 (fun h' => hn ⟨h, h'⟩)
    exact ⟨(p.1,r), ⟨le_rfl, hr⟩, fun ⟨s, hs, ht⟩ => hi ⟨s.2, hs.2, ht.2⟩⟩
  · obtain ⟨r, hr, hi⟩ := hP p.1 q.1 h
    exact ⟨(r,p.2), ⟨hr, le_rfl⟩, fun ⟨s, hs, ht⟩ => hi ⟨s.1, hs.1, ht.1⟩⟩

variable {S : Type u} [PartialOrder S]

/-- The first projection of a relabelled product, with its full domain. -/
def productProjection (e : S ≃o P × Q) (q₀ : Q) : PartialProjection κ S P where
  dom := Set.univ
  dense s := ⟨⟨s, Set.mem_univ s⟩, le_rfl⟩
  proj := ⟨fun s => (e s.val).1, fun _ _ h => (e.monotone h).1⟩
  reaches p := ⟨⟨e.symm (p,q₀), Set.mem_univ _⟩, by
    change (e (e.symm (p,q₀))).1 ≤ p
    rw [e.apply_symm_apply]⟩
  lifts x p h := by
    refine ⟨⟨e.symm (p,(e x.val).2), Set.mem_univ _⟩, ?_, ?_⟩
    · exact (e.symm_apply_le).2 ⟨h, le_rfl⟩
    · change (e (e.symm (p,(e x.val).2))).1 ≤ p
      rw [e.apply_symm_apply]
  closed _ _ _ _ _ _ p _ := Set.mem_univ p
  continuous L _ _ _ f _ p hp := by
    have h := (glbRange _ _).mp ((glb_image e _ _).mpr hp)
    apply (glbRange _ _).mpr
    refine ⟨fun i => (h.1 i).1, fun t ht => ?_⟩
    exact (h.2 (t,(e p.val).2) (fun i => ⟨ht i, (h.1 i).2⟩)).1

namespace Condition

theorem exists_product_refinement (p : Condition κ θ) (q : Q) (hq : Cardinal.mk Q < θ)
    (hθ : θ.IsInaccessible) (hsep : Separative Q) (hcl : ShortInfima κ Q) :
    ∃ w : Condition κ θ, ∃ e : w.Poset ≃o p.Poset × Q,
      e w.point = (p.point, q) ∧ w.length = p.length ∧ Refines w p := by
  have hsize : Cardinal.mk (p.Poset × Q) < θ := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le p.presentation.cardinal_lt hq
  obtain ⟨A, ⟨e⟩⟩ := exists_small_presentation (p.Poset × Q) hsize
  let π := productProjection (κ := κ) e q
  let w : Condition κ θ :=
    ⟨A, separative_of_iso e (separative_prod p.separative hsep),
      shortInfima_of_iso e (shortInfima_prod p.complete hcl),
      e.symm (p.point, q), p.length, fun i => π.booleanHom (p.bits i)⟩
  refine ⟨w, e, e.apply_symm_apply _, rfl, π, ?_, ?_⟩
  · apply (π.dom_condition ⟨w.point, Set.mem_univ _⟩ _).mpr
    change condition (e (e.symm (p.point,q))).1 ≤ condition p.point
    rw [e.apply_symm_apply]
  · let : Nonempty A.Carrier := ⟨w.point⟩
    let : NontrivialCompleteBooleanAlgebra w.Algebra :=
      { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
    apply extensionValue_of_bits π.booleanHom p.name w.name le_rfl
    intro i
    have hi : StringName.includeIndex (show p.length.toOrd.val ≤ w.length.toOrd.val from le_rfl) i = i :=
      Ordinal.ToType.mk.symm.injective (Subtype.ext (StringName.includeIndex_toOrd le_rfl i))
    simp only [hi, name, StringName.bits_ofBits]
    exact rfl

end Condition
end Erdos1172Shioya
