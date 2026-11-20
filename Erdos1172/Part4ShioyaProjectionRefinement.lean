/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaProductRefinement

@[expose] public section

/-! # Refinement along a partial projection

A projection from a small separative and completely closed poset onto
the underlying presentation gives a stronger dual Shioya condition.
Its point projects below the old point. Its string has the same length
and consists of the translated Boolean coefficients.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}} {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

namespace PartialProjection

def preimageIso (e : R ≃o Q) (d : Set Q) : (e ⁻¹' d) ≃o d where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by simpa only [Set.mem_preimage, e.apply_symm_apply] using y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_rel_iff' := e.map_rel_iff'

theorem image_glb (e : R ≃o Q) {I : Type u} (f : I → R) (p : R)
    (hp : IsGLB (Set.range f) p) : IsGLB (Set.range (fun i => e (f i))) (e p) := by
  change IsGLB (Set.range (e ∘ f)) (e p)
  rw [Set.range_comp, e.isGLB_image']
  exact hp

def precomposeIso (π : PartialProjection κ Q P) (e : R ≃o Q) : PartialProjection κ R P where
  dom := e ⁻¹' π.dom
  dense r := by
    obtain ⟨x, hx⟩ := π.dense (e r)
    exact ⟨(preimageIso e π.dom).symm x, e.symm_apply_le.mpr hx⟩
  proj := ⟨fun x => π.proj (preimageIso e π.dom x), fun _ _ h => π.proj.monotone ((preimageIso e π.dom).monotone h)⟩
  reaches p := by
    obtain ⟨x, hx⟩ := π.reaches p
    refine ⟨(preimageIso e π.dom).symm x, ?_⟩
    change π.proj (preimageIso e π.dom ((preimageIso e π.dom).symm x)) ≤ p
    rw [OrderIso.apply_symm_apply]
    exact hx
  lifts x p hp := by
    let d := preimageIso e π.dom
    obtain ⟨y, hy, hyp⟩ := π.lifts (d x) p hp
    refine ⟨d.symm y, d.symm_apply_le.mpr hy, ?_⟩
    change π.proj (d (d.symm y)) ≤ p
    rw [d.apply_symm_apply]
    exact hyp
  closed L _ _ hL f hf p hp := by
    let d := preimageIso e π.dom
    exact π.closed L hL (fun i => d (f i)) (d.monotone.comp_antitone hf) (e p)
      (image_glb e (fun i => (f i).val) p hp)
  continuous L _ _ hL f hf p hp := by
    let d := preimageIso e π.dom
    exact π.continuous L hL (fun i => d (f i)) (d.monotone.comp_antitone hf) (d p)
      (image_glb e (fun i => (f i).val) p.val hp)

end PartialProjection

namespace Condition

theorem exists_projection_refinement (p : Condition κ θ) (Q : Type u) [PartialOrder Q]
    (hQ : Cardinal.mk Q < θ) (hsep : Separative Q) (hcl : ShortInfima κ Q)
    (π : PartialProjection κ Q p.Poset) :
    ∃ w : Condition κ θ, Nonempty (w.Poset ≃o Q) ∧ w.length = p.length ∧ Refines w p := by
  obtain ⟨A, ⟨e⟩⟩ := exists_small_presentation Q hQ
  let σ := π.precomposeIso e
  obtain ⟨x, hx⟩ := σ.reaches p.point
  let w : Condition κ θ :=
    ⟨A, separative_of_iso e hsep, shortInfima_of_iso e hcl, x.val, p.length, fun i => σ.booleanHom (p.bits i)⟩
  refine ⟨w, ⟨e⟩, rfl, σ, (σ.dom_condition x _).mpr (condition_mono hx), ?_⟩
  let : Nonempty A.Carrier := ⟨w.point⟩
  let : NontrivialCompleteBooleanAlgebra w.Algebra :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  apply extensionValue_of_bits σ.booleanHom p.name w.name le_rfl
  intro i
  have hi : StringName.includeIndex (show p.length.toOrd.val ≤ w.length.toOrd.val from le_rfl) i = i :=
    Ordinal.ToType.mk.symm.injective (Subtype.ext (StringName.includeIndex_toOrd le_rfl i))
  simp only [hi, name, StringName.bits_ofBits]
  exact rfl

end Condition
end Erdos1172Shioya
