/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaStringTransport
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! # Countable fusion of names for binary strings

A common positive Boolean condition can force successive strings to extend
one another. At each position of the supremum of their lengths, take the bit
from any stage containing that position. On the given condition all such
choices agree.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Erdos1172Shioya.StringName

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
variable {γ : ℕ → Ordinal.{u}} (s : ∀ n, StringName B (γ n)) {Γ : B}

theorem extensionValue_of_successive (hstep : ∀ n, Γ ≤ extensionValue (CompleteLatticeHom.id B) (s n) (s (n+1)))
    {n m : ℕ} (hnm : n ≤ m) : Γ ≤ extensionValue (CompleteLatticeHom.id B) (s n) (s m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_top.trans (extensionValue_refl (s n))
  | succ k _ ih =>
    exact extensionValue_trans (CompleteLatticeHom.id B) (CompleteLatticeHom.id B) (s n) (s k) (s (k+1))
      (p := Γ) (q := Γ) le_rfl ih (hstep k)

theorem exists_countable_fusion (hΓ : Γ ≠ ⊥)
    (hstep : ∀ n, Γ ≤ extensionValue (CompleteLatticeHom.id B) (s n) (s (n+1))) :
    ∃ t : StringName B (⨆ n, γ n), ∀ n, Γ ≤ extensionValue (CompleteLatticeHom.id B) (s n) t := by
  classical
  have forward {n m : ℕ} (hnm : n ≤ m) (i : (γ n).ToType) (j : (γ m).ToType)
      (he : i.toOrd.val = j.toOrd.val) : Γ ⊓ (s n).bits i = Γ ⊓ (s m).bits j := by
    obtain ⟨h, hb⟩ := (extensionValue_iff_bits (CompleteLatticeHom.id B) (s n) (s m) hΓ).mp
      (extensionValue_of_successive s hstep hnm)
    have hj : includeIndex h i = j :=
      Ordinal.ToType.mk.symm.injective (Subtype.ext ((includeIndex_toOrd h i).trans he))
    simpa only [CompleteLatticeHom.id_apply, hj] using hb i
  have agree {n m : ℕ} (i : (γ n).ToType) (j : (γ m).ToType) (he : i.toOrd.val = j.toOrd.val) :
      Γ ⊓ (s n).bits i = Γ ⊓ (s m).bits j := by
    rcases le_total n m with h | h
    · exact forward h i j he
    · exact (forward h j i he.symm).symm
  have stage (j : (⨆ n, γ n).ToType) : ∃ n, j.toOrd.val < γ n := Ordinal.lt_iSup_iff.mp j.toOrd.property
  let atStage (j : (⨆ n, γ n).ToType) : (γ (stage j).choose).ToType :=
    Ordinal.ToType.mk ⟨j.toOrd.val, (stage j).choose_spec⟩
  have hpos (j : (⨆ n, γ n).ToType) : (atStage j).toOrd.val = j.toOrd.val :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  let b (j : (⨆ n, γ n).ToType) := (s (stage j).choose).bits (atStage j)
  refine ⟨ofBits _ b, fun n => extensionValue_of_bits _ _ _ (Ordinal.le_iSup γ n) Γ ?_⟩
  intro i
  rw [bits_ofBits, CompleteLatticeHom.id_apply]
  exact agree i _ ((includeIndex_toOrd _ i).symm.trans (hpos _).symm)

theorem fusion_length_lt {θ : Cardinal.{u}} (hθ : θ.IsInaccessible) (hγ : ∀ n, γ n < θ.ord) :
    (⨆ n, γ n) < θ.ord := by
  apply Ordinal.lift_iSup_lt_of_lt_cof _ hγ
  simpa [hθ.isRegular.cof_ord] using hθ.aleph0_lt

theorem exists_bounded_mapped_fusion {θ : Cardinal.{u}} (hθ : θ.IsInaccessible)
    (hγ : ∀ n, γ n < θ.ord) (A : ℕ → Type u) [∀ n, NontrivialCompleteBooleanAlgebra (A n)]
    (f : ∀ n, CompleteLatticeHom (A n) B) (v : ∀ n, StringName (A n) (γ n)) (hΓ : Γ ≠ ⊥)
    (hstep : ∀ n, Γ ≤ extensionValue (CompleteLatticeHom.id B) ((v n).map (f n)) ((v (n+1)).map (f (n+1)))) :
    (⨆ n, γ n) < θ.ord ∧ ∃ t : StringName B (⨆ n, γ n), ∀ n, Γ ≤ extensionValue (f n) (v n) t := by
  obtain ⟨t, ht⟩ := exists_countable_fusion (fun n => (v n).map (f n)) hΓ hstep
  refine ⟨fusion_length_lt hθ hγ, t, fun n => ?_⟩
  simpa only [extensionValue, map_id] using ht n

theorem exists_bounded_fusion_of_commuting_maps {θ : Cardinal.{u}} (hθ : θ.IsInaccessible)
    (hγ : ∀ n, γ n < θ.ord) (A : ℕ → Type u) [∀ n, NontrivialCompleteBooleanAlgebra (A n)]
    (g : ∀ n, CompleteLatticeHom (A n) (A (n+1))) (f : ∀ n, CompleteLatticeHom (A n) B)
    (hcomm : ∀ n, (f (n+1)).comp (g n) = f n) (v : ∀ n, StringName (A n) (γ n))
    (hΓ : Γ ≠ ⊥) (hstep : ∀ n, Γ ≤ f (n+1) (extensionValue (g n) (v n) (v (n+1)))) :
    (⨆ n, γ n) < θ.ord ∧ ∃ t : StringName B (⨆ n, γ n), ∀ n, Γ ≤ extensionValue (f n) (v n) t := by
  apply exists_bounded_mapped_fusion hθ hγ A f v hΓ
  intro n
  have h := hstep n
  simp only [extensionValue, bSet.ErdosNameTransport.map_subset] at h
  rw [extensionValue, map_id, ← hcomm n, map_comp]
  exact h

end Erdos1172Shioya.StringName
