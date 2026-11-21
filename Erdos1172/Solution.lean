/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.CountableNeighborhoodStep
public import Erdos1172.Part3Solution
public import Erdos1172.Part2NeighborhoodClosure
public import Erdos1172.Part4AnonymousInternalLevyValuation

@[expose] public section

/-!
# Solution Entrypoint for Erdős Problem 1172

This module assembles the proved endpoints for [Erdős Problem 1172](https://www.erdosproblems.com/1172),
matching the three Comparator declarations in `Challenge.lean` (`comparator.json`) as well as
universe-polymorphic and audit aliases:

* **New GCH results (`[BHT93, p. 2]`, `[Va99, 7.87]` — previously open):**
  * `Erdos1172.erdos_1172.parts.ii` : `GCH → ω₃ → (ω₂ + ω₁, ω₂ + ω)²`
  * `Erdos1172.erdos_1172.parts.iii` : `GCH → ω₂ → (ω₁^(ω + 2) + 2, ω₁ + 2)²`
* **Part (iv) (`[ErHa74, p. 272]` — first formalisation of Laver 1982 / Foreman–Hajnal 2003):**
  * `Erdos1172.erdos_1172.parts.iv` :
    `IsHugeWithTarget κ θ → (∀ μ ≥ θ, 2^μ = μ⁺) → Con(ZFC + GCH + ω₂ → (ω₁ + ω)₂²)`
    (for the `ω₁ + ω` case; the stronger simultaneous `∀ ξ < ω₂, ω₂ → (ξ)²_2` form is open).
* **Scope note on original Part (i) (`[BHT93, p. 2]`, `[Va99, 7.87]` — open):**
  * The original `[BHT93, p. 2]` Part (i) question `ω₃ → (ω₂ + 2)²_ω` under `GCH` remains **open**
    (and `erdosproblems.com/1172`'s cropped-scan binary reconstruction is omitted). As an
    unselected remark, `Erdos1172CountableNeighborhoodStep.omegaThree_to_omegaTwo_add_one_countable_of_gch`
    records our `< ℵ₂`-complete countable-color neighborhood-ideal proof of `GCH → ω₃ → (ω₂ + 1)²_ω`,
    which is due to Erdős and Rado (`[ErRa56]`; `[BHT93, Theorem 2.1]`).
* **Universe-polymorphic liftings & combined aliases:**
  * `Erdos1172.erdos_1172.part2` and `Erdos1172.erdos_1172.part3` : universe-polymorphic
    `Ordinal.{u}` liftings of Parts (ii) and (iii)
  * `Erdos1172.exact_parts23` and `Erdos1172.exact_parts23_and_gchPart4_consistency_of_huge`
-/

namespace Erdos1172

open Cardinal Ordinal Erdos1172GroundUltrapower Erdos1172AnonymousInternalLevy

/-- **Erdős Problem 1172, Part (ii)** (`[BHT93, p. 2]`, `[Va99, 7.87]`):
under `GCH`, `ω₃ → (ω₂ + ω₁, ω₂ + ω)²`. -/
theorem erdos_1172.parts.ii (hGCH : Cardinal.GCH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + ω_ 1) (ω_ 2 + ω) :=
  Erdos1172Part2NeighborhoodClosure.part2_of_gch hGCH

/-- **Erdős Problem 1172, Part (iii)** (`[BHT93, p. 2]`, `[Va99, 7.87]`):
under `GCH`, `ω₂ → (ω₁^(ω + 2) + 2, ω₁ + 2)²`. -/
theorem erdos_1172.parts.iii (hGCH : Cardinal.GCH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) :=
  Erdos1172Part3Solution.part3_of_gch hGCH

/-- Combined GCH theorem for Parts (ii) and (iii). -/
theorem exact_parts23 (hGCH : Cardinal.GCH) :
    Part2.{0} ∧ Part3.{0} :=
  ⟨erdos_1172.parts.ii hGCH, erdos_1172.parts.iii hGCH⟩

/-- **Erdős Problem 1172, Part (iv)** (`[ErHa74, p. 272]`, `ω₁ + ω` relative consistency;
Laver 1982, Foreman–Hajnal 2003): if `κ` is huge with target `θ` and ground `GCH` holds at
and above `θ`, then `ZFC + GCH + ω₂ → (ω₁ + ω, ω₁ + ω)²` is syntactically consistent. -/
theorem erdos_1172.parts.iv {κ θ : Cardinal.{0}}
    (hHuge : IsHugeWithTarget κ θ)
    (tail : ∀ μ : Cardinal.{0}, θ ≤ μ → (2 : Cardinal.{0}) ^ μ = Order.succ μ) :
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent :=
  gchPart4Theory_is_consistent_of_hugeWithTarget hHuge tail

/-- Alias for `erdos_1172.parts.iv` matching the internal consistency audit naming. -/
theorem exact_gchPart4Theory_is_consistent_of_hugeWithTarget {κ θ : Cardinal.{0}}
    (hHuge : IsHugeWithTarget κ θ)
    (tail : ∀ μ : Cardinal.{0}, θ ≤ μ → (2 : Cardinal.{0}) ^ μ = Order.succ μ) :
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent :=
  erdos_1172.parts.iv hHuge tail

/-- Combined closed-hypothesis theorem for Parts (ii)–(iv) under `Cardinal.GCH` and
`∃ κ, IsHugeCardinal κ`. -/
theorem exact_parts23_and_gchPart4_consistency_of_huge
    (hGCH : Cardinal.GCH) (hHuge : ∃ κ : Cardinal.{0}, IsHugeCardinal κ) :
    (Part2.{0} ∧ Part3.{0}) ∧
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent := by
  refine ⟨exact_parts23 hGCH, ?_⟩
  obtain ⟨κ, θ, hκθ⟩ := hHuge
  have hθ : θ.IsInaccessible := hκθ.inaccessible_right
  exact erdos_1172.parts.iv hκθ fun μ hμ => by
    obtain ⟨o, rfl⟩ := Cardinal.mem_range_aleph_iff.mpr (hθ.aleph0_lt.le.trans hμ)
    rw [hGCH o, Cardinal.succ_aleph, Order.succ_eq_add_one]

section UniverseLift

universe u

theorem toType_lift_orderIso (α : Ordinal.{0}) :
    Nonempty ((Ordinal.lift.{u, 0} α).ToType ≃o α.ToType) := by
  let r0 : α.ToType → α.ToType → Prop := (· < ·)
  let ru : ULift.{u, 0} α.ToType → ULift.{u, 0} α.ToType → Prop := (· < ·)
  have e0 : ru ≃r r0 := RelIso.preimage Equiv.ulift r0
  have h : Ordinal.type ru = Ordinal.lift.{u, 0} α := by
    have h1 := e0.ordinal_lift_type_eq
    rw [Ordinal.lift_id'.{0, u}, Ordinal.lift_umax.{0, u}] at h1
    exact h1.trans (congrArg (Ordinal.lift.{u, 0}) (Ordinal.type_toType α))
  have h2 : Ordinal.type ((· < ·) : (Ordinal.lift.{u, 0} α).ToType → _ → Prop) = Ordinal.type ru :=
    (Ordinal.type_toType (Ordinal.lift.{u, 0} α)).trans h.symm
  obtain ⟨e1⟩ := Ordinal.type_eq.mp h2
  exact ⟨OrderIso.ofRelIsoLT (e1.trans e0)⟩

theorem typeLT_preimage_orderIso {α : Type u} {β : Type 0} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (e : α ≃o β) (s : Set β) :
    typeLT (e ⁻¹' s) = Ordinal.lift.{u, 0} (typeLT s) := by
  let es : (e ⁻¹' s) ≃o s :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simp [y.2]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_rel_iff' := by intro a b; exact e.map_rel_iff }
  have h := es.toRelIsoLT.ordinal_lift_type_eq
  rw [Ordinal.lift_id'.{0, u}, Ordinal.lift_umax.{0, u}] at h
  exact h

private theorem typeLT_image_eq_of_lift {α : Type u} {β : Type 0} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (e : α ≃o β) {s : Set α} {γ : Ordinal.{0}}
    (hst : typeLT s = Ordinal.lift.{u, 0} γ) : typeLT (e '' s) = γ := by
  have hlift := typeLT_preimage_orderIso e (e '' s)
  rw [Set.preimage_image_eq s e.injective, hst] at hlift
  exact Ordinal.lift_inj.mp hlift.symm

theorem ordinalRamsey_lift_iff (α β γ : Ordinal.{0}) :
    OrdinalRamsey.{u} (Ordinal.lift.{u, 0} α) (Ordinal.lift.{u, 0} β) (Ordinal.lift.{u, 0} γ) ↔
    OrdinalRamsey.{0} α β γ := by
  obtain ⟨e⟩ := toType_lift_orderIso.{u} α
  constructor
  · intro h red blue hcompl
    obtain ⟨s, hs, hst⟩ | ⟨s, hs, hst⟩ :=
      h (red.comap e) ((red.comap e)ᶜ) isCompl_compl
    · refine Or.inl ⟨e '' s, ?_, typeLT_image_eq_of_lift e hst⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hs hx hy (fun h' => hxy (congrArg e h'))
    · refine Or.inr ⟨e '' s, ?_, typeLT_image_eq_of_lift e hst⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨hxy, (SimpleGraph.compl_adj _ _ _ |>.mp (hs hx hy (fun h' => hxy (congrArg e h')))).2⟩
  · intro h red blue hcompl
    obtain ⟨s, hs, hst⟩ | ⟨s, hs, hst⟩ :=
      h (red.comap e.symm) ((red.comap e.symm)ᶜ) isCompl_compl
    · refine Or.inl ⟨e ⁻¹' s, fun x hx y hy hxy => ?_, by rw [typeLT_preimage_orderIso e s, hst]⟩
      simpa using hs hx hy (fun h' => hxy (e.injective h'))
    · refine Or.inr ⟨e ⁻¹' s, fun x hx y hy hxy => ?_, by rw [typeLT_preimage_orderIso e s, hst]⟩
      have hedge := SimpleGraph.compl_adj _ _ _ |>.mp (hs hx hy (fun h' => hxy (e.injective h')))
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨hxy, fun hr => hedge.2 (by simpa using hr)⟩

theorem lift_pow_nat (a : Ordinal.{0}) : ∀ n : ℕ,
    Ordinal.lift.{u, 0} (a ^ (n : Ordinal.{0})) = (Ordinal.lift.{u, 0} a) ^ (n : Ordinal.{u})
  | 0 => by simp
  | n + 1 => by
      simp only [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one, Ordinal.lift_mul,
                 lift_pow_nat a n]

theorem lift_omega_opow_omega :
    Ordinal.lift.{u, 0} ((ω_ 1 : Ordinal.{0}) ^ ω) = (ω_ 1 : Ordinal.{u}) ^ ω := by
  have hω1 : Ordinal.lift.{u, 0} (ω_ 1 : Ordinal.{0}) = (ω_ 1 : Ordinal.{u}) := by
    rw [Ordinal.lift_omega, Ordinal.lift_one]
  apply le_antisymm
  · rw [← not_lt]; intro hlt
    obtain ⟨y, hy⟩ := (Ordinal.liftInitialSeg.{u, 0}).mem_range_of_le hlt.le
    have hy' : Ordinal.lift.{u, 0} y = (ω_ 1 : Ordinal.{u}) ^ ω := hy
    rw [← hy', Ordinal.lift_lt,
        Ordinal.lt_opow_of_isSuccLimit (Ordinal.omega_pos 1).ne'
          Ordinal.isSuccLimit_omega0] at hlt
    obtain ⟨c, hc, hcy⟩ := hlt
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hc
    refine not_lt_of_ge (Ordinal.lift_le.mp ?_) hcy
    rw [hy', lift_pow_nat, hω1]
    exact Ordinal.opow_le_opow_right (Ordinal.omega_pos 1) (Ordinal.natCast_lt_omega0 n).le
  · rw [Ordinal.opow_le_of_isSuccLimit (Ordinal.omega_pos 1).ne' Ordinal.isSuccLimit_omega0]
    intro b hb
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb
    rw [← hω1, ← lift_pow_nat, Ordinal.lift_le]
    exact Ordinal.opow_le_opow_right (Ordinal.omega_pos 1) (Ordinal.natCast_lt_omega0 n).le

theorem lift_omega_opow_omega_add_two :
    Ordinal.lift.{u, 0} ((ω_ 1 : Ordinal.{0}) ^ (ω + 2)) = (ω_ 1 : Ordinal.{u}) ^ (ω + 2) := by
  have hω1 : Ordinal.lift.{u, 0} (ω_ 1 : Ordinal.{0}) = (ω_ 1 : Ordinal.{u}) := by
    rw [Ordinal.lift_omega, Ordinal.lift_one]
  rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, show (2 : Ordinal.{u}) = 1 + 1 by norm_num,
      ← add_assoc, ← add_assoc, Ordinal.opow_add_one, Ordinal.opow_add_one,
      Ordinal.opow_add_one, Ordinal.opow_add_one, Ordinal.lift_mul, Ordinal.lift_mul,
      lift_omega_opow_omega, hω1]

end UniverseLift

/-- Universe-polymorphic (`Ordinal.{u}`) form of Part (ii) (`[BHT93, p. 2]`, `[Va99, 7.87]`). -/
theorem erdos_1172.part2 :
    Cardinal.GCH → OrdinalRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω) := by
  intro hGCH
  have h :=
    (ordinalRamsey_lift_iff (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω)).mpr (erdos_1172.parts.ii hGCH)
  simpa [Ordinal.lift_omega, Ordinal.lift_ofNat, Ordinal.lift_one, Ordinal.lift_add,
         Ordinal.lift_omega0] using h

/-- Universe-polymorphic (`Ordinal.{u}`) form of Part (iii) (`[BHT93, p. 2]`, `[Va99, 7.87]`). -/
theorem erdos_1172.part3 :
    Cardinal.GCH → OrdinalRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) := by
  intro hGCH
  have h :=
    (ordinalRamsey_lift_iff (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2)).mpr
      (erdos_1172.parts.iii hGCH)
  simpa [Ordinal.lift_add, lift_omega_opow_omega_add_two, Ordinal.lift_omega,
         Ordinal.lift_ofNat, Ordinal.lift_one] using h

end Erdos1172
