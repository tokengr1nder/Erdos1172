/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Statement
public import Erdos1172.CountableNeighborhoodStep
public import Erdos1172.Part3Solution
public import Erdos1172.Part2NeighborhoodClosure
public import Erdos1172.Variants
public import Erdos1172.Part4AnonymousInternalLevyValuation

@[expose] public section

/-!
# Solution Entrypoint for Erdős Problem 1172

This module assembles the proved endpoints for [Erdős Problem 1172](https://www.erdosproblems.com/1172),
matching the five Comparator declarations in `Challenge.lean` (`comparator.json`) as well as
universe-polymorphic and audit aliases:

* **New GCH results (`[BHT93, p. 2]`, `[Va99, 7.87]` — previously open):**
  * `Erdos1172.erdos_1172.parts.ii` : `GCH → ω₃ → (ω₂ + ω₁, ω₂ + ω)²`
  * `Erdos1172.erdos_1172.parts.iii` : `GCH → ω₂ → (ω₁^(ω + 2) + 2, ω₁ + 2)²`
* **Part (iv) (`[ErHa74, p. 272]` — first formalisation of Laver 1982 / Foreman–Hajnal 2003):**
  * `Erdos1172.erdos_1172.parts.iv` : `IsHugeWithTarget κ θ → (∀ μ ≥ θ, 2^μ = μ⁺) → Con(ZFC + GCH + ω₂ → (ω₁ + ω)₂²)`
    (for the `ω₁ + ω` case; the stronger simultaneous `∀ ξ < ω₂, ω₂ → (ξ)²_2` form is open).
* **Partial step toward the open original Part (i) (`[BHT93, p. 2]`, `[Va99, 7.87]`):**
  * `Erdos1172.erdos_1172.variants.part1_omega_two_add_one` : `GCH → ω₃ → (ω₂ + 1)²_ω`
    (`OrdinalCountableRamsey (ω_ 3) (ω_ 2 + 1)`), proved via our `< ℵ₂`-complete countable-color
    neighborhood-ideal machinery (`Erdos1172CountableNeighborhoodStep`); this weaker countable-color
    relation also follows from the Erdős–Rado theorem (`ErRa56`; `BHT93`, Theorem 2.1). The
    original `[BHT93, p. 2]` Part (i) question `ω₃ → (ω₂ + 2)²_ω` under `GCH` remains **open**
    (and `erdosproblems.com/1172`'s cropped-scan binary reconstruction is omitted).
* **Combined summary & aliases:**
  * `Erdos1172.erdos_1172.variants.parts_ii_iii_iv_and_part1_step` : combined `GCH` + huge-cardinal
    summary theorem for Parts (ii)–(iv) and the `ω₃ → (ω₂ + 1)²_ω` partial step
  * `Erdos1172.erdos_1172.part2`, `erdos_1172.part3`, and
    `Erdos1172.erdos_1172.variants.part1_omega_two_add_one_univ` : universe-polymorphic
    `Ordinal.{u}` liftings
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

/-- **Partial step toward original `[BHT93, p. 2]` Part (i)** (`ω₃ → (ω₂ + 1)²_ω` under `GCH`):
every countable-color pair coloring `Sym2 (ω_ 3).ToType → ℕ` admits a monochromatic subset of
order type `ω₂ + 1`. Proved here via our `< ℵ₂`-complete countable-color neighborhood-ideal
machinery (`Erdos1172CountableNeighborhoodStep`), and also entailed by Erdős–Rado (`ErRa56`;
`BHT93`, Theorem 2.1). The original `[BHT93, p. 2]` / `[Va99, 7.87]` Part (i) question
`ω₃ → (ω₂ + 2)²_ω` under `GCH` remains open. -/
theorem erdos_1172.variants.part1_omega_two_add_one (hGCH : Cardinal.GCH) :
    OrdinalCountableRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + 1) :=
  Erdos1172CountableNeighborhoodStep.omegaThree_to_omegaTwo_add_one_countable_of_gch hGCH

/-- Combined GCH theorem for the countable-color partial step `ω₃ → (ω₂ + 1)²_ω` and Parts (ii)–(iii). -/
theorem exact_parts23_and_part1_step (hGCH : Cardinal.GCH) :
    Part1CountableStep.{0} ∧ Part2.{0} ∧ Part3.{0} :=
  ⟨erdos_1172.variants.part1_omega_two_add_one hGCH, erdos_1172.parts.ii hGCH, erdos_1172.parts.iii hGCH⟩

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

/-- **Combined summary under `GCH`**: the countable-color partial step `ω₃ → (ω₂ + 1)²_ω`
(toward the open original `[BHT93, p. 2]` Part (i) `ω₃ → (ω₂ + 2)²_ω`) and Parts (ii)–(iii)
hold in `ZFC + GCH`, and if a huge cardinal exists (`∃ κ, IsHugeCardinal κ`), then
`ZFC + GCH + ω₂ → (ω₁ + ω, ω₁ + ω)²` (`gchPart4Theory`) is syntactically consistent. -/
theorem erdos_1172.variants.parts_ii_iii_iv_and_part1_step (hGCH : Cardinal.GCH) :
    (Part1CountableStep.{0} ∧ Part2.{0} ∧ Part3.{0}) ∧
    ((∃ κ : Cardinal.{0}, IsHugeCardinal κ) →
      Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent) := by
  refine ⟨exact_parts23_and_part1_step hGCH, fun hHuge => ?_⟩
  obtain ⟨κ, θ, hκθ⟩ := hHuge
  have hθ : θ.IsInaccessible := hκθ.inaccessible_right
  exact erdos_1172.parts.iv hκθ fun μ hμ => by
    obtain ⟨o, rfl⟩ := Cardinal.mem_range_aleph_iff.mpr (hθ.aleph0_lt.le.trans hμ)
    rw [hGCH o, Cardinal.succ_aleph, Order.succ_eq_add_one]

/-- Combined closed-hypothesis theorem under `Cardinal.GCH` and `∃ κ, IsHugeCardinal κ`. -/
theorem exact_parts23_part1_step_and_gchPart4_consistency_of_huge
    (hGCH : Cardinal.GCH) (hHuge : ∃ κ : Cardinal.{0}, IsHugeCardinal κ) :
    (Part1CountableStep.{0} ∧ Part2.{0} ∧ Part3.{0}) ∧
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent :=
  ⟨exact_parts23_and_part1_step hGCH, (erdos_1172.variants.parts_ii_iii_iv_and_part1_step hGCH).2 hHuge⟩

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

theorem ordinalRamsey_lift_iff (α β γ : Ordinal.{0}) :
    OrdinalRamsey.{u} (Ordinal.lift.{u, 0} α) (Ordinal.lift.{u, 0} β) (Ordinal.lift.{u, 0} γ) ↔
    OrdinalRamsey.{0} α β γ := by
  obtain ⟨e⟩ := toType_lift_orderIso.{u} α
  constructor
  · intro h red blue hcompl
    obtain ⟨s, hs, hst⟩ | ⟨s, hs, hst⟩ :=
      h (red.comap e) ((red.comap e)ᶜ) isCompl_compl
    · refine Or.inl ⟨e '' s, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
        exact hs hx hy (fun h' => hxy (congrArg e h'))
      · have pre_eq : e ⁻¹' (e '' s) = s := Set.preimage_image_eq s e.injective
        have hlift := typeLT_preimage_orderIso e (e '' s)
        rw [pre_eq, hst] at hlift
        exact Ordinal.lift_inj.mp hlift.symm
    · refine Or.inr ⟨e '' s, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
        have hedge := hs hx hy (fun h' => hxy (congrArg e h'))
        rw [SimpleGraph.compl_adj] at hedge
        rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
        exact ⟨hxy, hedge.2⟩
      · have pre_eq : e ⁻¹' (e '' s) = s := Set.preimage_image_eq s e.injective
        have hlift := typeLT_preimage_orderIso e (e '' s)
        rw [pre_eq, hst] at hlift
        exact Ordinal.lift_inj.mp hlift.symm
  · intro h red blue hcompl
    obtain ⟨s, hs, hst⟩ | ⟨s, hs, hst⟩ :=
      h (red.comap e.symm) ((red.comap e.symm)ᶜ) isCompl_compl
    · refine Or.inl ⟨e ⁻¹' s, ?_, ?_⟩
      · intro x hx y hy hxy
        have := hs hx hy (fun h' => hxy (e.injective h'))
        simpa using this
      · rw [typeLT_preimage_orderIso e s, hst]
    · refine Or.inr ⟨e ⁻¹' s, ?_, ?_⟩
      · intro x hx y hy hxy
        have hedge := hs hx hy (fun h' => hxy (e.injective h'))
        rw [SimpleGraph.compl_adj] at hedge
        rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
        exact ⟨hxy, fun hr => hedge.2 (by simpa using hr)⟩
      · rw [typeLT_preimage_orderIso e s, hst]

theorem ordinalCountableRamsey_lift_iff (α β : Ordinal.{0}) :
    OrdinalCountableRamsey.{u} (Ordinal.lift.{u, 0} α) (Ordinal.lift.{u, 0} β) ↔
    OrdinalCountableRamsey.{0} α β := by
  obtain ⟨e⟩ := toType_lift_orderIso.{u} α
  constructor
  · intro h col
    obtain ⟨n, s, hs, hst⟩ := h (fun p => col (p.map e))
    refine ⟨n, e '' s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hs x hx y hy (fun h' => hxy (congrArg e h'))
    · have pre_eq : e ⁻¹' (e '' s) = s := Set.preimage_image_eq s e.injective
      have hlift := typeLT_preimage_orderIso e (e '' s)
      rw [pre_eq, hst] at hlift
      exact Ordinal.lift_inj.mp hlift.symm
  · intro h col
    obtain ⟨n, s, hs, hst⟩ := h (fun p => col (p.map e.symm))
    refine ⟨n, e ⁻¹' s, ?_, ?_⟩
    · intro x hx y hy hxy
      have hcol : col s(e.symm (e x), e.symm (e y)) = n :=
        hs (e x) hx (e y) hy (fun h' => hxy (e.injective h'))
      rwa [e.symm_apply_apply, e.symm_apply_apply] at hcol
    · rw [typeLT_preimage_orderIso e s, hst]

theorem lift_pow_nat (a : Ordinal.{0}) : ∀ n : ℕ,
    Ordinal.lift.{u, 0} (a ^ (n : Ordinal.{0})) = (Ordinal.lift.{u, 0} a) ^ (n : Ordinal.{u})
  | 0 => by simp
  | n + 1 => by
      simp only [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one, Ordinal.lift_mul, lift_pow_nat a n]

theorem lift_omega_opow_omega :
    Ordinal.lift.{u, 0} ((ω_ 1 : Ordinal.{0}) ^ ω) = (ω_ 1 : Ordinal.{u}) ^ ω := by
  have hω1 : Ordinal.lift.{u, 0} (ω_ 1 : Ordinal.{0}) = (ω_ 1 : Ordinal.{u}) := by
    rw [Ordinal.lift_omega, Ordinal.lift_one]
  apply le_antisymm
  · rw [← not_lt]
    intro hlt
    obtain ⟨y, hy⟩ := (Ordinal.liftInitialSeg.{u, 0}).mem_range_of_le hlt.le
    have hy' : Ordinal.lift.{u, 0} y = (ω_ 1 : Ordinal.{u}) ^ ω := hy
    rw [← hy', Ordinal.lift_lt,
        Ordinal.lt_opow_of_isSuccLimit (Ordinal.omega_pos 1).ne' Ordinal.isSuccLimit_omega0] at hlt
    obtain ⟨c, hc, hcy⟩ := hlt
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hc
    have hle : Ordinal.lift.{u, 0} ((ω_ 1 : Ordinal.{0}) ^ (n : Ordinal.{0})) ≤ Ordinal.lift.{u, 0} y := by
      rw [hy', lift_pow_nat, hω1]
      exact Ordinal.opow_le_opow_right (Ordinal.omega_pos 1) (Ordinal.natCast_lt_omega0 n).le
    exact not_lt_of_ge (Ordinal.lift_le.mp hle) hcy
  · rw [Ordinal.opow_le_of_isSuccLimit (Ordinal.omega_pos 1).ne' Ordinal.isSuccLimit_omega0]
    intro b hb
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb
    rw [← hω1, ← lift_pow_nat, Ordinal.lift_le]
    exact Ordinal.opow_le_opow_right (Ordinal.omega_pos 1) (Ordinal.natCast_lt_omega0 n).le

theorem lift_omega_opow_omega_add_two :
    Ordinal.lift.{u, 0} ((ω_ 1 : Ordinal.{0}) ^ (ω + 2)) = (ω_ 1 : Ordinal.{u}) ^ (ω + 2) := by
  have h20 : (2 : Ordinal.{0}) = 1 + 1 := by norm_num
  have h2u : (2 : Ordinal.{u}) = 1 + 1 := by norm_num
  have hω1 : Ordinal.lift.{u, 0} (ω_ 1 : Ordinal.{0}) = (ω_ 1 : Ordinal.{u}) := by
    rw [Ordinal.lift_omega, Ordinal.lift_one]
  rw [h20, h2u, ← add_assoc, ← add_assoc, Ordinal.opow_add_one, Ordinal.opow_add_one,
      Ordinal.opow_add_one, Ordinal.opow_add_one, Ordinal.lift_mul, Ordinal.lift_mul,
      lift_omega_opow_omega, hω1]

end UniverseLift

/-- Universe-polymorphic (`Ordinal.{u}`) form of the partial step `GCH → ω₃ → (ω₂ + 1)²_ω`. -/
theorem erdos_1172.variants.part1_omega_two_add_one_univ :
    Cardinal.GCH → OrdinalCountableRamsey (ω_ 3) (ω_ 2 + 1) := by
  intro hGCH
  have h := (ordinalCountableRamsey_lift_iff (ω_ 3) (ω_ 2 + 1)).mpr
    (erdos_1172.variants.part1_omega_two_add_one hGCH)
  simpa [Ordinal.lift_omega, Ordinal.lift_ofNat, Ordinal.lift_one, Ordinal.lift_add] using h

/-- Universe-polymorphic (`Ordinal.{u}`) form of Part (ii) (`[BHT93, p. 2]`, `[Va99, 7.87]`). -/
theorem erdos_1172.part2 :
    Cardinal.GCH → OrdinalRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω) := by
  intro hGCH
  have h := (ordinalRamsey_lift_iff (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω)).mpr (erdos_1172.parts.ii hGCH)
  simpa [Ordinal.lift_omega, Ordinal.lift_ofNat, Ordinal.lift_one, Ordinal.lift_add,
         Ordinal.lift_omega0] using h

/-- Universe-polymorphic (`Ordinal.{u}`) form of Part (iii) (`[BHT93, p. 2]`, `[Va99, 7.87]`). -/
theorem erdos_1172.part3 :
    Cardinal.GCH → OrdinalRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) := by
  intro hGCH
  have h := (ordinalRamsey_lift_iff (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2)).mpr (erdos_1172.parts.iii hGCH)
  simpa [Ordinal.lift_add, lift_omega_opow_omega_add_two, Ordinal.lift_omega,
         Ordinal.lift_ofNat, Ordinal.lift_one] using h

end Erdos1172
