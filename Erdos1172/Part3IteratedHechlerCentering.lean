/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3IteratedHechlerClosure

@[expose] public section

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3IteratedHechlerCentering

open ErdosRadoCHAsym (W1)
open Erdos1172Part3NiceFunctionNames
open Erdos1172Part3IteratedHechlerOrder
open Erdos1172Part3StationaryDecisions (Compatible IncompatibleFamily OmegaTwoCC)
open Erdos1172Part3HechlerCentering (Stem stemRank mk_Stem_le)

/-- An omegaOne-valued coding whose fibers have lower bounds for all
countable subsets. This is stronger than just the omegaTwo chain condition. -/
structure CountablyCenteredCode (P : Type) [Preorder P] where
  code : P → W1
  lower : ∀ C : Set P, C.Countable → ∀ value : W1,
    (∀ p ∈ C, code p = value) → ∃ q : P, ∀ p ∈ C, q ≤ p

variable {P : Type} [Preorder P]

theorem CountablyCenteredCode.common_lower (c : CountablyCenteredCode P) {p q : P}
    (h : c.code p = c.code q) : Compatible p q := by
  obtain ⟨r, hr⟩ := c.lower {p, q} (by simp) (c.code q) (by
    intro x hx
    rcases hx with rfl | rfl
    · exact h
    · rfl)
  exact ⟨r, hr p (by simp), hr q (by simp)⟩

theorem CountablyCenteredCode.antichain_card_le (c : CountablyCenteredCode P)
    (A : Set P) (hA : IncompatibleFamily A) : #A ≤ ℵ_ 1 := by
  have hinj : Injective (fun p : A => c.code p.val) := by
    intro p q heq
    by_contra hne
    exact hA p.val p.property q.val q.property
      (fun h => hne (Subtype.ext h)) (c.common_lower heq)
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    Cardinal.mk_le_of_injective hinj

theorem CountablyCenteredCode.omegaTwoCC (c : CountablyCenteredCode P) : OmegaTwoCC P := by
  intro A hA
  exact (c.antichain_card_le A hA).trans_lt
    (Cardinal.aleph_lt_aleph.mpr (by norm_num))

noncomputable def pairRank : (W1 × W1) ↪ W1 := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).mp
  simp only [Cardinal.mk_prod, Cardinal.lift_id, W1, Cardinal.mk_toType,
    Ordinal.card_omega, Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1), le_refl]

theorem exists_common_lower_of_same_stem_and_code (c : CountablyCenteredCode P)
    (p0 : Condition P) (C : Set (Condition P)) (hC : C.Countable)
    (hbase : ∀ p ∈ C, c.code p.base = c.code p0.base)
    (hstem : ∀ p ∈ C, p.stem = p0.stem) :
    ∃ q : Condition P, ∀ p ∈ C, q ≤ p := by
  obtain ⟨lower, hlower⟩ := c.lower (Condition.base '' C) (hC.image Condition.base)
    (c.code p0.base) (by rintro _ ⟨p, hp, rfl⟩; exact hbase p hp)
  let q : Condition P :=
    { base := lower
      stem := p0.stem
      stem_countable := p0.stem_countable
      side := ⋃ p ∈ C, p.side
      side_countable := hC.biUnion (fun p _ => p.side_countable) }
  refine ⟨q, ?_⟩
  intro p hp
  refine ⟨hlower p.base ⟨p, hp, rfl⟩, ?_, ?_, ?_⟩
  · intro i v hv
    change p0.stem i = some v
    rwa [hstem p hp] at hv
  · intro F hF
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hF⟩⟩
  · intro i hi v hv _ _
    change p0.stem i = some v at hv
    rw [hstem p hp] at hi
    rw [hi] at hv
    cases hv

/-- The pair of an old center and a new countable stem is a center for
the extended order. Named side conditions do not invalidate this fact. -/
noncomputable def CountablyCenteredCode.extend (c : CountablyCenteredCode P) (hCH : CH) :
    CountablyCenteredCode (Condition P) where
  code p := pairRank (c.code p.base, stemRank hCH ⟨p.stem, p.stem_countable⟩)
  lower := by
    intro C hC value hvalue
    by_cases hne : C.Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      have hpairs : ∀ p ∈ C,
          (c.code p.base, stemRank hCH ⟨p.stem, p.stem_countable⟩) =
            (c.code p0.base, stemRank hCH ⟨p0.stem, p0.stem_countable⟩) := by
        intro p hp
        exact pairRank.injective ((hvalue p hp).trans (hvalue p0 hp0).symm)
      apply exists_common_lower_of_same_stem_and_code c p0 C hC
      · intro p hp
        exact congrArg Prod.fst (hpairs p hp)
      · intro p hp
        exact congrArg Subtype.val ((stemRank hCH).injective (congrArg Prod.snd (hpairs p hp)))
    · obtain ⟨lower, _⟩ := c.lower ∅ Set.countable_empty value (fun _ h => h.elim)
      exact ⟨emptyOver lower, fun _ hp => (hne ⟨_, hp⟩).elim⟩

noncomputable def hechlerCentered (hCH : CH) :
    CountablyCenteredCode Erdos1172Part3HechlerOrder.Condition where
  code := Erdos1172Part3HechlerCentering.centerCode hCH
  lower := Erdos1172Part3HechlerCentering.centerCode_countably_centered hCH

theorem condition_ext {p q : Condition P} (hbase : p.base = q.base)
    (hstem : p.stem = q.stem) (hside : p.side = q.side) : p = q := by
  cases p
  cases q
  cases hbase
  cases hstem
  cases hside
  rfl

/-- Small nice names ensure that adding another dominating-function
stage preserves the alephTwo condition bound under GCH. -/
theorem mk_Condition_le (hGCH : GCH) (hP : #P ≤ ℵ_ 2) : #(Condition P) ≤ ℵ_ 2 := by
  let Side := {s : Set (NiceFunctionName P W1 W1) // #s ≤ ℵ₀}
  have hnames : #(NiceFunctionName P W1 W1) ≤ ℵ_ 2 := mk_nice_function_name_le hGCH hP
  have hside : #Side ≤ ℵ_ 2 := by
    apply (Cardinal.mk_bounded_set_le (NiceFunctionName P W1 W1) ℵ₀).trans
    exact (Cardinal.power_le_power_right (max_le hnames (Cardinal.aleph0_le_aleph 2))).trans_eq
      hGCH.aleph_two_power_aleph_zero
  let encode (p : Condition P) : P × (Stem × Side) :=
    (p.base, ⟨p.stem, p.stem_countable⟩,
      ⟨p.side, Cardinal.le_aleph0_iff_set_countable.mpr p.side_countable⟩)
  have hinj : Injective encode := by
    intro p q h
    apply condition_ext
    · exact congrArg (fun c : P × (Stem × Side) => c.1) h
    · exact congrArg (fun c : P × (Stem × Side) => c.2.1.val) h
    · exact congrArg (fun c : P × (Stem × Side) => c.2.2.val) h
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [Cardinal.mk_prod, Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  have hstem : #Stem ≤ ℵ_ 2 := (mk_Stem_le hGCH.toCH).trans
    (Cardinal.aleph_le_aleph.mpr (by norm_num : (1 : Ordinal.{0}) ≤ 2))
  have hinner : #Stem * #Side ≤ ℵ_ 2 := (mul_le_mul' hstem hside).trans_eq
    (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))
  exact (mul_le_mul' hP hinner).trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))

end Erdos1172Part3IteratedHechlerCentering
