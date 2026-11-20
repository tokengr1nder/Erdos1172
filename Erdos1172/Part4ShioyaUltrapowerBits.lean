/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerProjection

@[expose] public section

/-! # Boolean coefficients of strings on bounded ultrapower stages -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def values (b : Point U a (Completion P)) : LowerSet (Point U a P) where
  carrier := {p | ∀ᶠ i in U, condition (repr U a p i) ≤ repr U a b i}
  lower' := by
    intro x y hxy hy
    exact (((le_iff U a _ _).mp hxy).and hy).mono fun _ hi => (condition_mono hi.1).trans hi.2

theorem values_compl (b : Point U a (Completion P)) :
    values U a (map U a compl b) = (values U a b)ᶜ := by
  apply SetLike.ext
  intro p
  rw [mem_pseudocompl_iff]
  change (∀ᶠ i in U, condition (repr U a p i) ≤ repr U a (map U a compl b) i) ↔ _
  constructor
  · intro h q hqp hq
    obtain ⟨i,hh,hv,hle,hm⟩ := (h.and ((map_repr U a compl b).and (((le_iff U a _ _).mp hqp).and hq))).exists
    have hc := (condition_mono hle).trans (hh.trans_eq hv)
    exact condition_ne_bot (repr U a q i) (bot_unique ((le_inf hm hc).trans inf_compl_eq_bot.le))
  · intro h
    by_contra bad
    have hbad := (U.eventually_not.mpr bad).and (map_repr U a compl b)
    have hex : ∀ᶠ i in U, ∃ q, q ≤ repr U a p i ∧ condition q ≤ repr U a b i := hbad.mono fun i hi => by
      by_contra! hnone
      apply hi.1
      rw [hi.2,condition_le_iff]
      exact (mem_pseudocompl_iff _ _).mpr fun q hq hmem => hnone q hq (condition_le_iff.mpr hmem)
    obtain ⟨q,hq⟩ := choose_pair U a p b (fun t c y => y ≤ t ∧ condition y ≤ c) hex
    exact h q ((le_iff U a _ _).mpr (hq.mono fun _ hi => hi.1)) (hq.mono fun _ hi => hi.2)

def booleanValue (b : Point U a (Completion P)) : Completion (Point U a P) := by
  refine ⟨values U a b,?_⟩
  change (values U a b)ᶜᶜ = values U a b
  rw [← values_compl,← values_compl]
  apply congrArg (values U a)
  apply Subtype.ext
  obtain ⟨η,f,hf⟩ := b.property
  change Germ.map compl (Germ.map compl b.val) = b.val
  rw [← hf]
  exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => compl_compl _)

theorem condition_le_booleanValue (p : Point U a P) (b : Point U a (Completion P)) :
    condition p ≤ booleanValue U a b ↔ ∀ᶠ i in U, condition (repr U a p i) ≤ repr U a b i :=
  condition_le_iff

theorem booleanValue_mono : Monotone (booleanValue U a (P := P)) := by
  intro b c h p hp
  exact (hp.and ((le_iff U a b c).mp h)).mono fun _ hi => hi.1.trans hi.2

theorem booleanValue_compl (b : Point U a (Completion P)) :
    booleanValue U a (map U a compl b) = (booleanValue U a b)ᶜ :=
  Heyting.Regular.coe_injective (values_compl U a b)

theorem booleanValue_condition (p : Point U a P) :
    booleanValue U a (map U a condition p) = condition p := by
  classical
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro q
  rw [← condition_le_iff,condition_le_booleanValue,mem_condition_iff]
  have simplify : (∀ᶠ i in U, condition (repr U a q i) ≤ repr U a (map U a condition p) i) ↔
      ∀ᶠ i in U, condition (repr U a q i) ≤ condition (repr U a p i) :=
    eventually_congr ((map_repr U a condition p).mono fun _ hi => by rw [hi])
  rw [simplify]
  constructor
  · intro h r hr
    have existsLower := (h.and ((le_iff U a _ _).mp hr)).mono fun i hi =>
      (mem_condition_iff _ _).mp (condition_le_iff.mp hi.1) (repr U a r i) hi.2
    obtain ⟨s,hs⟩ := choose_pair U a r p (fun t v y => y ≤ t ∧ y ≤ v) existsLower
    exact ⟨s,(le_iff U a _ _).mpr (hs.mono fun _ hi => hi.1),(le_iff U a _ _).mpr (hs.mono fun _ hi => hi.2)⟩
  · intro h
    by_contra hn
    have bad := (U.eventually_not.mpr hn).mono fun i hi => by
      rw [condition_le_iff,mem_condition_iff] at hi
      push Not at hi
      exact hi
    obtain ⟨r,hr⟩ := choose_pair U a q p (fun t v r => r ≤ t ∧ ∀ y ≤ r, ¬ y ≤ v) bad
    obtain ⟨s,hs₁,hs₂⟩ := h r ((le_iff U a _ _).mpr (hr.mono fun _ hi => hi.1))
    obtain ⟨i,hi,hl,hm⟩ := (hr.and (((le_iff U a _ _).mp hs₁).and ((le_iff U a _ _).mp hs₂))).exists
    exact hi.2 (repr U a s i) hl hm

theorem booleanValue_projection (π : PartialProjection κ P Q) (hθ : θ.IsRegular)
    (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (hP : ShortInfima κ P) (b : Point U a (Completion Q)) :
    booleanValue U a (map U a π.booleanHom b) =
      (projection U a π hθ fine normal ht hP).booleanHom (booleanValue U a b) := by
  let ρ := projection U a π hθ fine normal ht hP
  have eq (p : ρ.dom) :
      condition p.val ≤ booleanValue U a (map U a π.booleanHom b) ↔
        condition p.val ≤ ρ.booleanHom (booleanValue U a b) := by
    rw [ρ.dom_condition,condition_le_booleanValue,condition_le_booleanValue]
    obtain ⟨z,hz,hy⟩ := (projection_graph U a π hθ fine normal ht hP p.val (ρ.proj p)).mp ⟨p.property,rfl⟩
    rw [← hz,← hy]
    apply eventually_congr
    filter_upwards [map_repr U a (fun x : π.dom => x.val) z,map_repr U a π.booleanHom b,
      map_repr U a π.proj z] with i hp hc hq
    simpa only [hp,hc,hq] using (π.dom_condition (repr U a z i) (repr U a b i))
  have hd (p : Point U a P) : ∃ q ∈ ρ.dom, q ≤ p := by
    obtain ⟨q,hq⟩ := ρ.dense p
    exact ⟨q.val,q.property,hq⟩
  exact le_antisymm (le_of_dense_conditions_le ρ.dom hd fun p => (eq p).mp)
    (le_of_dense_conditions_le ρ.dom hd fun p => (eq p).mpr)

/-- Evaluate a ground string at every location in its image ordinal,
including locations outside the diagonal image of its old domain. -/
def stringBit {V : Type u} (s : V → Completion P) (j : Point U a V) : Completion (Point U a P) :=
  booleanValue U a (map U a s j)

theorem condition_le_stringBit {V : Type u} (s : V → Completion P) (p : Point U a P) (j : Point U a V) :
    condition p ≤ stringBit U a s j ↔ ∀ᶠ i in U, condition (repr U a p i) ≤ s (repr U a j i) := by
  rw [stringBit,condition_le_booleanValue]
  exact eventually_congr ((map_repr U a s j).mono fun _ hi => by rw [hi])

theorem stringBit_local [Nonempty θ.ord.ToType] {V : Type u} (s t : V → Completion P) (p : P)
    (h : ∀ k, condition p ⊓ s k = condition p ⊓ t k) (j : Point U a V) :
    condition (diagonal U a p) ⊓ stringBit U a s j = condition (diagonal U a p) ⊓ stringBit U a t j := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro q
  have hp : repr U a (map U a condition (diagonal U a p)) =ᶠ[U] (fun _ => condition p) :=
    Germ.coe_eq.mp (repr_eq U a _)
  suffices hh : condition q ≤ condition (diagonal U a p) ⊓ stringBit U a s j ↔
      condition q ≤ condition (diagonal U a p) ⊓ stringBit U a t j from
    condition_le_iff.symm.trans (hh.trans condition_le_iff)
  have readCone (hc : condition q ≤ condition (diagonal U a p)) :
      ∀ᶠ i in U, condition (repr U a q i) ≤ condition p := by
    rw [← booleanValue_condition U a (diagonal U a p)] at hc
    exact (((condition_le_booleanValue U a _ _).mp hc).and hp).mono fun _ hi => hi.1.trans_eq hi.2
  constructor
  · intro hh
    have hc := hh.trans inf_le_left
    have hs := (condition_le_stringBit U a s q j).mp (hh.trans inf_le_right)
    exact le_inf hc ((condition_le_stringBit U a t q j).mpr (((readCone hc).and hs).mono
      fun i hi => ((le_inf hi.1 hi.2).trans_eq (h (repr U a j i))).trans inf_le_right))
  · intro hh
    have hc := hh.trans inf_le_left
    have ht := (condition_le_stringBit U a t q j).mp (hh.trans inf_le_right)
    exact le_inf hc ((condition_le_stringBit U a s q j).mpr (((readCone hc).and ht).mono
      fun i hi => ((le_inf hi.1 hi.2).trans_eq (h (repr U a j i)).symm).trans inf_le_right))

end Erdos1172Shioya.UltrapowerStage
