/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Statement
public import Erdos1172.Part4GroundElementaryEmbedding
public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

/-!
# The fine seed and indexed graphs in a ground ultrapower

Fineness puts every prescribed index into the seed. Normality makes each
index chosen below the seed constant on a measure-one set. Together they
compute the complete collapsed range of a pointwise family. In particular
the diagonal range on an ordinal, and graphs of arbitrary target values
indexed by that range, are sets in the target class.
-/

set_option autoImplicit false
noncomputable section
open Filter
universe u

namespace Erdos1172GroundUltrapower

variable {I J : Type u} (U : Ultrafilter I)

private theorem select_normal_index (a : I → Set J) (hn : NormalOn U a) (E : I → J → Prop)
    (h : ∀ᶠ i in U, ∃ ξ, ξ ∈ a i ∧ E i ξ) : ∃ ξ, ∀ᶠ i in U, ξ ∈ a i ∧ E i ξ := by
  classical
  obtain ⟨i₀, ξ₀, _⟩ := h.exists
  let f (i : I) := if hi : ∃ ξ, ξ ∈ a i ∧ E i ξ then hi.choose else ξ₀
  have hs : ∀ᶠ i in U, f i ∈ a i ∧ E i (f i) :=
    h.mono fun i hi => by simpa only [f, dif_pos hi] using hi.choose_spec
  obtain ⟨ξ, hξ⟩ := hn f (hs.mono fun _ hi => hi.1)
  exact ⟨ξ, (hs.and hξ).mono fun _ hi => hi.2 ▸ hi.1⟩

variable [CountableInterFilter (U : Filter I)]

/-- Pointwise collect all selected representatives into one set. -/
def fineFamilyCode (a : I → Set J) (v : J → I → ZFSet.{u}) : Ground U :=
  Germ.ofFun fun i => ZFSet.range (fun ξ : a i => v ξ.val i)

theorem collapse_fineFamilyCode (a : I → Set J) (hf : FineOn U a) (hn : NormalOn U a)
    (v : J → I → ZFSet.{u}) :
    collapse U (fineFamilyCode U a v) = ZFSet.range (fun ξ => collapse U (Germ.ofFun (v ξ))) := by
  apply ZFSet.ext
  intro x
  rw [mem_collapse_iff, ZFSet.mem_range]
  constructor
  · rintro ⟨z, hz, rfl⟩
    induction z using Germ.inductionOn with
    | _ Z =>
      have hs : ∀ᶠ i in U, Z i ∈ ZFSet.range (fun ξ : a i => v ξ.val i) := hz
      have hsel : ∀ᶠ i in U, ∃ ξ, ξ ∈ a i ∧ v ξ i = Z i := hs.mono fun i hi => by
        obtain ⟨ξ, heq⟩ := ZFSet.mem_range.mp hi
        exact ⟨ξ.val, ξ.property, heq⟩
      obtain ⟨ξ, hξ⟩ := select_normal_index U a hn _ hsel
      exact ⟨ξ, congrArg (collapse U) (Germ.coe_eq.mpr (hξ.mono fun _ hi => hi.2))⟩
  · rintro ⟨ξ, rfl⟩
    refine ⟨Germ.ofFun (v ξ), ?_, rfl⟩
    exact (hf ξ).mono fun i hi => ZFSet.mem_range.mpr ⟨⟨ξ, hi⟩, rfl⟩

/-- Arbitrary externally indexed families of target sets have a target range. -/
theorem targetClass_fine_range (a : I → Set J) (hf : FineOn U a) (hn : NormalOn U a)
    (X : J → ZFSet.{u}) (hX : ∀ ξ, X ξ ∈ targetClass U) : ZFSet.range X ∈ targetClass U := by
  have rep (ξ : J) : ∃ f : I → ZFSet.{u}, collapse U (Germ.ofFun f) = X ξ := by
    obtain ⟨z, hz⟩ := hX ξ
    obtain ⟨f, he⟩ : ∃ f : I → ZFSet.{u}, Germ.ofFun f = z :=
      Germ.inductionOn z (fun f => ⟨f, rfl⟩)
    exact ⟨f, (congrArg (collapse U) he).trans hz⟩
  choose v hv using rep
  exact ⟨fineFamilyCode U a v, (collapse_fineFamilyCode U a hf hn v).trans
    (congrArg ZFSet.range (funext hv))⟩

theorem collapse_doubleton (f g : I → ZFSet.{u}) :
    collapse U (Germ.ofFun (fun i => ({f i, g i} : ZFSet.{u}))) =
      ({collapse U (Germ.ofFun f), collapse U (Germ.ofFun g)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro x
  rw [mem_collapse_iff, ZFSet.mem_pair]
  constructor
  · rintro ⟨z, hz, rfl⟩
    induction z using Germ.inductionOn with
    | _ Z =>
      have h : ∀ᶠ i in U, Z i ∈ ({f i, g i} : ZFSet.{u}) := hz
      rcases U.eventually_or.mp (h.mono fun _ hi => ZFSet.mem_pair.mp hi) with h | h
      · exact Or.inl (congrArg (collapse U) (Germ.coe_eq.mpr h))
      · exact Or.inr (congrArg (collapse U) (Germ.coe_eq.mpr h))
  · rintro (rfl | rfl)
    · exact ⟨Germ.ofFun f, Eventually.of_forall fun i => ZFSet.mem_pair.mpr (Or.inl rfl), rfl⟩
    · exact ⟨Germ.ofFun g, Eventually.of_forall fun i => ZFSet.mem_pair.mpr (Or.inr rfl), rfl⟩

theorem collapse_ordered_pair (f g : I → ZFSet.{u}) :
    collapse U (Germ.ofFun (fun i => ZFSet.pair (f i) (g i))) =
      ZFSet.pair (collapse U (Germ.ofFun f)) (collapse U (Germ.ofFun g)) := by
  have hs : collapse U (Germ.ofFun (fun i => ({f i} : ZFSet.{u}))) =
      ({collapse U (Germ.ofFun f)} : ZFSet.{u}) := by
    simpa only [ZFSet.pair_eq_singleton] using collapse_doubleton U f f
  unfold ZFSet.pair
  rw [collapse_doubleton, collapse_doubleton, hs]

variable (θ : Cardinal.{u})

def fineSeed (a : I → Set θ.ord.ToType) : ZFSet.{u} :=
  collapse U (fineFamilyCode U a (fun ξ _ => ξ.toOrd.val.toZFSet))

theorem fineSeed_mem_targetClass (a : I → Set θ.ord.ToType) : fineSeed U θ a ∈ targetClass U :=
  ⟨_, rfl⟩

theorem fineSeed_eq_diagonal_range (a : I → Set θ.ord.ToType)
    (hf : FineOn U a) (hn : NormalOn U a) :
    fineSeed U θ a = ZFSet.range (fun ξ : θ.ord.ToType => diagonal U ξ.toOrd.val.toZFSet) :=
  collapse_fineFamilyCode U a hf hn _

theorem mem_fineSeed_iff (a : I → Set θ.ord.ToType) (hf : FineOn U a) (hn : NormalOn U a)
    (x : ZFSet.{u}) : x ∈ fineSeed U θ a ↔
      ∃ ξ : θ.ord.ToType, diagonal U ξ.toOrd.val.toZFSet = x := by
  rw [fineSeed_eq_diagonal_range U θ a hf hn, ZFSet.mem_range]

/-- The seed itself belongs to the diagonal image of the powerset of the
ordinal. In particular this membership uses the actual small subsets
that represent the seed at each index. -/
theorem fineSeed_mem_diagonal_powerset (a : I → Set θ.ord.ToType) :
    fineSeed U θ a ∈ diagonal U (ZFSet.powerset θ.ord.toZFSet) := by
  apply (seed_mem_diagonal U _ _).mpr
  apply Eventually.of_forall
  intro i
  apply ZFSet.mem_powerset.mpr
  intro x hx
  obtain ⟨ξ, rfl⟩ := ZFSet.mem_range.mp hx
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr ξ.val.toOrd.property

/-- This actual target graph has domain the diagonal image of the ordinal
and value `collapse U (g ξ)` at the corresponding diagonal index. -/
def fineSeedGraph (g : θ.ord.ToType → Ground U) : ZFSet.{u} :=
  ZFSet.range fun ξ : θ.ord.ToType => ZFSet.pair (diagonal U ξ.toOrd.val.toZFSet) (collapse U (g ξ))

theorem fineSeedGraph_mem_targetClass (a : I → Set θ.ord.ToType) (hf : FineOn U a)
    (hn : NormalOn U a) (g : θ.ord.ToType → Ground U) : fineSeedGraph U θ g ∈ targetClass U := by
  apply targetClass_fine_range U a hf hn
  intro ξ
  obtain ⟨v, hv⟩ : ∃ v : I → ZFSet.{u}, Germ.ofFun v = g ξ :=
    Germ.inductionOn (g ξ) (fun v => ⟨v, rfl⟩)
  rw [← hv]
  exact ⟨_, collapse_ordered_pair U (fun _ => ξ.toOrd.val.toZFSet) v⟩

theorem fineSeedGraph_value (g : θ.ord.ToType → Ground U) (ξ : θ.ord.ToType) (y : ZFSet.{u}) :
    ZFSet.pair (diagonal U ξ.toOrd.val.toZFSet) y ∈ fineSeedGraph U θ g ↔ y = collapse U (g ξ) := by
  constructor
  · intro hy
    obtain ⟨η, he⟩ := ZFSet.mem_range.mp hy
    have hpair := ZFSet.pair_inj.mp he
    have hd := collapse_injective U hpair.1
    have ho := Ordinal.toZFSet_injective (Germ.const_inj.mp hd)
    have hξ : η = ξ := Ordinal.ToType.mk.symm.injective (Subtype.ext ho)
    simpa only [hξ] using hpair.2.symm
  · rintro rfl
    exact ZFSet.mem_range_self ξ

/-- Fineness and normality restrict to any subfamily of the index set,
including the empty subfamily. -/
theorem targetClass_subindexed_range {K : Type u} (a : I → Set J) (hf : FineOn U a)
    (hn : NormalOn U a) (j : K ↪ J) (X : K → ZFSet.{u}) (hX : ∀ k, X k ∈ targetClass U) :
    ZFSet.range X ∈ targetClass U := by
  let b : I → Set K := fun i => j ⁻¹' a i
  have hfb : FineOn U b := fun k => hf (j k)
  have hnb : NormalOn U b := by
    intro f h
    obtain ⟨ξ, hξ⟩ := hn (fun i => j (f i)) h
    obtain ⟨i₀, h₀⟩ := hξ.exists
    exact ⟨f i₀, hξ.mono fun i hi => j.injective (hi.trans h₀.symm)⟩
  exact targetClass_fine_range U b hfb hnb X hX

private theorem ordinal_range (α : Ordinal.{u}) :
    ZFSet.range (fun ξ : α.ToType => ξ.toOrd.val.toZFSet) = α.toZFSet := by
  ext x
  rw [ZFSet.mem_range, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ.toOrd.val, ξ.toOrd.property, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨Ordinal.ToType.mk ⟨β, hβ⟩,
      congrArg (fun z : Set.Iio α => z.val.toZFSet) (Ordinal.ToType.mk.symm_apply_apply _)⟩

/-- The actual ground ordinals through θ belong to the target class.
This uses transfinite induction and indexed ranges inside the class. -/
theorem ordinal_mem_fine_targetClass (a : I → Set θ.ord.ToType) (hf : FineOn U a)
    (hn : NormalOn U a) (α : Ordinal.{u}) : α ≤ θ.ord → α.toZFSet ∈ targetClass U := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro hα
    let j : α.ToType ↪ θ.ord.ToType :=
      (Classical.choice (show Nonempty (α.ToType ≤i θ.ord.ToType) from
        Ordinal.type_le_iff.mp (by simpa only [Ordinal.type_toType] using hα))).toRelEmbedding.toEmbedding
    rw [← ordinal_range α]
    exact targetClass_subindexed_range U a hf hn j _
      (fun ξ => ih ξ.toOrd.val ξ.toOrd.property (ξ.toOrd.property.le.trans hα))

theorem orderedPair_mem_targetClass {x y : ZFSet.{u}} (hx : x ∈ targetClass U)
    (hy : y ∈ targetClass U) : ZFSet.pair x y ∈ targetClass U := by
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  induction v, w using Germ.inductionOn₂ with
  | _ f g => exact ⟨_, collapse_ordered_pair U f g⟩

/-- Closure under actual ground functions of length θ with arbitrary
target values. The domain here is the original ordinal θ. -/
theorem fine_targetClass_closed_sequences (a : I → Set θ.ord.ToType) (hf : FineOn U a)
    (hn : NormalOn U a) (S F : ZFSet.{u}) (hF : ZFSet.IsFunc θ.ord.toZFSet S F)
    (hvalues : ∀ (ξ : θ.ord.ToType) y, ZFSet.pair ξ.toOrd.val.toZFSet y ∈ F →
      y ∈ targetClass U) : F ∈ targetClass U := by
  let l := fun ξ : θ.ord.ToType => ξ.toOrd.val.toZFSet
  have hdom (ξ : θ.ord.ToType) : l ξ ∈ θ.ord.toZFSet :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr ξ.toOrd.property
  choose v hv using fun ξ : θ.ord.ToType => (hF.2 (l ξ) (hdom ξ)).exists
  have hgraph : ZFSet.range (fun ξ => ZFSet.pair (l ξ) (v ξ)) = F := by
    ext z
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨ξ, rfl⟩
      exact hv ξ
    · intro hz
      obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hF.1 hz)
      rw [← ordinal_range θ.ord, ZFSet.mem_range] at hx
      obtain ⟨ξ, rfl⟩ := hx
      exact ⟨ξ, congrArg (ZFSet.pair (l ξ)) ((hF.2 (l ξ) (hdom ξ)).unique (hv ξ) hz)⟩
  rw [← hgraph]
  exact targetClass_fine_range U a hf hn _
    (fun ξ => orderedPair_mem_targetClass U
      (ordinal_mem_fine_targetClass U θ a hf hn _ ξ.toOrd.property.le) (hvalues ξ (v ξ) (hv ξ)))

end Erdos1172GroundUltrapower
