/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Flypitch4.ToMathlib
public import Erdos1172.Part4PositiveBooleanCompletion

@[expose] public section

/-! # Truth values for Boolean ultrapowers

Take the completion of the positive pointwise Boolean germs. An indexed
join with a varying index type is computed using sections on large sets.
This lets empty fibers occur. Countable completeness is unnecessary for
these Boolean calculations.
-/

set_option autoImplicit false
noncomputable section

open Filter
open Erdos1172PosetCompletion Erdos1172PositiveBoolean

universe u v w

namespace Erdos1172BooleanUltrapower

variable {I : Type u} {B : Type v}

/-- Pointwise operations give the distributive lattice of germs a Boolean
complement. The order and lattice operations are the existing germ instances. -/
instance germBooleanAlgebra (F : Filter I) [BooleanAlgebra B] :
    BooleanAlgebra (Germ F B) where
  __ := (inferInstance : DistribLattice (Germ F B))
  __ := (inferInstance : BoundedOrder (Germ F B))
  compl := Germ.map (·ᶜ)
  inf_compl_le_bot x := Germ.inductionOn x fun f =>
    Eventually.of_forall (fun i => (show f i ⊓ (f i)ᶜ = ⊥ from inf_compl_eq_bot).le)
  top_le_sup_compl x := Germ.inductionOn x fun f =>
    Eventually.of_forall (fun i => (show f i ⊔ (f i)ᶜ = ⊤ from sup_compl_eq_top).ge)

abbrev Algebra (U : Ultrafilter I) (B : Type v) [BooleanAlgebra B] :=
  Completion (Positive (Germ (U : Filter I) B))

instance algebraNontrivial (U : Ultrafilter I) [NontrivialCompleteBooleanAlgebra B] :
    NontrivialCompleteBooleanAlgebra (Algebra U B) := by
  letI : Nonempty (Positive (Germ (U : Filter I) B)) := ⟨⟨⊤, top_ne_bot⟩⟩
  exact { toCompleteBooleanAlgebra := inferInstance, bot_lt_top := bot_lt_top }

section Cone

variable {A : Type*} [BooleanAlgebra A]

def cone (b : A) : LowerSet (Positive A) :=
  ⟨{p | p.val ≤ b}, fun _ _ hpq hq => (show _ ≤ _ from Subtype.coe_le_coe.mpr hpq).trans hq⟩

private theorem cone_compl (b : A) : cone bᶜ = (cone b)ᶜ := by
  classical
  apply SetLike.ext
  intro p
  change p.val ≤ bᶜ ↔ p ∈ (cone b)ᶜ
  rw [mem_pseudocompl_iff]
  constructor
  · intro hp q hqp hq
    have hqb : q.val ≤ b := hq
    have hqc : q.val ≤ bᶜ := (show q.val ≤ p.val from hqp).trans hp
    exact q.property (bot_unique ((le_inf hqb hqc).trans inf_compl_eq_bot.le))
  · intro hp
    apply le_compl_iff_disjoint_right.mpr
    rw [disjoint_iff_inf_le]
    by_contra h
    have hpos : p.val ⊓ b ≠ ⊥ := fun he => h he.le
    exact hp ⟨p.val ⊓ b, hpos⟩ inf_le_left inf_le_right

theorem cone_regular (b : A) : Heyting.IsRegular (cone b) := by
  change (cone b)ᶜᶜ = cone b
  rw [← cone_compl, ← cone_compl, compl_compl]

def embed (b : A) : Completion (Positive A) := ⟨cone b, cone_regular b⟩

private theorem embed_le_iff {b c : A} : embed b ≤ embed c ↔ b ≤ c := by
  constructor
  · intro h
    by_cases hb : b = ⊥
    · exact hb ▸ bot_le
    · exact h (show (⟨b, hb⟩ : Positive A) ∈ (embed b).val from le_rfl)
  · intro h p hp
    exact (show p.val ≤ b from hp).trans h

private theorem embed_condition (p : Positive A) : embed p.val = condition p := by
  apply Heyting.Regular.coe_injective
  have hcone : LowerSet.Iic p = cone p.val := by
    apply SetLike.ext
    intro q
    rfl
  change cone p.val = (LowerSet.Iic p)ᶜᶜ
  rw [hcone, (cone_regular p.val).eq]

end Cone

section Values

variable [BooleanAlgebra B]

/-- Canonical inclusion of Boolean germs into their regular completion. -/
def germValue (U : Ultrafilter I) (b : Germ (U : Filter I) B) : Algebra U B := embed b

def value (U : Ultrafilter I) (f : I → B) : Algebra U B := germValue U (Germ.ofFun f)

theorem value_le_value_iff (U : Ultrafilter I) {f g : I → B} :
    value U f ≤ value U g ↔ f ≤ᶠ[U] g := embed_le_iff

theorem value_eq_of_eventuallyEq (U : Ultrafilter I) {f g : I → B} (h : f =ᶠ[U] g) :
    value U f = value U g := congrArg (germValue U) (Germ.coe_eq.mpr h)

theorem value_top (U : Ultrafilter I) : value U (fun _ => (⊤ : B)) = ⊤ := by
  apply top_unique
  intro p _
  exact (le_top : p.val ≤ (⊤ : Germ (U : Filter I) B))

theorem value_bot (U : Ultrafilter I) : value U (fun _ => (⊥ : B)) = ⊥ := by
  apply bot_unique
  intro p hp
  exact (p.property (bot_unique (show p.val ≤ (⊥ : Germ (U : Filter I) B) from hp))).elim

theorem value_inf (U : Ultrafilter I) (f g : I → B) :
    value U (fun i => f i ⊓ g i) = value U f ⊓ value U g := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  exact (le_inf_iff : p.val ≤ (Germ.ofFun f : Germ (U : Filter I) B) ⊓ Germ.ofFun g ↔ _)

theorem value_compl (U : Ultrafilter I) (f : I → B) :
    value U (fun i => (f i)ᶜ) = (value U f)ᶜ :=
  Heyting.Regular.coe_injective (cone_compl (Germ.ofFun f : Germ (U : Filter I) B))

theorem value_sup (U : Ultrafilter I) (f g : I → B) :
    value U (fun i => f i ⊔ g i) = value U f ⊔ value U g := by
  apply compl_injective
  rw [← value_compl, compl_sup, ← value_compl, ← value_compl]
  simp only [compl_sup]
  exact value_inf U (fun i => (f i)ᶜ) (fun i => (g i)ᶜ)

end Values

structure LargeSelection (U : Ultrafilter I) (T : I → Type w) where
  carrier : Set I
  large : carrier ∈ (U : Filter I)
  pick : ∀ i : carrier, T i.val

def selected {U : Ultrafilter I} {T : I → Type w} [Bot B]
    (a : ∀ i, T i → B) (s : LargeSelection U T) (i : I) : B := by
  classical
  exact if hi : i ∈ s.carrier then a i (s.pick ⟨i, hi⟩) else ⊥

def selectedTop {U : Ultrafilter I} {T : I → Type w} [Top B]
    (a : ∀ i, T i → B) (s : LargeSelection U T) (i : I) : B := by
  classical
  exact if hi : i ∈ s.carrier then a i (s.pick ⟨i, hi⟩) else ⊤

section Joins

variable [CompleteBooleanAlgebra B]

/-- Every positive germ below a varying join meets a term chosen on a
large domain. Only that domain needs to have nonempty fibers. -/
private theorem exists_selection (U : Ultrafilter I) (T : I → Type w) (a : ∀ i, T i → B)
    (f : I → B) (hpos : ∀ᶠ i in U, f i ≠ ⊥) (hle : ∀ᶠ i in U, f i ≤ ⨆ t, a i t) :
    ∃ s : LargeSelection U T, ∀ᶠ i in U, f i ⊓ selected a s i ≠ ⊥ := by
  classical
  let S := {i | ∃ t, f i ⊓ a i t ≠ ⊥}
  have hS : S ∈ (U : Filter I) := (hpos.and hle).mono fun i h => by
    by_contra hn
    apply h.1
    have hzero : (⨆ t, f i ⊓ a i t) = ⊥ := iSup_eq_bot.mpr fun t =>
      by_contra fun ht => hn ⟨t, ht⟩
    rwa [← inf_iSup_eq, inf_eq_left.mpr h.2] at hzero
  let s : LargeSelection U T := ⟨S, hS, fun i => i.property.choose⟩
  refine ⟨s, ?_⟩
  filter_upwards [hS] with i hi
  simpa only [selected, s, dif_pos hi] using hi.choose_spec

theorem value_iSup (U : Ultrafilter I) (T : I → Type w) (a : ∀ i, T i → B) :
    value U (fun i => ⨆ t, a i t) =
      ⨆ s : LargeSelection U T, value U (selected a s) := by
  classical
  let J := value U (fun i => ⨆ t, a i t)
  let R := ⨆ s : LargeSelection U T, value U (selected a s)
  apply le_antisymm
  · change J ≤ R
    by_contra hn
    have hpos : J ⊓ Rᶜ ≠ ⊥ := fun h => hn (by
      have hd : J ≤ (Rᶜ)ᶜ := le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)
      simpa only [compl_compl] using hd)
    obtain ⟨q, hq⟩ := exists_condition_le hpos
    obtain ⟨f, hf⟩ : ∃ f : I → B, Germ.ofFun f = q.val := Germ.inductionOn q.val fun f => ⟨f, rfl⟩
    have hqf : value U f = condition q := by
      change embed (Germ.ofFun f : Germ (U : Filter I) B) = condition q
      rw [hf, embed_condition]
    have hnon : ∀ᶠ i in U, f i ≠ ⊥ := U.eventually_not.mpr fun h =>
      q.property (hf.symm.trans (Germ.coe_eq.mpr h))
    have hle := (value_le_value_iff U).mp (hqf.le.trans (hq.trans inf_le_left))
    obtain ⟨s, hs⟩ := exists_selection U T a f hnon hle
    have hbad : value U (fun i => f i ⊓ selected a s i) ≤ ⊥ := by
      rw [value_inf, hqf]
      exact (inf_le_inf (hq.trans inf_le_right) (show value U (selected a s) ≤ R from
          le_iSup (fun t : LargeSelection U T => value U (selected a t)) s)).trans compl_inf_eq_bot.le
    rw [← value_bot U] at hbad
    exact (U.eventually_not.mp hs) (((value_le_value_iff U).mp hbad).mono fun _ h => bot_unique h)
  · apply iSup_le
    intro s
    apply (value_le_value_iff U).mpr
    filter_upwards [s.large] with i hi
    simp only [selected, dif_pos hi]
    exact le_iSup _ _

theorem value_iInf (U : Ultrafilter I) (T : I → Type w) (a : ∀ i, T i → B) :
    value U (fun i => ⨅ t, a i t) =
      ⨅ s : LargeSelection U T, value U (selectedTop a s) := by
  classical
  apply compl_injective
  rw [← value_compl, compl_iInf]
  simp only [compl_iInf]
  rw [value_iSup U T (fun i t => (a i t)ᶜ)]
  apply iSup_congr
  intro s
  rw [← value_compl]
  apply value_eq_of_eventuallyEq
  filter_upwards [s.large] with i hi
  simp only [selected, selectedTop, dif_pos hi]

end Joins

end Erdos1172BooleanUltrapower
