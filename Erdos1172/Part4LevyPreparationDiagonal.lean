/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationFiniteGerms

@[expose] public section

/-! # Constant condition germs are exactly the initial-collapse embedding -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
open scoped Erdos1172LevyCollapse
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
local notation "K" => κ.ord.ToType
local notation "L" => θ.ord.ToType

private theorem letter_val (f : K ↪o L) (i : K) (x : Set.Iio i) : (letter f i x).val = f x.val := rfl

theorem mem_graph_relabel (f : K ↪o L) (p : BelowCondition κ) (z : ZFSet.{u}) :
    z ∈ conditionGraph (relabel f p) ↔ ∃ (i : K) (n : ℕ) (hn : n < (p i).entries.length),
      entryTriple (f i).toOrd.val n (f (p i).entries[n].val).toOrd.val = z := by
  rw [mem_conditionGraph_iff]
  constructor
  · rintro ⟨y,n,hlen,hz⟩
    by_cases hy : y ∈ Set.range f
    · obtain ⟨i,rfl⟩ := hy
      have hr := relabel_entries f p i
      have h : n < (p i).entries.length := by simpa only [hr,List.length_map] using hlen
      exact ⟨i,n,h,by simpa only [hr,List.getElem_map,letter_val] using hz⟩
    · rw [relabel_off _ _ hy] at hlen
      exact (Nat.not_lt_zero _ hlen).elim
  · rintro ⟨i,n,h,hz⟩
    have hr := relabel_entries f p i
    have h' : n < ((relabel f p) (f i)).entries.length := by simpa only [hr,List.length_map]
    exact ⟨f i,n,h',by simpa only [hr,List.getElem_map,letter_val] using hz⟩

theorem relabel_eq_of_eqOn {f g : K ↪o L} (p : BelowCondition κ)
    (same : ∀ x ∈ labels p, f x = g x) : relabel f p = relabel g p := by
  apply conditionGraph_injective
  ext z
  rw [mem_graph_relabel,mem_graph_relabel]
  have he (i : K) (n : ℕ) (h : n < (p i).entries.length) :
      entryTriple (f i).toOrd.val n (f (p i).entries[n].val).toOrd.val =
      entryTriple (g i).toOrd.val n (g (p i).entries[n].val).toOrd.val := by
    have hs : i ∈ p.support := DFinsupp.mem_support_iff.mpr (fun hi => by
      rw [hi] at h; exact Nat.not_lt_zero _ h)
    rw [same i (support_mem_labels p hs),same _ (letter_mem_labels p _ (List.getElem_mem h))]
  exact ⟨fun ⟨i,n,h,hz⟩ => ⟨i,n,h,(he i n h).symm.trans hz⟩,fun ⟨i,n,h,hz⟩ =>
    ⟨i,n,h,(he i n h).trans hz⟩⟩

theorem relabel_initial (hk : κ ≤ θ) (p : BelowCondition κ) :
    relabel (initialCoordinate hk).toOrderEmbedding p = zeroExtension hk p := by
  apply DFinsupp.ext
  intro y
  by_cases hy : y ∈ Set.range (initialCoordinate hk)
  · obtain ⟨i,rfl⟩ := hy
    apply Erdos1172Collapse.Condition.ext
    rw [zeroExtension_entries]
    exact relabel_entries (initialCoordinate hk).toOrderEmbedding p i
  · rw [relabel_off _ _ hy,zeroExtension_off _ _ hy]

variable [CardinalInterFilter (U : Filter I) κ]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)

include hf ht in
theorem fiberEmbedding_fixed (x : K) : ∀ᶠ i in U, fiberEmbedding a hk i x = initialCoordinate hk x := by
  induction x using WellFoundedLT.induction with
  | ind x ih =>
    let j := initialCoordinate hk
    have all := (eventually_cardinal_forall (belowAlphabet_cardinal_lt κ x)).mpr (fun t : Set.Iio x => ih t.val t.property)
    filter_upwards [all,hf (j x),fiber_range U a hk ht] with i hi hx hr
    let f := fiberEmbedding a hk i
    have mem : j x ∈ Set.range f := hr ▸ hx
    apply le_antisymm
    · by_contra! h
      obtain ⟨k,hk'⟩ := mem
      have hlt : k < x := f.lt_iff_lt.mp (hk'.symm ▸ h)
      exact hlt.ne (j.injective ((hi ⟨k,hlt⟩).symm.trans hk'))
    · by_contra! h
      obtain ⟨k,hlt,he⟩ := j.lt_apply_iff.mp h
      exact hlt.ne (f.injective ((hi ⟨k,hlt⟩).trans he))

variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]

theorem collapseGermIso_const (p : BelowCondition κ) :
    collapseGermIso U a hk hf hn ht (Germ.const p) = zeroExtension hk p := by
  classical
  have eq := eventually_countable_forall.mpr (fun x : ↥(labels p) => fiberEmbedding_fixed U a hk hf ht x.val)
  obtain ⟨i,hi,hp⟩ := (eq.and (collapseGermIso_spec U a hk hf hn ht (fun _ => p))).exists
  exact hp.symm.trans ((relabel_eq_of_eqOn p (g := (initialCoordinate hk).toOrderEmbedding)
    (fun x hx => hi ⟨x,hx⟩)).trans (relabel_initial hk p))

end Erdos1172LevyCollapse.Preparation
