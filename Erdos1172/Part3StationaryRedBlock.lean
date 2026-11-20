/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TraceDerivedIdeal

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationaryRedBlock

open Erdos1172Part3CoreObjectCode Erdos1172Part3CoreObjectIdeal
open Erdos1172Part3ConvergentCore
open Erdos1172Part3NeighborhoodCode (W2 alephZero_lt_cof_W2)
open Erdos1172Part3CenteredStationaryLoss (exists_stationary_fiber_of_small)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)
open OrdinalRamsey (HasCliqueOfType)

theorem exists_common_red_core_of_countable_losses (hCH : CH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : Set W2) (hc : G.IsClique core) (ht : typeLT core = ω_ 1)
    (a : W2) (hca : core ⊆ Set.Iio a)
    (future : Set W2) (hf : IsStationary future) (hfa : future ⊆ Set.Ioi a)
    (hloss : ∀ b ∈ future, #(core ∩ {x | H.Adj x b} : Set W2) < ℵ_ 1) :
    ∃ c : Set W2, c ⊆ core ∧ G.IsClique c ∧ typeLT c = ω_ 1 ∧
      ∃ later : Set W2, later ⊆ future ∧ IsStationary later ∧
        ∀ b ∈ later, ∀ x ∈ c, x < b ∧ G.Adj x b := by
  classical
  have hcard : #core = ℵ_ 1 := by
    simpa only [Ordinal.card_type, Ordinal.card_omega] using congrArg Ordinal.card ht
  let Profile := {t : Set core // #t ≤ ℵ₀}
  have hpCard : #Profile < ℵ_ 2 := by
    have h := Cardinal.mk_bounded_set_le core ℵ₀
    have hle : #Profile ≤ ℵ_ 1 := by
      simpa only [hcard, max_eq_left (Cardinal.aleph0_le_aleph 1),
        hCH.aleph_one_power_aleph_zero] using h
    exact hle.trans_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let profile (b : future) : Profile := ⟨{x : core | H.Adj x.val b.val}, by
    apply (Cardinal.mk_le_of_injective (f := fun x : {x : core | H.Adj x.val b.val} =>
      (⟨x.val.val, x.val.property, x.property⟩ : (core ∩ {x | H.Adj x b.val} : Set W2)))
      (fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun z : (core ∩ {x | H.Adj x b.val} : Set W2) => z.val) h)))).trans
    exact Cardinal.lt_aleph_one_iff.mp (hloss b.val b.property)⟩
  obtain ⟨p, hp⟩ := exists_stationary_fiber_of_small hpCard hf profile
  let lost : Set W2 := Subtype.val '' p.val
  have hlost : TraceSmall core lost := by
    apply Cardinal.lt_aleph_one_iff.mpr
    exact ((Cardinal.mk_le_mk_of_subset Set.inter_subset_right).trans Cardinal.mk_image_le).trans
      p.property
  have hpositive : ¬TraceSmall core core := by
    simp only [TraceSmall, Set.inter_self, hcard, lt_self_iff_false, not_false_eq_true]
  have hremain := (traceSmallness core).positive_sdiff hpositive hlost
  obtain ⟨hcl, hct⟩ := core_of_trace_positive hc ht hremain
  refine ⟨core ∩ (core \ lost), Set.inter_subset_left, hcl, hct,
    {b | ∃ hb : b ∈ future, profile ⟨b, hb⟩ = p}, fun _ h => h.choose, hp, ?_⟩
  rintro b ⟨hb, heq⟩ x hx
  have hxb : x < b := (hca hx.1).trans (hfa hb)
  refine ⟨hxb, ?_⟩
  rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
  refine ⟨hxb.ne, ?_⟩
  intro hblue
  have hmem : (⟨x, hx.1⟩ : core) ∈ (profile ⟨b, hb⟩).val := hblue
  rw [heq] at hmem
  exact hx.2.2 ⟨⟨x, hx.1⟩, hmem, rfl⟩

structure CoreData (r : Code ↪ W2) (G H : SimpleGraph W2) (source : Set W2) (a : W2) where
  core : Set W2
  subset_prior : core ⊆ source ∩ Set.Iio a
  clique : G.IsClique core
  type_eq : typeLT core = ω_ 1
  small_traces : ∀ x : Set W2, Small r G H a x → TraceSmall core x

theorem exists_stationary_red_block_of_coreData (hCH : CH)
    {r : Code ↪ W2} {σ : Obj ↪ W2}
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (source domain : Set W2)
    (hd : IsStationary domain) (hds : domain ⊆ source)
    (hgood : ∀ a ∈ domain, GoodCut r σ G H a)
    (hdata : ∀ a ∈ domain, Nonempty (CoreData r G H source a))
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ c : Set W2, c ⊆ source ∧ G.IsClique c ∧ typeLT c = ω_ 1 ∧
      ∃ future : Set W2, future ⊆ source ∧ IsStationary future ∧
        ∀ b ∈ future, ∀ x ∈ c, x < b ∧ G.Adj x b := by
  classical
  let data (a : domain) := Classical.choice (hdata a.val a.property)
  let cores (a : W2) : Set W2 := if ha : a ∈ domain then (data ⟨a, ha⟩).core else ∅
  let J (a : W2) := traceSmallness (cores a)
  have hbase : ∀ a ∈ domain, ∀ x : Set W2, Small r G H a x → (J a).small x := by
    intro a ha x hx
    change TraceSmall (cores a) x
    simpa only [cores, dif_pos ha] using (data ⟨a, ha⟩).small_traces x hx
  have hpos : ∀ a ∈ domain, ¬(J a).small (source ∩ Set.Iio a) := by
    intro a ha
    have ht := (data ⟨a, ha⟩).type_eq
    have hc : #(data ⟨a, ha⟩).core = ℵ_ 1 := by
      simpa only [Ordinal.card_type, Ordinal.card_omega] using congrArg Ordinal.card ht
    change ¬TraceSmall (cores a) (source ∩ Set.Iio a)
    simp only [cores, dif_pos ha, TraceSmall,
      Set.inter_eq_left.mpr (data ⟨a, ha⟩).subset_prior, hc, lt_self_iff_false, not_false_eq_true]
  obtain ⟨a, had, x, hxp, hxpos, future, hfd, hf, hloss⟩ :=
    Erdos1172Part3TraceDerivedIdeal.exists_positive_stationary_loss G H hcompl source hd
      hgood hbase hpos hred hblue
  have hcore : G.IsClique (cores a) ∧ typeLT (cores a) = ω_ 1 := by
    have heq : cores a = (data ⟨a, had⟩).core := dif_pos had
    rw [heq]
    exact ⟨(data ⟨a, had⟩).clique, (data ⟨a, had⟩).type_eq⟩
  obtain ⟨hxc, hxt⟩ := core_of_trace_positive hcore.1 hcore.2 hxpos
  have hcount : ∀ b ∈ future, #((cores a ∩ x) ∩ {v | H.Adj v b} : Set W2) < ℵ_ 1 := by
    intro b hb
    have h := (hloss b hb).2
    change #(cores a ∩ (x ∩ {v | H.Adj v b}) : Set W2) < ℵ_ 1 at h
    simpa only [Set.inter_assoc] using h
  obtain ⟨c, hcc, hc, ht, later, hlf, hl, hjoin⟩ :=
    exists_common_red_core_of_countable_losses hCH G H hcompl (cores a ∩ x) hxc hxt a
      (fun _ hv => (hxp hv.2).2) future hf (fun _ hb => (hloss _ hb).1) hcount
  exact ⟨c, fun _ hv => (hxp (hcc hv).2).1, hc, ht,
    later, hlf.trans (hfd.trans hds), hl, hjoin⟩

/-- The first whole-block stationary conclusion is proved from CH and
the two forbidden clique bounds. The source consists of omegaOne cuts. -/
theorem exists_stationary_red_block (hCH : CH) (r : Code ↪ W2) (σ : Obj ↪ W2)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (source : Set W2)
    (hs : IsStationary source) (hsup : ∀ a ∈ source, ErdosRadoCHAsym.IsOmegaOneSup a)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ c : Set W2, c ⊆ source ∧ G.IsClique c ∧ typeLT c = ω_ 1 ∧
      ∃ future : Set W2, future ⊆ source ∧ IsStationary future ∧
        ∀ b ∈ future, ∀ x ∈ c, x < b ∧ G.Adj x b := by
  obtain ⟨cg, hcg, hg⟩ := exists_club_goodCut hCH r σ G H
  obtain ⟨cp, hcp, hp⟩ :=
    Erdos1172Part3RedPredecessorReflection.exists_club_red_predecessor_positive_of_no_blue_target
      r G H hcompl hblue source
  let domain := source ∩ (cg ∩ cp)
  have hd : IsStationary domain := stationary_inter_club hs
    (hcg.inter alephZero_lt_cof_W2.ne' hcp)
  have hgood : ∀ a ∈ domain, GoodCut r σ G H a :=
    fun a ha => hg a ha.2.1 (hsup a ha.1)
  apply exists_stationary_red_block_of_coreData hCH G H hcompl source domain hd
    Set.inter_subset_left hgood _ hred hblue
  intro a ha
  obtain ⟨core, hcore, hc, ht, _, htrace⟩ := exists_cofinal_core_with_small_traces
    (hgood a ha) true ((source ∩ Set.Iio a) ∩ {x | G.Adj x a}) (hp a ha.2.2 ha.1)
    (fun _ hx => hx.1.2) (fun _ hx => hx.2)
  exact ⟨⟨core, hcore.trans Set.inter_subset_left, hc, ht, htrace⟩⟩

end Erdos1172Part3StationaryRedBlock
