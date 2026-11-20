/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SquareTraceIdeal
public import Erdos1172.Part3FailureFiber

@[expose] public section

/-!
# Stationary square decisions from arbitrary colorings under GCH

Convergent red squares supply finite trace ideals. The derived-ideal
argument gives stationary ordinal-small blue losses, to which the
Hechler decision construction applies. No square or loss hypothesis is
left in the GCH theorem beyond the two forbidden clique alternatives.

The output is a persistent decision system with a stationary possible
future, not a single ground-model square with a stationary common red
future. It does not yet give the omegaOne^(omega+2) core of exact Part 3.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationarySquareBridge

open Erdos1172Part3CoreObjectCode Erdos1172Part3CoreObjectIdeal
open Erdos1172Part3ConvergentSquareCore Erdos1172Part3SquareTraceIdeal
open Erdos1172Part3LocalRedBlock
open Erdos1172Part3StationarySquareDecisions (Square StationarySquareDecisions)
open Erdos1172Part3SquareLossBounds (typeLT_square)
open Erdos1172Part3HechlerOrder (Condition)
open Erdos1172Part3NeighborhoodCode (W2 alephZero_lt_cof_W2)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)
open OrdinalRamsey (HasCliqueOfType)

theorem exists_stationary_square_decisions_of_coreData (hCH : CH) (p0 : Condition)
    {r : Code ↪ W2} {σ : Obj ↪ W2}
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (source domain : Set W2)
    (hd : IsStationary domain) (hds : domain ⊆ source)
    (hgood : ∀ a ∈ domain, GoodCut r σ G H a)
    (hdata : ∀ a ∈ domain, Nonempty (SquareCoreData r G H source a))
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ sys : StationarySquareDecisions G source, sys.start ≤ p0 ∧
      ∀ q i x, sys.clique.decides q i x → x ∈ source := by
  classical
  let data (a : domain) := Classical.choice (hdata a.val a.property)
  let cores (a : W2) : Set W2 := if ha : a ∈ domain then (data ⟨a, ha⟩).core else ∅
  let J (a : W2) := squareTraceSmallness (cores a)
  have hbase : ∀ a ∈ domain, ∀ x : Set W2, Small r G H a x → (J a).small x := by
    intro a ha x hx
    change SquareTraceSmall (cores a) x
    simpa only [cores, dif_pos ha] using (data ⟨a, ha⟩).small_traces x hx
  have hpos : ∀ a ∈ domain, ¬(J a).small (source ∩ Set.Iio a) := by
    intro a ha hsmall
    change typeLT (cores a ∩ (source ∩ Set.Iio a) : Set W2) < _ at hsmall
    have heq : cores a = (data ⟨a, ha⟩).core := dif_pos ha
    have hinter : (data ⟨a, ha⟩).core ∩ (source ∩ Set.Iio a) =
        (data ⟨a, ha⟩).core := Set.inter_eq_left.mpr (data ⟨a, ha⟩).subset_prior
    rw [heq, hinter, (data ⟨a, ha⟩).type_eq] at hsmall
    exact hsmall.false
  obtain ⟨a, had, x, hxp, hxpos, future, hfd, hf, hloss⟩ :=
    Erdos1172Part3TraceDerivedIdeal.exists_positive_stationary_loss G H hcompl source hd
      hgood hbase hpos hred hblue
  have hcore : G.IsClique (cores a) ∧ typeLT (cores a) = (ω_ 1) ^ (2 : Ordinal.{0}) := by
    have heq : cores a = (data ⟨a, had⟩).core := dif_pos had
    rw [heq]
    exact ⟨(data ⟨a, had⟩).clique, (data ⟨a, had⟩).type_eq⟩
  obtain ⟨hxc, hxt⟩ := core_of_square_trace_positive hcore.1 hcore.2 hxpos
  have hle : typeLT Square ≤ typeLT (cores a ∩ x : Set W2) :=
    (typeLT_square.trans hxt.symm).le
  obtain ⟨e⟩ := Ordinal.type_le_iff.mp hle
  let f (z : Square) : W2 := (e.toOrderEmbedding z).val
  have hstrict : StrictMono f := by
    intro z w hzw
    exact e.toOrderEmbedding.strictMono hzw
  have hfc : Set.range f ⊆ cores a ∩ x := by
    rintro _ ⟨z, rfl⟩
    exact (e.toOrderEmbedding z).property
  have hsmall : ∀ b ∈ future,
      typeLT (Set.range f ∩ {v | H.Adj v b} : Set W2) < (ω_ 1) ^ (2 : Ordinal.{0}) := by
    intro b hb
    have h := (hloss b hb).2
    change typeLT (cores a ∩ (x ∩ {v | H.Adj v b}) : Set W2) < _ at h
    apply (Ordinal.type_mono (show Set.range f ∩ {v | H.Adj v b} ⊆
      cores a ∩ (x ∩ {v | H.Adj v b}) from ?_)).trans_lt h
    intro v hv
    exact ⟨(hfc hv.1).1, (hfc hv.1).2, hv.2⟩
  obtain ⟨sys, hsys, hinside⟩ :=
    Erdos1172Part3SquareLossBounds.exists_stationary_square_decisions_of_small_losses
      hCH p0 G H hcompl f hstrict (hxc.subset hfc) future hf
      (fun b hb z => (hxp (hfc ⟨z, rfl⟩).2).2.trans (hloss b hb).1) hsmall
  refine ⟨⟨sys.start, sys.clique, sys.future, sys.persistent,
    fun q b hb => hds (hfd (sys.subset_source q b hb)), sys.stationary, sys.cross⟩,
    hsys, ?_⟩
  intro q i v hv
  exact (hxp (hfc (hinside q i v hv)).2).1

/-- The square and its ordinal-small losses are constructed internally
from local red-block reflection. The caller supplies no core data. -/
theorem exists_stationary_square_decisions (hCH : CH) (p0 : Condition)
    (r : Code ↪ W2) (σ : Obj ↪ W2)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (source : Set W2)
    (hs : IsStationary source) (hsup : ∀ a ∈ source, ErdosRadoCHAsym.IsOmegaOneSup a)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ sys : StationarySquareDecisions G source, sys.start ≤ p0 ∧
      ∀ q i x, sys.clique.decides q i x → x ∈ source := by
  obtain ⟨cl, hcl, hl⟩ := exists_club_local_red_block hCH r σ G H hcompl source hsup hred hblue
  obtain ⟨cg, hcg, hg⟩ := exists_club_goodCut hCH r σ G H
  let domain := source ∩ (cl ∩ cg)
  have hd : IsStationary domain := stationary_inter_club hs
    (hcl.inter alephZero_lt_cof_W2.ne' hcg)
  have hgood : ∀ a ∈ domain, GoodCut r σ G H a :=
    fun a ha => hg a ha.2.2 (hsup a ha.1)
  apply exists_stationary_square_decisions_of_coreData hCH p0 G H hcompl source domain hd
    Set.inter_subset_left hgood _ hred hblue
  intro a ha
  exact squareCoreData_of_local_red_block (hgood a ha) (hl a ha.2.1 ha.1)

/-- GCH supplies both coding embeddings. There is no additional
domination, square-existence, or small-loss premise. -/
theorem exists_stationary_square_decisions_of_gch (hGCH : GCH) (p0 : Condition)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (source : Set W2)
    (hs : IsStationary source) (hsup : ∀ a ∈ source, ErdosRadoCHAsym.IsOmegaOneSup a)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ sys : StationarySquareDecisions G source, sys.start ≤ p0 ∧
      ∀ q i x, sys.clique.decides q i x → x ∈ source :=
  exists_stationary_square_decisions hGCH.toCH p0 (rank hGCH) (objectRank hGCH)
    G H hcompl source hs hsup hred hblue

/-- The first two alternatives are exactly the Part 3 clique targets.
The third is a proved decision-system residual, not a Part 3 solution. -/
theorem part3_targets_or_stationary_square_decisions (hGCH : GCH) (p0 : Condition)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) :
    HasCliqueOfType G ((ω_ 1) ^ ((ω : Ordinal.{0}) + 2) + 2) ∨
      HasCliqueOfType H (ω_ 1 + 2) ∨
        ∃ sys : StationarySquareDecisions G {a | ErdosRadoCHAsym.IsOmegaOneSup a},
          sys.start ≤ p0 ∧ ∀ q i x, sys.clique.decides q i x →
            ErdosRadoCHAsym.IsOmegaOneSup x := by
  classical
  by_cases hred : HasCliqueOfType G (ω_ 2)
  · obtain ⟨s, hs, ht⟩ := hred
    obtain ⟨t, hts, htt⟩ := Ordinal.exists_subset_typeLT_eq s
      (show (ω_ 1) ^ ((ω : Ordinal.{0}) + 2) + 2 ≤ typeLT s by
        rw [ht]
        exact Erdos1172Part3Failure.part3_red_target_lt_omegaTwo.le)
    exact Or.inl ⟨t, hs.subset hts, htt⟩
  by_cases hblue : HasCliqueOfType H (ω_ 1 + 2)
  · exact Or.inr (Or.inl hblue)
  exact Or.inr (Or.inr (exists_stationary_square_decisions_of_gch hGCH p0 G H hcompl
    {a | ErdosRadoCHAsym.IsOmegaOneSup a}
    ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo (fun _ h => h) hred hblue))

end Erdos1172Part3StationarySquareBridge
