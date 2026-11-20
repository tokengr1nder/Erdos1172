/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCenteredFamily

@[expose] public section

/-!
# Simultaneous named positivity and stationary small losses

Maximality witnesses include actual membership of every finite future
vertex. After freezing the finite witness, regularity recovers that
membership at the stationary refinement itself. Thus positivity and
stationarity hold under one condition, not under unrelated refinements.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3NamedCenteredLoss

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3NamedCenteredFamily
open Erdos1172Part3StationaryDecisions (possible StationaryAt exists_stationary_refinement)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)
open Erdos1172Part3CenteredStationaryLoss (exists_stationary_fiber_of_small)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P]

def MonotoneSmallness (J : RegularName P (RegularName P W2)) : Prop :=
  ∀ p : P, ∀ U V : RegularName P W2,
    (∀ x, (implication U V).holds p x) → J.holds p V → J.holds p U

def finiteFuture (future : RegularName P W2) (t : Finset W2) : RegularName P Unit where
  holds p _ := ∀ b ∈ t, future.holds p b
  persistent hqp h b hb := future.persistent hqp (h b hb)
  of_dense p _ h b hb := by
    apply future.of_dense p b
    intro q hqp
    obtain ⟨s, hsq, hs⟩ := h q hqp
    exact ⟨s, hsq, hs b hb⟩

def goodFuture (J : RegularName P (RegularName P W2)) (H : SimpleGraph W2)
    (rows future : RegularName P W2) (t : Finset W2) : RegularName P W2 :=
  meet future (meet (reindex (finiteFuture future t) (fun _ => ()))
    (reindex J (fun b => meet (rowsMeet H rows t) (ground {x | H.Adj x b}))))

theorem exists_loss_witness (J : RegularName P (RegularName P W2))
    (hmono : MonotoneSmallness J) (H : SimpleGraph W2)
    (rows future : RegularName P W2) (p0 : P) {family : Set W2}
    (hfamily : Maximal (fun family => family ⊆ possible future.holds p0 ∧
      Centered J H rows future p0 family) family)
    (b : W2) (hb : b ∈ possible future.holds p0) (hbnot : b ∉ family) :
    ∃ t : Finset W2, (↑t : Set W2) ⊆ family ∧
      ∃ q : P, q ≤ p0 ∧ (goodFuture J H rows future t).holds q b := by
  classical
  have hnot : ¬Centered J H rows future p0 (insert b family) := by
    intro hcenter
    exact hbnot (hfamily.2 ⟨Set.insert_subset hb hfamily.1.1, hcenter⟩
      (Set.subset_insert _ _) (Set.mem_insert _ _))
  unfold Centered at hnot
  push Not at hnot
  obtain ⟨t, ht, p, hpp0, hpresent, hnotpos⟩ := hnot
  change ¬∀ q : P, q ≤ p → ¬J.holds q (rowsMeet H rows t) at hnotpos
  push Not at hnotpos
  obtain ⟨q, hqp, hsmall⟩ := hnotpos
  have hbt : b ∈ t := by
    by_contra hbt
    have htfamily : (↑t : Set W2) ⊆ family := by
      intro x hx
      rcases Set.mem_insert_iff.mp (ht hx) with rfl | hxf
      · exact (hbt hx).elim
      · exact hxf
    exact (hfamily.1.2 t htfamily p hpp0 hpresent) q hqp hsmall
  have herase : (↑(t.erase b) : Set W2) ⊆ family := by
    intro x hx
    obtain ⟨hxb, hxt⟩ := Finset.mem_erase.mp hx
    exact (Set.mem_insert_iff.mp (ht hxt)).resolve_left hxb
  have hsub : ∀ x, (implication
      (meet (rowsMeet H rows (t.erase b)) (ground {x | H.Adj x b}))
      (rowsMeet H rows t)).holds q x := by
    intro x s hsq hs
    refine ⟨hs.1.1, ?_⟩
    intro c hct
    by_cases hcb : c = b
    · subst c
      exact hs.2
    · exact hs.1.2 c (Finset.mem_erase.mpr ⟨hcb, hct⟩)
  have hloss := hmono q _ _ hsub hsmall
  refine ⟨t.erase b, herase, q, hqp.trans hpp0,
    future.persistent hqp (hpresent b hbt), ?_, hloss⟩
  intro c hc
  exact future.persistent hqp (hpresent c (Finset.mem_erase.mp hc).2)

theorem mk_finite_subsets_lt {family : Set W2} (bound : W2)
    (hbound : ∀ b ∈ family, b < bound) :
    #{t : Finset W2 // (↑t : Set W2) ⊆ family} < ℵ_ 2 := by
  classical
  have hfamilyCard : #family ≤ ℵ_ 1 := by
    have he : #family ≤ #(Set.Iio bound) := Cardinal.mk_le_of_injective
      (f := fun b : family => (⟨b.val, hbound b.val b.property⟩ : Set.Iio bound))
      (fun _ _ h => Subtype.ext (congrArg (fun z : Set.Iio bound => z.val) h))
    exact he.trans (Erdos1172Part3CountableRankClosure.mk_local_le (Embedding.refl W2) bound)
  obtain ⟨e⟩ : Nonempty (family ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hfamilyCard)
  have hcard : #{t : Finset W2 // (↑t : Set W2) ⊆ family} = #(Finset family) :=
    Cardinal.mk_congr (Equiv.finsetSubtypeComm (fun x : W2 => x ∈ family)).symm
  rw [hcard]
  have hle : #(Finset family) ≤ #(Finset W1) :=
    Cardinal.mk_le_of_injective (Finset.map_injective e)
  have hinfinite : Infinite W1 := by
    apply Cardinal.aleph0_le_mk_iff.mp
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph0_le_aleph 1
  rw [Cardinal.mk_finset_of_infinite W1] at hle
  apply hle.trans_lt
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))

/-- Both positivity and the stationary small-loss future are obtained at
the same constructed condition. The extraction law remains explicit. -/
theorem exists_stationary_small_loss (center : CountablyCenteredCode P)
    (J : RegularName P (RegularName P W2)) (hmono : MonotoneSmallness J)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (rows future : RegularName P W2) (p0 : P) (a : W2)
    (hr : ∀ p : P, p ≤ p0 → ∀ x, rows.holds p x → x < a)
    (hf : ∀ p : P, p ≤ p0 → ∀ b, future.holds p b → a < b)
    (hrows : (neg J).holds p0 rows) (hfuture : IsStationary (possible future.holds p0))
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (hcore : BlueExtraction J H rows p0) :
    ∃ p : P, p ≤ p0 ∧ ∃ X out : RegularName P W2,
      (∀ q x, X.holds q x → rows.holds q x) ∧
      (neg J).holds p X ∧ StationaryAt out.holds p ∧
      ∀ q b, out.holds q b → future.holds q b ∧
        J.holds q (meet X (ground {x | H.Adj x b})) := by
  classical
  obtain ⟨family, hfamily⟩ := exists_maximal_centered J H rows future p0 hrows
  obtain ⟨bound, hbound⟩ := centered_bounded center J G H hcompl rows future p0 a
    hr hf hred hblue hcore hfamily.1.1 hfamily.1.2
  let later : Set W2 := possible future.holds p0 ∩ Set.Ioi bound
  have hlater : IsStationary later := stationary_inter_club hfuture
    (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 bound)
  have witness (b : later) : ∃ t : Finset W2, (↑t : Set W2) ⊆ family ∧
      ∃ q : P, q ≤ p0 ∧ (goodFuture J H rows future t).holds q b.val :=
    exists_loss_witness J hmono H rows future p0 hfamily b.val b.property.1
      (fun hb => (hbound b.val hb).asymm b.property.2)
  let Witness := {t : Finset W2 // (↑t : Set W2) ⊆ family}
  have hWitness : #Witness < ℵ_ 2 := mk_finite_subsets_lt bound hbound
  let chosen : later → Witness := fun b => ⟨(witness b).choose, (witness b).choose_spec.1⟩
  obtain ⟨t, ht⟩ := exists_stationary_fiber_of_small hWitness hlater chosen
  let out := goodFuture J H rows future t.val
  have hout : IsStationary (possible out.holds p0) := by
    apply ht.mono
    rintro b ⟨hb, heq⟩
    obtain ⟨q, hqp0, hq⟩ := (witness ⟨b, hb⟩).choose_spec.2
    have hval : (witness ⟨b, hb⟩).choose = t.val := congrArg Subtype.val heq
    rw [hval] at hq
    exact ⟨q, hqp0, hq⟩
  obtain ⟨p, hpp0, hstat⟩ := exists_stationary_refinement center.omegaTwoCC out.holds
    (fun hqp h => out.persistent hqp h) p0 hout
  have hpresent : ∀ b ∈ t.val, future.holds p b := by
    intro b hb
    apply future.of_dense p b
    intro q hqp
    obtain ⟨c, s, hsq, hsc⟩ := (hstat q hqp).nonempty
    exact ⟨s, hsq, hsc.2.1 b hb⟩
  refine ⟨p, hpp0, rowsMeet H rows t.val, out, (fun q x hx => hx.1),
    hfamily.1.2 t.val t.property p hpp0 hpresent, hstat, ?_⟩
  intro q b hq
  exact ⟨hq.1, hq.2.2⟩

end Erdos1172Part3NamedCenteredLoss
