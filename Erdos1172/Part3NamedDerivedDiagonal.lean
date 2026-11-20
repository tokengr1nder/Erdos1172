/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedDerivedLoss

@[expose] public section

/-!
# The all-small branch for a condition-dependent source

If every source-present cut is derived-small below a fixed starting
condition, diagonal reflection constructs an earlier actual cut with
stationarily preserved small losses. No intersection indexed by all
conditions and no stationary ground subset of actual members is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedDerivedDiagonal

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3GuardedTraceFamily (priorSource)
open Erdos1172Part3NamedBlueDerivedIdeal
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3StationaryDecisions (possible StationaryAt OmegaTwoCC exists_stationary_refinement)
open Erdos1172Part3NamedCenteredLoss (MonotoneSmallness)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open Erdos1172Part3TwoSuccessorBootstrap (isClub_diagonalInter)

variable {P I : Type} [Preorder P] [LinearOrder I] {G H : SimpleGraph W2}

noncomputable def cutFuture (H : SimpleGraph W2) (D : RegularName P W2)
    (J : W2 → RegularName P (RegularName P W2)) (source : RegularName P W2)
    (a : W2) : RegularName P W2 :=
  meet D (meet (ground {b | a < b})
    (reindex (J a) (fun b => fiber H b (priorSource source a))))

theorem exists_loss_of_all_blueSmall_general (hCH : CH) (hcc : OmegaTwoCC P) (hI : #I ≤ ℵ_ 1)
    (r : Code P I G ↪ W2) (σ : NiceCliqueName P I W2 G ↪ W2)
    (H : SimpleGraph W2) (source D : RegularName P W2)
    (J : W2 → RegularName P (RegularName P W2))
    (hmono : ∀ a, MonotoneSmallness (J a))
    (hsup : ∀ p a, D.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : P) (hstat : StationaryAt D.holds p0)
    (hext : ∀ a p, p ≤ p0 → D.holds p a →
      (blueSmallName r H D J a).holds p (priorSource source a)) :
    ∃ a : W2, ∃ p : P, p ≤ p0 ∧ D.holds p a ∧
      StationaryAt (cutFuture H D J source a).holds p := by
  classical
  let W (a : W2) := meet (cutFuture H D J source a) (reindex D (fun _ => a))
  by_contra hnone
  have hnonstat (a : W2) : ¬IsStationary (possible (W a).holds p0) := by
    intro h
    obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement hcc (W a).holds
      (fun hqp hq => (W a).persistent hqp hq) p0 h
    have hDa : D.holds p a := by
      apply D.of_dense p a
      intro q hqp
      obtain ⟨b, s, hsq, hs⟩ := (hp q hqp).nonempty
      exact ⟨s, hsq, hs.2⟩
    apply hnone
    refine ⟨a, p, hpp0, hDa, ?_⟩
    intro q hqp
    apply (hp q hqp).mono
    rintro b ⟨s, hsq, hs⟩
    exact ⟨s, hsq, hs.1⟩
  choose clubs hclubs hdisjoint using fun a => not_isStationary_iff.mp (hnonstat a)
  let diagonal := Set.diagonalInter clubs
  have hdiagonal : IsClub diagonal := isClub_diagonalInter clubs hclubs
  let Z := meet D (ground diagonal)
  obtain ⟨reflectClub, hreflectClub, hreflect⟩ := exists_club_goodCut hCH hcc hI G H r σ Z
  obtain ⟨b, hbpossible, hbdiag, hbreflect⟩ := (hstat p0 le_rfl)
    (hdiagonal.inter alephZero_lt_cof_W2.ne' hreflectClub)
  obtain ⟨p, hpp0, hDb⟩ := hbpossible
  have hg : GoodCut r σ H Z b := hreflect b hbreflect (hsup p b hDb)
  have hpositive := source_not_small hg p (show Z.holds p b from ⟨hDb, hbdiag⟩)
  apply hpositive p le_rfl
  apply smallName_mono_set (V := support H D J b (priorSource source b)) ?_
    (hext b p hpp0 hDb)
  intro a hab q hqp hZa
  refine ⟨hab, hZa.1, ?_⟩
  intro s hsq hsmall
  have hJ : (J a).holds s (fiber H b (priorSource source a)) := by
    apply hmono a s (fiber H b (priorSource source a))
      (blueSection H b a (priorSource source b)) ?_ hsmall
    intro x t hts ht
    exact ⟨⟨ht.1.1, ht.1.2.trans hab⟩, ht.2, ht.1.2⟩
  have hW : (W a).holds s b :=
    ⟨⟨D.persistent (hsq.trans hqp) hDb, hab, hJ⟩, D.persistent hsq hZa.1⟩
  exact Set.disjoint_left.mp (hdisjoint a)
    ⟨s, (hsq.trans hqp).trans hpp0, hW⟩ (hbdiag a hab)

theorem exists_loss_of_all_blueSmall (hCH : CH) (hcc : OmegaTwoCC P)
    (r : Code P W1 G ↪ W2) (σ : NiceCliqueName P W1 W2 G ↪ W2)
    (H : SimpleGraph W2) (source D : RegularName P W2)
    (J : W2 → RegularName P (RegularName P W2))
    (hmono : ∀ a, MonotoneSmallness (J a))
    (hsup : ∀ p a, D.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : P) (hstat : StationaryAt D.holds p0)
    (hext : ∀ a p, p ≤ p0 → D.holds p a →
      (blueSmallName r H D J a).holds p (priorSource source a)) :
    ∃ a : W2, ∃ p : P, p ≤ p0 ∧ D.holds p a ∧
      StationaryAt (cutFuture H D J source a).holds p :=
  exists_loss_of_all_blueSmall_general hCH hcc
    (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
    r σ H source D J hmono hsup p0 hstat hext

end Erdos1172Part3NamedDerivedDiagonal
