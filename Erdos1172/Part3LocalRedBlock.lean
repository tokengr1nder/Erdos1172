/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3StationaryRedBlock

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3LocalRedBlock

open Erdos1172Part3CoreObjectCode Erdos1172Part3StationaryRedBlock
open Erdos1172Part3NeighborhoodCode (W2 alephZero_lt_cof_W2)
open Erdos1172Part3RedPredecessorReflection (stationaryPressingDown)
open OrdinalRamsey (HasCliqueOfType)

/-- Every local named neighborhood contains a whole locally named red
omegaOne block, joined to the cut. Object locality is an explicit part
of this conclusion, and is proved by stationary reflection below. -/
def LocalRedBlock (r : Code ↪ W2) (σ : Obj ↪ W2) (G H : SimpleGraph W2)
    (source : Set W2) (a : W2) : Prop :=
  ∀ c : Code, r c < a → a ∈ eval G H c →
    ∃ block : Obj, σ block < a ∧ block.val ⊆ source ∩ eval G H c ∧
      G.IsClique block.val ∧ typeLT block.val = ω_ 1 ∧ a ∈ afterRed G block

theorem exists_club_local_red_block (hCH : CH) (r : Code ↪ W2) (σ : Obj ↪ W2)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (source : Set W2)
    (hsup : ∀ a ∈ source, ErdosRadoCHAsym.IsOmegaOneSup a)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, a ∈ source →
      LocalRedBlock r σ G H source a := by
  classical
  let bad := {a | a ∈ source ∧ ¬LocalRedBlock r σ G H source a}
  have witness (a : bad) : ∃ c : Code, r c < a.val ∧ a.val ∈ eval G H c ∧
      ¬∃ block : Obj, σ block < a.val ∧ block.val ⊆ source ∩ eval G H c ∧
        G.IsClique block.val ∧ typeLT block.val = ω_ 1 ∧ a.val ∈ afterRed G block := by
    have h := a.property.2
    unfold LocalRedBlock at h
    push Not at h
    obtain ⟨c, hc, hac, hnone⟩ := h
    refine ⟨c, hc, hac, ?_⟩
    push Not
    exact hnone
  have hnonstat : ¬IsStationary bad := by
    intro hbad
    let chosen (a : W2) : Code := if ha : a ∈ bad then (witness ⟨a, ha⟩).choose
      else SmallUnionCode.empty
    have hspec (a : W2) (ha : a ∈ bad) : r (chosen a) < a ∧ a ∈ eval G H (chosen a) ∧
        ¬∃ block : Obj, σ block < a ∧ block.val ⊆ source ∩ eval G H (chosen a) ∧
          G.IsClique block.val ∧ typeLT block.val = ω_ 1 ∧ a ∈ afterRed G block := by
      simpa only [chosen, dif_pos ha] using (witness ⟨a, ha⟩).choose_spec
    obtain ⟨value, hstat⟩ := stationaryPressingDown bad (fun a => r (chosen a)) hbad
      (fun a ha => (hspec a ha).1)
    let fiber := {a | a ∈ bad ∧ r (chosen a) = value}
    obtain ⟨core, hcore, hc, ht, future, hfuture, hf, hjoin⟩ :=
      exists_stationary_red_block hCH r σ G H hcompl fiber hstat
        (fun a ha => hsup a ha.1.1) hred hblue
    have hcard : #core ≤ ℵ_ 1 := by
      have heq : #core = ℵ_ 1 := by
        simpa only [Ordinal.card_type, Ordinal.card_omega] using congrArg Ordinal.card ht
      exact heq.le
    let block : Obj := ⟨core, hcard⟩
    obtain ⟨a, haf, hlocal⟩ := hf
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 (σ block))
    have habad : a ∈ bad := (hfuture haf).1
    apply (hspec a habad).2.2
    refine ⟨block, hlocal, ?_, hc, ht, hjoin a haf⟩
    intro x hx
    have hxf := hcore hx
    have hcode : chosen x = chosen a := r.injective (hxf.2.trans (hfuture haf).2.symm)
    refine ⟨hxf.1.1, ?_⟩
    rw [← hcode]
    exact (hspec x hxf.1).2.1
  obtain ⟨club, hclub, hdisjoint⟩ := not_isStationary_iff.mp hnonstat
  refine ⟨club, hclub, ?_⟩
  intro a hac has
  by_contra h
  exact Set.disjoint_left.mp hdisjoint ⟨has, h⟩ hac

end Erdos1172Part3LocalRedBlock
