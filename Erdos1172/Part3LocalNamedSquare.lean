/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CliqueNameCoding
public import Erdos1172.Part3StationarySquareBridge

@[expose] public section

/-!
# Local reflection of small square names

At club many cuts, every locally coded starting condition and ground
neighborhood has a locally coded square name supported below the cut.
A strengthening makes all its point decisions red-adjacent to the cut.
The strengthening itself is not asserted to have a local condition code.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3LocalNamedSquare

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerOrder (Condition emptyCondition)
open Erdos1172Part3CoreObjectCode (Code eval)
open Erdos1172Part3CliqueNameCoding
open Erdos1172Part3NiceCliqueNames (exists_nice_clique_name)
open Erdos1172Part3RedPredecessorReflection (stationaryPressingDown)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

def JoinedAt {G : SimpleGraph W2} (N : SquareName G) (p : Condition) (a : W2) : Prop :=
  ∀ q : Condition, q ≤ p → ∀ i x, N.toClique.decides q i x → x < a ∧ G.Adj x a

theorem joinedAt_mono {G : SimpleGraph W2} {N : SquareName G}
    {p q : Condition} {a : W2} (h : JoinedAt N p a) (hqp : q ≤ p) :
    JoinedAt N q a := fun r hr => h r (hr.trans hqp)

/-- Locality applies to the name and the starting condition. In
particular, the concluding strengthening has no asserted code bound. -/
def LocalNamedSquare (π : Condition ↪ W2) (r : Code ↪ W2)
    {G : SimpleGraph W2} (σ : SquareName G ↪ W2) (H : SimpleGraph W2)
    (source : Set W2) (a : W2) : Prop :=
  ∀ p : Condition, π p < a → ∀ c : Code, r c < a → a ∈ eval G H c →
    ∃ N : SquareName G, σ N < a ∧ N.values ⊆ (source ∩ eval G H c) ∩ Set.Iio a ∧
      ∃ q : Condition, q ≤ p ∧ JoinedAt N q a

theorem exists_club_local_named_square (hGCH : GCH)
    (π : Condition ↪ W2) (r : Code ↪ W2)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (σ : SquareName G ↪ W2)
    (source : Set W2) (hsup : ∀ a ∈ source, ErdosRadoCHAsym.IsOmegaOneSup a)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, a ∈ source →
      LocalNamedSquare π r σ H source a := by
  classical
  let bad : Set W2 := {a | a ∈ source ∧ ¬LocalNamedSquare π r σ H source a}
  have witness (a : bad) : ∃ p : Condition, π p < a.val ∧ ∃ c : Code,
      r c < a.val ∧ a.val ∈ eval G H c ∧
        ¬∃ N : SquareName G, σ N < a.val ∧
          N.values ⊆ (source ∩ eval G H c) ∩ Set.Iio a.val ∧
            ∃ q : Condition, q ≤ p ∧ JoinedAt N q a.val := by
    have h := a.property.2
    unfold LocalNamedSquare at h
    push Not at h
    obtain ⟨p, hp, c, hc, hac, hnone⟩ := h
    refine ⟨p, hp, c, hc, hac, ?_⟩
    push Not
    exact hnone
  let start (a : W2) : Condition := if ha : a ∈ bad then (witness ⟨a, ha⟩).choose
    else emptyCondition
  let code (a : W2) : Code := if ha : a ∈ bad then (witness ⟨a, ha⟩).choose_spec.2.choose
    else SmallUnionCode.empty
  have hspec (a : W2) (ha : a ∈ bad) :
      π (start a) < a ∧ r (code a) < a ∧ a ∈ eval G H (code a) ∧
        ¬∃ N : SquareName G, σ N < a ∧
          N.values ⊆ (source ∩ eval G H (code a)) ∩ Set.Iio a ∧
            ∃ q : Condition, q ≤ start a ∧ JoinedAt N q a := by
    have hp := (witness ⟨a, ha⟩).choose_spec.1
    have hc := (witness ⟨a, ha⟩).choose_spec.2.choose_spec
    simpa only [start, code, dif_pos ha] using And.intro hp hc
  have hnonstat : ¬IsStationary bad := by
    intro hbad
    obtain ⟨pvalue, hpstat⟩ := stationaryPressingDown bad (fun a => π (start a)) hbad
      (fun a ha => (hspec a ha).1)
    let pfiber : Set W2 := {a | a ∈ bad ∧ π (start a) = pvalue}
    obtain ⟨cvalue, hcstat⟩ := stationaryPressingDown pfiber (fun a => r (code a)) hpstat
      (fun a ha => (hspec a ha.1).2.1)
    let fiber : Set W2 := {a | a ∈ pfiber ∧ r (code a) = cvalue}
    obtain ⟨a0, ha0⟩ := hcstat.nonempty
    let p0 := start a0
    have hpconstant (a : W2) (ha : a ∈ fiber) : start a = p0 :=
      π.injective (ha.1.2.trans ha0.1.2.symm)
    obtain ⟨sys, hstart, hsource⟩ :=
      Erdos1172Part3StationarySquareBridge.exists_stationary_square_decisions_of_gch
        hGCH p0 G H hcompl fiber hcstat (fun a ha => hsup a ha.1.1.1) hred hblue
    obtain ⟨N, hN⟩ := exists_nice_clique_name
      (Erdos1172Part3StationaryDecisions.hechler_omegaTwoCC hGCH.toCH) sys.clique
    have hvalues : N.values ⊆ fiber := by
      intro x hx
      rw [N.values_eq_possible] at hx
      obtain ⟨p, i, hi⟩ := hx
      exact hsource p i x (hN p i x hi)
    obtain ⟨bound, hbound⟩ := exists_square_value_bound N
    obtain ⟨a, ⟨q, hq, hfuture⟩, hlocal⟩ := (sys.stationary sys.start le_rfl)
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 (max (σ N) bound))
    have haf : a ∈ fiber := sys.subset_source q a hfuture
    have habad : a ∈ bad := haf.1.1
    apply (hspec a habad).2.2.2
    refine ⟨N, (le_max_left _ _).trans_lt hlocal, ?_, q, ?_, ?_⟩
    · intro x hx
      have hxf := hvalues hx
      have hcode : code x = code a := r.injective (hxf.2.trans haf.2.symm)
      refine ⟨⟨hxf.1.1.1, ?_⟩, (hbound x hx).trans ((le_max_right _ _).trans_lt hlocal)⟩
      rw [← hcode]
      exact (hspec x hxf.1.1).2.2.1
    · rw [hpconstant a haf]
      exact hq.trans hstart
    · intro s hsq i x hx
      exact sys.cross s a (sys.persistent hsq hfuture) i x (hN s i x hx)
  obtain ⟨club, hclub, hdisjoint⟩ := not_isStationary_iff.mp hnonstat
  refine ⟨club, hclub, ?_⟩
  intro a hac has
  by_contra h
  exact Set.disjoint_left.mp hdisjoint ⟨has, h⟩ hac

/-- GCH supplies all the code embeddings; no locality or cardinality
assumptions about an externally supplied name space are left over. -/
theorem exists_club_local_named_square_of_gch (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (source : Set W2)
    (hsup : ∀ a ∈ source, ErdosRadoCHAsym.IsOmegaOneSup a)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, a ∈ source →
      LocalNamedSquare (conditionRank hGCH) (Erdos1172Part3CoreObjectCode.rank hGCH)
        (squareNameRank hGCH G) H source a :=
  exists_club_local_named_square hGCH (conditionRank hGCH)
    (Erdos1172Part3CoreObjectCode.rank hGCH) G H hcompl (squareNameRank hGCH G)
    source hsup hred hblue

end Erdos1172Part3LocalNamedSquare
