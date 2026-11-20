/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CompleteRestrictionNames
public import Erdos1172.Part3RegularLocalBlock
public import Erdos1172.Part3RegularStageLocality

@[expose] public section

/-!
# Reading the same ranked witness test at an earlier stage

If every name allowed by the full-order rank cutoff is supported on an
earlier stage, and the source is lifted from that stage, the full ranked
availability test and its negation are exactly readable there.

The allowed names retain their original full-order ranks. No inequality
for a separately chosen rank on earlier-stage names is inferred. This is
locality of a ranked test, not existence of any higher-core witness.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RankedWitnessRestriction

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3CompleteRestriction
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique containedIn cliqueFunction)

variable {P Q I : Type} [Preorder P] [Preorder Q] [LinearOrder I]
variable {G : SimpleGraph W2}

def RankedWitness (rank : NiceCliqueName P I W2 G ↪ W2)
    (source : RegularName P W2) (p : P) (a : W2) : Prop :=
  ∃ N : NiceCliqueName P I W2 G, rank N < a ∧
    (∀ q i x, N.toClique.decides q i x → x < a) ∧
    (containedIn (cliqueFunction N.toClique) source).holds p () ∧
    (afterClique N.toClique).holds p a

def rankedAvailability (rank : NiceCliqueName P I W2 G ↪ W2) (source : RegularName P W2) :
    RegularName P W2 := regularize (RankedWitness rank source)

theorem rankedAvailability_eq_localBlockName
    (rank : NiceCliqueName P W1 W2 G ↪ W2) (source : RegularName P W2) :
    rankedAvailability rank source = Erdos1172Part3RegularLocalBlock.localBlockName rank source := rfl

theorem restrictClique_containedIn_iff (r : CompleteRestriction P Q)
    (N : NiceCliqueName P I W2 G) (hs : Supported r N.function)
    (source : RegularName Q W2) (p : P) :
    (containedIn (cliqueFunction N.toClique) (r.liftRegular source)).holds p () ↔
      (containedIn (cliqueFunction (restrictClique r N hs).toClique) source).holds (r.restrict p) () := by
  constructor
  · intro h q hqp i x hx
    obtain ⟨s, hsp, hsbase⟩ := r.lift p q hqp
    have hx' : (restrictClique r N hs).toClique.decides (r.restrict s) i x := by
      rwa [hsbase]
    have hsource := h s hsp i x ((restrictClique_decides_iff r N hs s i x).mp hx')
    change source.holds (r.restrict s) x at hsource
    rwa [hsbase] at hsource
  · intro h q hqp i x hx
    exact h (r.restrict q) (r.restrict.monotone hqp) i x
      ((restrictClique_decides_iff r N hs q i x).mpr hx)

def restrictedWitness (r : CompleteRestriction P Q)
    (rank : NiceCliqueName P I W2 G ↪ W2) (a : W2)
    (hs : ∀ N, rank N < a → Supported r N.function)
    (source : RegularName Q W2) (q : Q) : Prop :=
  ∃ N : {N : NiceCliqueName P I W2 G // rank N < a},
    (∀ p i x, N.val.toClique.decides p i x → x < a) ∧
    (containedIn (cliqueFunction (restrictClique r N.val (hs N.val N.property)).toClique)
      source).holds q () ∧
    (afterClique (restrictClique r N.val (hs N.val N.property)).toClique).holds q a

def restrictedAvailability (r : CompleteRestriction P Q)
    (rank : NiceCliqueName P I W2 G ↪ W2) (a : W2)
    (hs : ∀ N, rank N < a → Supported r N.function)
    (source : RegularName Q W2) : RegularName Q Unit :=
  regularize (fun q _ => restrictedWitness r rank a hs source q)

theorem rankedWitness_restrict_iff (r : CompleteRestriction P Q)
    (rank : NiceCliqueName P I W2 G ↪ W2) (a : W2)
    (hs : ∀ N, rank N < a → Supported r N.function)
    (source : RegularName Q W2) (p : P) :
    RankedWitness rank (r.liftRegular source) p a ↔
      restrictedWitness r rank a hs source (r.restrict p) := by
  constructor
  · rintro ⟨N, hN, hbelow, hsource, hafter⟩
    exact ⟨⟨N, hN⟩, hbelow,
      (restrictClique_containedIn_iff r N (hs N hN) source p).mp hsource,
      (restrictClique_after_iff r N (hs N hN) p a).mpr hafter⟩
  · rintro ⟨⟨N, hN⟩, hbelow, hsource, hafter⟩
    exact ⟨N, hN, hbelow,
      (restrictClique_containedIn_iff r N (hs N hN) source p).mpr hsource,
      (restrictClique_after_iff r N (hs N hN) p a).mp hafter⟩

theorem rankedAvailability_restrict_iff (r : CompleteRestriction P Q)
    (rank : NiceCliqueName P I W2 G ↪ W2) (a : W2)
    (hs : ∀ N, rank N < a → Supported r N.function)
    (source : RegularName Q W2) (p : P) :
    (rankedAvailability rank (r.liftRegular source)).holds p a ↔
      (restrictedAvailability r rank a hs source).holds (r.restrict p) () := by
  constructor
  · intro h q hqp
    obtain ⟨s, hsp, hsbase⟩ := r.lift p q hqp
    obtain ⟨t, hts, ht⟩ := h s hsp
    refine ⟨r.restrict t, ?_, (rankedWitness_restrict_iff r rank a hs source t).mp ht⟩
    have hle := r.restrict.monotone hts
    rwa [hsbase] at hle
  · intro h q hqp
    obtain ⟨s, hsq, hs'⟩ := h (r.restrict q) (r.restrict.monotone hqp)
    obtain ⟨t, htq, htbase⟩ := r.lift q s hsq
    refine ⟨t, htq, (rankedWitness_restrict_iff r rank a hs source t).mpr ?_⟩
    rwa [htbase]

theorem neg_rankedAvailability_restrict_iff (r : CompleteRestriction P Q)
    (rank : NiceCliqueName P I W2 G ↪ W2) (a : W2)
    (hs : ∀ N, rank N < a → Supported r N.function)
    (source : RegularName Q W2) (p : P) :
    (neg (rankedAvailability rank (r.liftRegular source))).holds p a ↔
      (neg (restrictedAvailability r rank a hs source)).holds (r.restrict p) () := by
  constructor
  · intro h q hqp hq
    obtain ⟨s, hsp, hsbase⟩ := r.lift p q hqp
    apply h s hsp
    apply (rankedAvailability_restrict_iff r rank a hs source s).mpr
    rwa [hsbase]
  · intro h q hqp hq
    exact h (r.restrict q) (r.restrict.monotone hqp)
      ((rankedAvailability_restrict_iff r rank a hs source q).mp hq)

/-- The name-support and source-factorization premises above are
simultaneously supplied on a club by the stated countable-support stage
system. The original full-order rank cutoff is retained on both sides. -/
theorem exists_club_ranked_tests_local
    (Stage : W2 → Type) [∀ a, Preorder (Stage a)]
    (restriction : ∀ a, CompleteRestriction P (Stage a))
    (conditionSupport : P → Set W2) (hsmall : ∀ p, (conditionSupport p).Countable)
    (hlocal : ∀ a p, (∀ b ∈ conditionSupport p, b < a) →
      p ∈ Set.range (restriction a).embed)
    (G H : SimpleGraph W2) (hI : #I ≤ ℵ_ 1)
    (codeRank : Erdos1172Part3RegularNeighborhoodCode.Code P I G ↪ W2)
    (nameRank : NiceCliqueName P I W2 G ↪ W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ∀ c : Erdos1172Part3RegularNeighborhoodCode.Code P I G, codeRank c < a →
        ∃ U : RegularName (Stage a) Unit,
          (∀ p : P,
            (rankedAvailability nameRank (Erdos1172Part3RegularNeighborhoodCode.eval G H c)).holds p a ↔
              U.holds ((restriction a).restrict p) ()) ∧
          ∀ p : P,
            (neg (rankedAvailability nameRank (Erdos1172Part3RegularNeighborhoodCode.eval G H c))).holds p a ↔
              (neg U).holds ((restriction a).restrict p) () := by
  obtain ⟨names, hnames, hn⟩ := Erdos1172Part3NiceNameSupport.exists_club_supported_names
    conditionSupport hsmall Stage restriction hlocal hI nameRank
  obtain ⟨sources, hsources, hc⟩ := Erdos1172Part3RegularStageLocality.exists_club_local_code_sources
    Stage restriction conditionSupport hsmall hlocal G H hI codeRank
  refine ⟨names ∩ sources,
    hnames.inter Erdos1172Part3NeighborhoodCode.alephZero_lt_cof_W2.ne' hsources, ?_⟩
  intro a ha c hca
  obtain ⟨source, hsource⟩ := hc a ha.2 c hca
  let hs := hn a ha.1
  refine ⟨restrictedAvailability (restriction a) nameRank a hs source, ?_, ?_⟩
  · intro p
    rw [← hsource]
    exact rankedAvailability_restrict_iff (restriction a) nameRank a hs source p
  · intro p
    rw [← hsource]
    exact neg_rankedAvailability_restrict_iff (restriction a) nameRank a hs source p

end Erdos1172Part3RankedWitnessRestriction
