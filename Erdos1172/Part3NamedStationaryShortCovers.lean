/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedDiscreteCoverProfile
public import Erdos1172.Part3NamedShortCover

@[expose] public section

/-!
# One short cover profile for stationary families of actual loss names

The short cover families are constructed before any loss is chosen.
Hereditary absence of a full ordered decision embedding supplies their
local coverage. The proved discrete profile theorem then freezes one
family on a stationary regular subname and supplies global function names
covering every actual loss at every actual future member.

The hereditary no-embedding hypothesis is explicit. Establishing it for
the original coloring's loss names is still a separate mathematical task;
the earlier weak trace-smallness statement is not substituted for it.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedStationaryShortCovers

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC possible StationaryAt)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)
open Erdos1172Part3SupportedCoverRealization (coverName)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V]

/-- The covering family and global covering function names are conclusions,
not supplied hypotheses. Actual loss shortness remains explicit at every
relevant condition and every actual source member. -/
theorem exists_stationary_short_cover
    (hcard : #V ≤ ℵ_ 1) (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (U : RegularName P W2) (p0 : P) (hs : IsStationary (possible U.holds p0))
    (loss : W2 → RegularName P V)
    (hno : ∀ p : P, p ≤ p0 → ∀ b : W2, U.holds p b →
      ¬HasOrderedEmbeddingBelow (I := V) (loss b) p) :
    ∃ p : P, p ≤ p0 ∧ ∃ T : RegularName P W2,
      StationaryAt T.holds p ∧ (∀ q b, T.holds q b → U.holds q b) ∧
        ∃ C : (W1 → W1) → Set V, Monotone C ∧ FinitelySupported C ∧
          (∀ f, typeLT (C f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) ∧
          ∃ F : W2 → FunctionDecisions P W1 W1,
            ∀ q b x, T.holds q b → (loss b).holds q x → (coverName (F b) C).holds q x := by
  obtain ⟨C, hC, hcover⟩ :=
    Erdos1172Part3NamedShortCover.exists_supported_named_short_covers hcard htype
  have hsmall : #(V × ℕ) < ℵ_ 2 :=
    (Erdos1172Part3BoundedPrefixCovers.mk_profiles_le hcard).trans_lt
      (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))
  obtain ⟨e, p, hpp0, T, hT, hTU, F, hF⟩ :=
    Erdos1172Part3NamedDiscreteCoverProfile.exists_stationary_cover_profile
      hsmall hcc U p0 hs loss C (by
        intro q hqp0 b hb
        obtain ⟨r, hrq, e, F, hF⟩ := hcover P hclosed (loss b) q (hno q hqp0 b hb)
        exact ⟨r, hrq, e, F, hF⟩)
  exact ⟨p, hpp0, T, hT, hTU, C e, (hC e).1, (hC e).2.1, (hC e).2.2, F, hF⟩

end Erdos1172Part3NamedStationaryShortCovers
