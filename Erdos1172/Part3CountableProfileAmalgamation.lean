/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountablyUniversalLabels
public import Erdos1172.Part3IteratedHechlerCentering

@[expose] public section

/-!
# Countable amalgamation in universal profile classes

Profiles in one covering class agree wherever both are active. Their
countable union is again a profile, with exactly the union of supports.
For whole-stem labels this says that overlapping active coordinates
have identical stems, not merely compatible values at some entries.

The final centering API retains its history-amalgamation premise. It
does not claim to have constructed an uncountable Hechler iteration.
-/

open Cardinal Ordinal Set Function

namespace Erdos1172Part3CountableProfileAmalgamation

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3CountableSupportProfiles (Profile support StemProfile)
open Erdos1172Part3CountablyUniversalLabels (CountableCover exists_countableCover_of_gch)
open Erdos1172Part3HechlerCentering (Stem mk_Stem_le)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)

variable {I V : Type}

noncomputable def stemCover (hGCH : GCH) (hI : #I ≤ ℵ_ 2) : CountableCover I Stem :=
  Classical.choice (exists_countableCover_of_gch hGCH hI (mk_Stem_le hGCH.toCH))

variable {P : Type} [Preorder P]

/-- A reusable centering construction for histories. The substantive
order-specific lower-bound assertion remains explicit. -/
noncomputable def centered_of_profile_amalgamation
    (cover : CountableCover I V) (profile : P → Profile I V)
    (hfuse : ∀ C : Set P, C.Countable →
      (∀ p ∈ C, ∀ q ∈ C, ∀ i v w,
        (profile p).val i = some v → (profile q).val i = some w → v = w) →
      ∃ lower : P, ∀ p ∈ C, lower ≤ p) : CountablyCenteredCode P where
  code p := cover.code (profile p)
  lower := by
    intro C hC value hvalue
    apply hfuse C hC
    intro p hp q hq i v w hpv hqw
    exact cover.agree_on_overlap ((hvalue p hp).trans (hvalue q hq).symm) hpv hqw

end Erdos1172Part3CountableProfileAmalgamation
