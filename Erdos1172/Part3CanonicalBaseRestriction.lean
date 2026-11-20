/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CompleteRestriction
public import Erdos1172.Part3CountableHechlerOverBase

@[expose] public section

/-!
# Canonical empty-tail restrictions for the constructed orders

The base restriction is complete for both one added Hechler stage and
the already constructed countable extension. The countable inclusion
is defined coordinate by coordinate with genuinely empty stems and
sides; it is not an arbitrary coherent extension chosen by existence.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CanonicalBaseRestriction

open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3IteratedHechlerOrder (Condition emptyOver liftBase liftBase_le base_le)
open Erdos1172Part3FiniteHechlerStages (SmallClosedCenteredOrder)
open Erdos1172Part3CountableHechlerOverBase (At LimitOver)

variable {P : Type} [Preorder P]

theorem le_emptyOver (p : Condition P) (q : P) (hpq : p.base ≤ q) : p ≤ emptyOver q := by
  refine ⟨hpq, ?_, ?_, ?_⟩
  · intro i v hv
    cases hv
  · exact Set.empty_subset _
  · intro i hi v hv F hF
    exact hF.elim

theorem emptyOver_mono {p q : P} (hpq : p ≤ q) : emptyOver p ≤ emptyOver q :=
  le_emptyOver (emptyOver p) q hpq

def oneStage : CompleteRestriction (Condition P) P where
  restrict := ⟨Condition.base, fun _ _ h => base_le h⟩
  embed := ⟨emptyOver, fun _ _ h => emptyOver_mono h⟩
  restrict_embed _ := rfl
  below_embed p := le_emptyOver p p.base le_rfl
  lift p q hqp := ⟨liftBase p q, liftBase_le p hqp, rfl⟩

variable {hGCH : GCH} {R : SmallClosedCenteredOrder}

noncomputable def emptyBranch (p : R.Carrier) : ∀ n : ℕ, At hGCH R n
  | 0 => p
  | n + 1 => emptyOver (emptyBranch p n)

noncomputable def emptyTail (p : R.Carrier) : LimitOver hGCH R where
  point := emptyBranch p
  coherent _ := rfl

theorem emptyTail_base (p : R.Carrier) : (emptyTail (hGCH := hGCH) p).point 0 = p := rfl

theorem emptyTail_stem (p : R.Carrier) (n : ℕ) :
    ((emptyTail (hGCH := hGCH) p).point (n + 1)).stem = fun _ => none := rfl

theorem emptyTail_side (p : R.Carrier) (n : ℕ) :
    ((emptyTail (hGCH := hGCH) p).point (n + 1)).side = ∅ := rfl

theorem emptyTail_mono {p q : R.Carrier} (hpq : p ≤ q) :
    emptyTail (hGCH := hGCH) p ≤ emptyTail q := by
  intro n
  induction n with
  | zero => exact hpq
  | succ n ih => exact emptyOver_mono ih

theorem le_emptyTail (p : LimitOver hGCH R) (q : R.Carrier) (hpq : p.point 0 ≤ q) :
    p ≤ emptyTail q := by
  intro n
  induction n with
  | zero => exact hpq
  | succ n ih =>
    apply le_emptyOver
    rw [p.coherent n]
    exact ih

noncomputable def countableStage : CompleteRestriction (LimitOver hGCH R) R.Carrier where
  restrict := Erdos1172Part3CountableHechlerOverBase.atMap 0
  embed := ⟨emptyTail, fun _ _ h => emptyTail_mono h⟩
  restrict_embed _ := rfl
  below_embed p := le_emptyTail p (p.point 0) le_rfl
  lift := Erdos1172Part3CountableHechlerOverBase.exists_lift_base

end Erdos1172Part3CanonicalBaseRestriction
