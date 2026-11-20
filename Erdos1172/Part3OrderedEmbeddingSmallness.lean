/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedDiscreteCoverProfile
public import Erdos1172.Part3NamedShortCover
public import Erdos1172.Part3SupportedCoverEmbedding
public import Erdos1172.Part3SupportedCoverUnion
public import Erdos1172.Part3OmegaSuccessorUnion

@[expose] public section

/-!
# Hereditary absence of full ordered embeddings

Failure to carry an ordered embedding at one condition is not silently
assumed to persist. Smallness instead rules out such an embedding on
every sub-cone. This hereditary predicate is regular and downward closed
under actual named inclusion.

At the omega-successor threshold, the constructed local short covers and
joint realization of supported cover names give binary-union closure.
Ground bounds strictly below the embedding type supply smallness, while
an actual full ordered embedding supplies positivity. Applications must
still establish their own source embedding and base-small ground bounds.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OrderedEmbeddingSmallness

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName regularize ground neg implication)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3NamedLocalRowCover (onConeDecisions)
open Erdos1172Part3NamedCofinalRowCovers (nestCone flattenDecisions)
open Erdos1172Part3NamedDiscreteCoverProfile (CoveredAt coveredAt_persistent)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3SupportedCoverRealization (coverName holds_of_certificate)
open Erdos1172Part3SupportedCoverUnion (firstRow unionFamily holds_union_left holds_union_right)
open Erdos1172Part3FunctionProfileEncoding (encodedName)
open Erdos1172Part3CoverProfileTools (head row decode)

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]

/-- A full ordered embedding restricts to every smaller cone. -/
theorem hasOrderedEmbeddingBelow_persistent {U : RegularName P V} {p q : P}
    (hqp : q ≤ p) (hp : HasOrderedEmbeddingBelow (I := I) U p) :
    HasOrderedEmbeddingBelow (I := I) U q := by
  obtain ⟨E, hordered, hmem⟩ := hp
  let r : Iic p := ⟨q, hqp⟩
  refine ⟨flattenDecisions r (onConeDecisions E r), ?_, ?_⟩
  · intro s i j x y hij hx hy
    exact hordered (nestCone r s).val i j x y hij hx hy
  · intro s i x hx
    exact hmem (nestCone r s).val i x hx

/-- Inclusion on the whole starting cone transfers an actual ordered
embedding to the larger regular name. -/
theorem hasOrderedEmbeddingBelow_mono {U W : RegularName P V} {p : P}
    (hsub : ∀ q : P, q ≤ p → ∀ x : V, U.holds q x → W.holds q x)
    (hU : HasOrderedEmbeddingBelow (I := I) U p) :
    HasOrderedEmbeddingBelow (I := I) W p := by
  obtain ⟨E, hordered, hmem⟩ := hU
  exact ⟨E, hordered, fun q i x hx => hsub q.val q.property x (hmem q i x hx)⟩

/-- Smallness rules out a full ordered embedding on every sub-cone. -/
def SmallAt (U : RegularName P V) (p : P) : Prop :=
  ∀ q : P, q ≤ p → ¬HasOrderedEmbeddingBelow (I := I) U q

theorem smallAt_persistent {U : RegularName P V} {p q : P}
    (hqp : q ≤ p) (hp : SmallAt (I := I) U p) : SmallAt (I := I) U q :=
  fun r hrq => hp r (hrq.trans hqp)

/-- Hereditary smallness is downward closed for actual inclusion on the
starting cone, without a global inclusion assumption. -/
theorem smallAt_mono {U W : RegularName P V} {p : P}
    (hsub : ∀ q : P, q ≤ p → ∀ x : V, U.holds q x → W.holds q x)
    (hsmall : SmallAt (I := I) W p) : SmallAt (I := I) U p := by
  intro q hqp hE
  exact hsmall q hqp (hasOrderedEmbeddingBelow_mono
    (fun r hrq x hx => hsub r (hrq.trans hqp) x hx) hE)

/-- Dense hereditary smallness is hereditary smallness. An embedding
on a sub-cone would restrict to a dense smallness witness below it. -/
def smallName : RegularName P (RegularName P V) where
  holds p U := SmallAt (I := I) U p
  persistent hqp hp := smallAt_persistent hqp hp
  of_dense := by
    intro p U hd q hqp hE
    obtain ⟨r, hrq, hr⟩ := hd q hqp
    exact hr r le_rfl (hasOrderedEmbeddingBelow_persistent hrq hE)

/-- A full embedding gives actual positivity, since it survives on
every sub-cone and contradicts hereditary smallness there. -/
theorem smallName_neg_of_embedding {U : RegularName P V} {p : P}
    (hE : HasOrderedEmbeddingBelow (I := I) U p) :
    (neg (smallName (I := I))).holds p U := by
  intro q hqp hq
  exact hq q le_rfl (hasOrderedEmbeddingBelow_persistent hqp hE)

variable [WellFoundedLT I] [WellFoundedLT V]

/-- A uniformly short local cover rules out every full embedding below
that cone. The realization bounds decided points, not possible points. -/
theorem smallAt_of_coveredAt (hclosed : CountablyClosed P) (hI : #I ≤ ℵ_ 1)
    {U : RegularName P V} {C : (W1 → W1) → Set V} {p : P}
    (hcover : CoveredAt U C p) (hC : ∀ f, typeLT (C f) < typeLT I) :
    SmallAt (I := I) U p := by
  intro q hqp hE
  obtain ⟨F, hF⟩ := coveredAt_persistent hqp hcover
  obtain ⟨E, hordered, hmem⟩ := hE
  have hbad : typeLT I < typeLT I :=
    Erdos1172Part3SupportedCoverEmbedding.typeLT_lt_of_embedding_decisions F E C
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
      ⟨q, le_rfl⟩ hI (fun r _ i x hx => hF r x (hmem r i x hx))
      (fun r _ i j x y hij hx hy => hordered r i j x y hij hx hy) (typeLT I) hC
  exact (lt_irrefl _) hbad

/-- A short ground bound for every actual point throughout a cone
supplies hereditary smallness; there is no cardinal bound on the codomain. -/
theorem smallAt_of_ground_bound (hclosed : CountablyClosed P) (hI : #I ≤ ℵ_ 1)
    (U : RegularName P V) (p : P) (A : Set V) (hA : typeLT A < typeLT I)
    (hsub : ∀ q : P, q ≤ p → ∀ x : V, U.holds q x → x ∈ A) :
    SmallAt (I := I) U p := by
  apply smallAt_of_coveredAt hclosed hI (C := fun _ => A) (hC := fun _ => hA)
  refine ⟨FunctionDecisions.ofFunction
    (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ?_⟩
  intro q x hx
  apply holds_of_certificate
  refine ⟨(fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ∅, by simp, ?_⟩
  exact fun _ _ => hsub q.val q.property x hx

end Erdos1172Part3OrderedEmbeddingSmallness
