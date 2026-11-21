/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OrderedEmbeddingSmallness

@[expose] public section

/-!
# Actual ordered traces on named cores

Pullback membership tests all future decisions of a coordinate against
actual regular membership. Ordered trace smallness is hereditary absence
of a full embedding in this regular inverse image.

For a guarded omega-successor product, convergence of a base-small
witness excludes every coordinate in sufficiently late outer rows.
The remaining ground rows have strictly smaller whole order type. This
argument does not identify weak eventual finite-level trace smallness
with order-type smallness.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OrderedCoreTrace

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions CountablyClosed)
open Erdos1172Part3RegularCliqueNeighborhoods (cliqueFunction)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3OrderedEmbeddingSmallness (SmallAt smallAt_mono
  smallAt_of_ground_bound smallName_neg_of_embedding)

variable {P I X : Type} [Preorder P]

/-- Actual regular inverse image along a name with unique dense values. -/
def pullback (F : FunctionDecisions P I X) (U : RegularName P X) : RegularName P I where
  holds p i := ∀ q : P, q ≤ p → ∀ x, F.decides q i x → U.holds q x
  persistent hqp hp r hrq := hp r (hrq.trans hqp)
  of_dense := by
    intro p i hd q hqp x hx
    apply U.of_dense q x
    intro r hrq
    obtain ⟨s, hsr, hs⟩ := hd r (hrq.trans hqp)
    exact ⟨s, hsr, hs s le_rfl x (F.persistent (hsr.trans hrq) hx)⟩

theorem pullback_holds_iff_of_decides (F : FunctionDecisions P I X)
    (U : RegularName P X) {p : P} {i : I} {x : X} (hx : F.decides p i x) :
    (pullback F U).holds p i ↔ U.holds p x := by
  constructor
  · exact fun h => h p le_rfl x hx
  · intro h q hqp y hy
    have hxy : x = y := F.unique (F.persistent hqp hx) hy
    subst y
    exact U.persistent hqp h

theorem pullback_mono_on_decisions (F : FunctionDecisions P I X)
    {U W : RegularName P X} {p : P}
    (hsub : ∀ q : P, q ≤ p → ∀ i x, F.decides q i x → U.holds q x → W.holds q x) :
    ∀ q : P, q ≤ p → ∀ i, (pullback F U).holds q i → (pullback F W).holds q i := by
  intro q hqp i hi r hrq x hx
  exact hsub r (hrq.trans hqp) i x hx (hi r hrq x hx)

theorem pullback_mono (F : FunctionDecisions P I X)
    {U W : RegularName P X} {p : P}
    (hsub : ∀ x, (implication U W).holds p x) :
    ∀ q : P, q ≤ p → ∀ i, (pullback F U).holds q i → (pullback F W).holds q i :=
  pullback_mono_on_decisions F (fun q hqp _ x _ hx => hsub x q hqp hx)

section Ordered

variable [LinearOrder I]

/-- When every actual named value lies in U on a cone, the identity
selector is a full ordered embedding into its inverse image. -/
theorem hasOrderedEmbeddingBelow_pullback_of_cover
    (F : FunctionDecisions P I X) (U : RegularName P X) (p : P)
    (hcover : ∀ q : P, q ≤ p → ∀ i x, F.decides q i x → U.holds q x) :
    HasOrderedEmbeddingBelow (I := I) (pullback F U) p := by
  refine ⟨FunctionDecisions.ofFunction (id : I → I), ?_, ?_⟩
  · intro q i j x y hij hx hy
    change i = x at hx
    change j = y at hy
    exact hx ▸ hy ▸ hij
  · intro q i j _ r hrq x hx
    exact hcover r (hrq.trans q.property) j x hx

variable [LinearOrder X] {G : SimpleGraph X}

def trace (core : CliqueDecisions P I X G) : RegularName P (RegularName P X) :=
  reindex (Erdos1172Part3OrderedEmbeddingSmallness.smallName (I := I))
    (pullback (cliqueFunction core))

theorem trace_holds_iff (core : CliqueDecisions P I X G) (p : P) (U : RegularName P X) :
    (trace core).holds p U ↔ SmallAt (I := I) (pullback (cliqueFunction core) U) p := Iff.rfl

theorem trace_mono_on_decisions (core : CliqueDecisions P I X G)
    {p : P} {U W : RegularName P X}
    (hsub : ∀ q : P, q ≤ p → ∀ i x, core.decides q i x → U.holds q x → W.holds q x)
    (hsmall : (trace core).holds p W) : (trace core).holds p U :=
  smallAt_mono (pullback_mono_on_decisions (cliqueFunction core) hsub) hsmall

theorem trace_mono (core : CliqueDecisions P I X G) (p : P) (U W : RegularName P X)
    (hsub : ∀ x, (implication U W).holds p x)
    (hsmall : (trace core).holds p W) : (trace core).holds p U :=
  smallAt_mono (pullback_mono (cliqueFunction core) hsub) hsmall

theorem trace_not_small_of_cover (core : CliqueDecisions P I X G)
    (p : P) (U : RegularName P X)
    (hcover : ∀ q : P, q ≤ p → ∀ i x, core.decides q i x → U.holds q x) :
    (neg (trace core)).holds p U :=
  smallName_neg_of_embedding
    (hasOrderedEmbeddingBelow_pullback_of_cover (cliqueFunction core) U p hcover)

end Ordered

open Erdos1172Part3OmegaPowerIndex (OmegaIndex)
open Erdos1172Part3OmegaSuccessorCore (OmegaSuccessor mk_omegaSuccessor_le)
open Erdos1172Part3ExactOmegaIndex (boundedRows boundedRows_type_lt typeLT_omegaSuccessor)
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ControlledCoreProducts (ProductData)
open Erdos1172Part3GuardedTraceFamily (priorSource)

variable {G H : SimpleGraph W2}

/-- Eventual avoidance in every outer row bounds the actual inverse
image by the ground initial collection of rows. -/
theorem pullback_boundedRows_of_avoids
    (core : CliqueDecisions P OmegaSuccessor W2 G) (U : RegularName P W2)
    (p : P) (bound : W1)
    (havoid : ∀ q : P, q ≤ p → ∀ z : OmegaSuccessor, bound < (ofLex z).1 →
      ∀ x, core.decides q z x → ¬U.holds q x) :
    ∀ q : P, q ≤ p → ∀ z, (pullback (cliqueFunction core) U).holds q z → z ∈ boundedRows bound := by
  intro q hqp z hz
  change (ofLex z).1 ≤ bound
  apply le_of_not_gt
  intro hlate
  obtain ⟨r, hrq, x, hx⟩ := core.dense q z
  exact havoid r (hrq.trans hqp) z hlate x hx (hz r hrq x hx)

theorem small_trace_of_avoids_late_rows (hclosed : CountablyClosed P)
    (core : CliqueDecisions P OmegaSuccessor W2 G) (U : RegularName P W2)
    (p : P) (bound : W1)
    (havoid : ∀ q : P, q ≤ p → ∀ z : OmegaSuccessor, bound < (ofLex z).1 →
      ∀ x, core.decides q z x → ¬U.holds q x) : (trace core).holds p U := by
  apply smallAt_of_ground_bound hclosed mk_omegaSuccessor_le
    (pullback (cliqueFunction core) U) p (boundedRows bound)
  · rw [typeLT_omegaSuccessor]
    exact boundedRows_type_lt bound
  · exact pullback_boundedRows_of_avoids core U p bound havoid

variable {r : Code P OmegaIndex G ↪ W2}
  {σ : NiceCliqueName P OmegaIndex W2 G ↪ W2}
  {source : RegularName P W2} {a : W2}

/-- Base-small witnesses are eventually avoided by whole outer rows,
not just by lower-dimensional fragments of those rows. -/
theorem base_small_to_ordered_trace (hclosed : CountablyClosed P)
    (data : ProductData r H source a) (ha : GoodCut r σ H source a)
    (p : P) (hp : source.holds p a) (U : RegularName P W2)
    (hU : (Erdos1172Part3RegularNamedIdeal.smallName r H a).holds p U) :
    (trace data.name.toClique).holds p U := by
  apply (trace data.name.toClique).of_dense p U
  intro q hqp
  obtain ⟨s, hsq, c, hc, hn, hcover⟩ := hU q hqp
  have hca : (eval G H (SmallUnionCode.compl c)).holds s a := by
    rw [Erdos1172Part3RegularNeighborhoodCode.eval_compl]
    exact hn
  obtain ⟨t, hts, bound, hbound⟩ := data.converges (SmallUnionCode.compl c)
    (ha.compl_lt c hc) s (source.persistent (hsq.trans hqp) hp) hca s le_rfl
  refine ⟨t, hts.trans hsq, small_trace_of_avoids_late_rows hclosed data.name.toClique U t bound ?_⟩
  intro v hvt z hz x hx hUx
  have hcx := hbound v hvt z hz x hx
  rw [Erdos1172Part3RegularNeighborhoodCode.eval_compl] at hcx
  exact hcx v le_rfl (hcover x (data.geometry v z x hx).1 v (hvt.trans hts) hUx)

theorem prior_source_ordered_positive (data : ProductData r H source a)
    (p : P) (hp : source.holds p a) :
    (neg (trace data.name.toClique)).holds p (priorSource source a) := by
  apply trace_not_small_of_cover data.name.toClique p (priorSource source a)
  intro q hqp z x hx
  exact ⟨data.actual_source q (source.persistent hqp hp) z x hx, (data.geometry q z x hx).1⟩

end Erdos1172Part3OrderedCoreTrace
