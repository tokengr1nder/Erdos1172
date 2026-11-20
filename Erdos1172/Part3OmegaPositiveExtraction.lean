/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaTraceComponents

@[expose] public section

/-!
# A whole omega core inside every positive omega trace

Successively chosen positive finite levels have unbounded depths. After
finite extraction and reindexing, a countable lower bound joins them into
one omega core with actual membership and exact original-point witnesses.
Reindexing is used only for extraction: no finite-trace transfer across
a dimension drop, or countable completeness of the omega trace, is claimed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OmegaPositiveExtraction

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FiniteTraceSchemes (Index scheme scheme_extracts mk_index_le typeLT_index)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex)
open Erdos1172Part3OmegaLevelTrace (levelCore omegaTrace exists_positive_level)
open Erdos1172Part3CliqueConeExtension (exists_global_clique_from_cone)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem exists_index_embedding {m n : ℕ} (hmn : m ≤ n) : Nonempty (Index m ↪o Index n) := by
  have htype : typeLT (Index m) ≤ typeLT (Index n) := by
    rw [typeLT_index, typeLT_index]
    apply Ordinal.opow_le_opow_right (Ordinal.omega_pos 1)
    exact_mod_cast Nat.succ_le_succ hmn
  obtain ⟨f⟩ := Ordinal.type_le_iff'.mp htype
  exact ⟨OrderEmbedding.ofStrictMono f (fun _ _ h => f.map_rel_iff.mpr h)⟩

def reindexCore {I J : Type} [LinearOrder I] [LinearOrder J]
    (core : CliqueDecisions P J W2 G) (e : I ↪o J) : CliqueDecisions P I W2 G where
  decides p i x := core.decides p (e i) x
  dense p i := core.dense p (e i)
  persistent hqp hx := core.persistent hqp hx
  unique hx hy := core.unique hx hy
  ordered hij hx hy := core.ordered (e.strictMono hij) hx hy
  adjacent hij hx hy := core.adjacent (fun h => hij (e.injective h)) hx hy

structure LevelState (p0 : P) where
  start : P
  below : start ≤ p0
  level : ℕ

structure LevelStep (core : CliqueDecisions P OmegaIndex W2 G) (U : RegularName P W2)
    (p0 : P) (m : ℕ) (old : LevelState p0) where
  next : LevelState p0
  below : next.start ≤ old.start
  level_gt : old.level < next.level
  name : CliqueDecisions P (Index m) W2 G
  origin : ∀ p : P, p ≤ next.start → ∀ i x, name.decides p i x → U.holds p x ∧
    ∃ j : Index next.level, core.decides p (toLex ⟨next.level, j⟩) x

theorem exists_level_step (hclosed : CountablyClosed P)
    (core : CliqueDecisions P OmegaIndex W2 G) (U : RegularName P W2) (p0 : P)
    (hU : (neg (omegaTrace core)).holds p0 U) (m : ℕ) (old : LevelState p0) :
    Nonempty (LevelStep core U p0 m old) := by
  obtain ⟨s, hs, n, hn, hpos⟩ :=
    exists_positive_level core p0 U hU old.start old.below (max old.level m)
  obtain ⟨t, hts, sub, hsub, _⟩ :=
    scheme_extracts G n hclosed (levelCore core n) s U (hpos s le_rfl)
  obtain ⟨e⟩ := exists_index_embedding ((le_max_right old.level m).trans hn.le)
  let smaller : CliqueDecisions (Set.Iic t) (Index m) W2 G := reindexCore sub e
  obtain ⟨global, hglobal, _⟩ := exists_global_clique_from_cone hclosed t smaller (mk_index_le m)
  refine ⟨{
    next := ⟨t, (hts.trans hs).trans old.below, n⟩
    below := hts.trans hs
    level_gt := (le_max_left old.level m).trans_lt hn
    name := global
    origin := ?_ }⟩
  intro p hp i x hx
  exact hsub ⟨p, hp⟩ (e i) x ((hglobal p hp i x).mp hx)

structure OmegaSubsequenceData (core : CliqueDecisions P OmegaIndex W2 G)
    (U : RegularName P W2) (p0 : P) where
  levels : ℕ → ℕ
  strict : StrictMono levels
  names : ∀ n : ℕ, CliqueDecisions P (Index n) W2 G
  origins : ∀ n p, p ≤ p0 → ∀ i x, (names n).decides p i x → U.holds p x ∧
    ∃ j : Index (levels n), core.decides p (toLex ⟨levels n, j⟩) x

theorem exists_omega_subsequence_data (hclosed : CountablyClosed P)
    (core : CliqueDecisions P OmegaIndex W2 G) (p0 : P) (U : RegularName P W2)
    (hU : (neg (omegaTrace core)).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ Nonempty (OmegaSubsequenceData core U q) := by
  classical
  let initial : LevelState p0 := ⟨p0, le_rfl, 0⟩
  let next (n : ℕ) (old : LevelState p0) : LevelStep core U p0 n old :=
    Classical.choice (exists_level_step hclosed core U p0 hU n old)
  let states : ℕ → LevelState p0 := fun n => Nat.rec initial (fun n old => (next n old).next) n
  have hstep (n : ℕ) : (states (n + 1)).start ≤ (states n).start := (next n (states n)).below
  have hanti : Antitone (fun n => (states n).start) := antitone_nat_of_succ_le hstep
  let C : Set P := Set.range (fun n => (states n).start)
  have hC : IsChain (· ≤ ·) C := by
    rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ _
    rcases le_total i j with hij | hji
    · exact Or.inr (hanti hij)
    · exact Or.inl (hanti hji)
  obtain ⟨q, hq⟩ := hclosed C ⟨(states 0).start, 0, rfl⟩ (Set.countable_range _) hC
  refine ⟨q, hq (states 0).start ⟨0, rfl⟩, ⟨{
    levels := fun n => (states (n + 1)).level
    strict := strictMono_nat_of_lt_succ (fun n => (next (n + 1) (states (n + 1))).level_gt)
    names := fun n => (next n (states n)).name
    origins := ?_ }⟩⟩
  intro n p hp i x hx
  exact (next n (states n)).origin p (hp.trans (hq _ ⟨n + 1, rfl⟩)) i x hx

variable {core : CliqueDecisions P OmegaIndex W2 G} {U : RegularName P W2} {p0 : P}

def OmegaSubsequenceData.decides (data : OmegaSubsequenceData core U p0)
    (p : Set.Iic p0) (z : OmegaIndex) (x : W2) : Prop :=
  (data.names (ofLex z).1).decides p.val (ofLex z).2 x

theorem OmegaSubsequenceData.ordered_pair (data : OmegaSubsequenceData core U p0)
    {p : Set.Iic p0} {i j : OmegaIndex} {x y : W2} (hij : i < j)
    (hx : data.decides p i x) (hy : data.decides p j y) : x < y ∧ G.Adj x y := by
  cases hij with
  | left k l hmn =>
    obtain ⟨_, oldi, hi⟩ := data.origins _ p.val p.property k x hx
    obtain ⟨_, oldj, hj⟩ := data.origins _ p.val p.property l y hy
    have hlt : (toLex ⟨data.levels _, oldi⟩ : OmegaIndex) < toLex ⟨data.levels _, oldj⟩ :=
      Sigma.Lex.left _ _ (data.strict hmn)
    exact ⟨core.ordered hlt hi hj, core.adjacent hlt.ne hi hj⟩
  | right k l hkl => exact ⟨(data.names _).ordered hkl hx hy, (data.names _).adjacent hkl.ne hx hy⟩

def OmegaSubsequenceData.toOmega (data : OmegaSubsequenceData core U p0) :
    CliqueDecisions (Set.Iic p0) OmegaIndex W2 G where
  decides := data.decides
  dense := by
    intro p z
    obtain ⟨q, hqp, x, hx⟩ := (data.names (ofLex z).1).dense p.val (ofLex z).2
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, x, hx⟩
  persistent := by
    intro p q z x hqp hx
    exact (data.names (ofLex z).1).persistent hqp hx
  unique := by
    intro p z x y hx hy
    exact (data.names (ofLex z).1).unique hx hy
  ordered hij hx hy := (data.ordered_pair hij hx hy).1
  adjacent := by
    intro p i j x y hij hx hy
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (data.ordered_pair hlt hx hy).2
    · exact (data.ordered_pair hgt hy hx).2.symm

theorem OmegaSubsequenceData.membership (data : OmegaSubsequenceData core U p0)
    (p : Set.Iic p0) (z : OmegaIndex) (x : W2) (hx : data.toOmega.decides p z x) :
    U.holds p.val x ∧ ∃ old : OmegaIndex, core.decides p.val old x := by
  obtain ⟨hUx, j, hj⟩ := data.origins (ofLex z).1 p.val p.property (ofLex z).2 x hx
  exact ⟨hUx, toLex ⟨data.levels (ofLex z).1, j⟩, hj⟩

theorem exists_omega_subcore (hclosed : CountablyClosed P)
    (core : CliqueDecisions P OmegaIndex W2 G) (p0 : P) (U : RegularName P W2)
    (hU : (neg (omegaTrace core)).holds p0 U) :
    ∃ q : P, q ≤ p0 ∧ ∃ sub : CliqueDecisions (Set.Iic q) OmegaIndex W2 G,
      ∀ p z x, sub.decides p z x → U.holds p.val x ∧
        ∃ old : OmegaIndex, core.decides p.val old x := by
  obtain ⟨q, hqp0, ⟨data⟩⟩ := exists_omega_subsequence_data hclosed core p0 U hU
  exact ⟨q, hqp0, data.toOmega, data.membership⟩

end Erdos1172Part3OmegaPositiveExtraction
