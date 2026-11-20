/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerCoverAssembly

@[expose] public section

/-!
# Coverage by the assembled higher-power family

Every proper row is decomposed into countably many pure pieces. Their
actual endpoints have countable prefixes, so one line cover contains
all endpoints. A pointwise bound for the countably many local covering
functions in each row then covers every piece. The resulting profile
is constructed from the given cofinal set.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalPowerCoverCoverage

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3CofinalPowerEndpoints (below exists_bounded_cofinal_power_decomposition)
open Erdos1172Part3CofinalFiniteCuts (rowSection cofinal_row_type_lt covers_of_countable_prefixes)
open Erdos1172Part3CoverProfileTools
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers cover addedRow)

variable {V : Type} [LinearOrder V] [WellFoundedLT V] {n : ℕ}

structure PieceCover (data : LineCoverData V) (L : LowerCovers n V) (i : W1) (B : Set V) where
  endpoint : V
  endpoint_le : endpoint ≤ data.cut i
  row_witness : ∃ x : V, data.row x = i ∧ x ≤ endpoint
  function : W1 → W1
  covered : ∀ x ∈ B, x = endpoint ∨ ∃ k : Fin n, x ∈ L.into endpoint k function

theorem exists_pieceCover (data : LineCoverData V) (L : LowerCovers n V)
    (i : W1) (B : Set V)
    (hrow : ∀ x ∈ B, data.row x = i) (hbound : B ⊆ Set.Iio (data.cut i))
    (hpiece : typeLT B = 1 ∨ ∃ k : ℕ, k < n ∧ ∃ bound : V,
      bound ≤ data.cut i ∧ B ⊆ Set.Iio bound ∧ IsCofinal (below B bound) ∧
        typeLT (below B bound) = (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal)) :
    Nonempty (PieceCover data L i B) := by
  classical
  rcases hpiece with hsingle | ⟨k, hk, endpoint, hend, hsub, hcof, htype⟩
  · obtain ⟨uniqueB⟩ := Ordinal.type_eq_one_iff_unique.mp hsingle
    let x : B := uniqueB.default
    refine ⟨⟨x.val, (hbound x.property).le, ⟨x.val, hrow x.val x.property, le_rfl⟩,
      (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ?_⟩⟩
    intro y hy
    exact Or.inl (congrArg Subtype.val (uniqueB.uniq (⟨y, hy⟩ : B)))
  · obtain ⟨f, hf⟩ := L.covers endpoint ⟨k, hk⟩ B hsub hcof htype
    have hn : Nonempty (below B endpoint) := Ordinal.type_ne_zero_iff_nonempty.mp (by
      rw [htype]
      exact (Ordinal.opow_pos _ (Ordinal.omega_pos 1)).ne')
    obtain ⟨x⟩ := hn
    refine ⟨⟨endpoint, hend,
      ⟨x.val.val, hrow x.val.val x.property, (hsub x.property).le⟩, f, ?_⟩⟩
    exact fun y hy => Or.inr ⟨⟨k, hk⟩, hf hy⟩

theorem exists_covering_profile (data : LineCoverData V) (L : LowerCovers n V)
    (seed A : Set V) (hA : IsCofinal A)
    (htype : typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    ∃ f : Profile, A ⊆ cover data L seed f := by
  classical
  have hdecomp (i : W1) : ∃ D : Set (Set V), D.Countable ∧ ⋃₀ D = rowSection data A i ∧
      ∀ B ∈ D, typeLT B = 1 ∨ ∃ k : ℕ, k < n ∧ ∃ endpoint : V,
        endpoint ≤ data.cut i ∧ B ⊆ Set.Iio endpoint ∧ IsCofinal (below B endpoint) ∧
          typeLT (below B endpoint) = (ω_ 1 : Ordinal.{0}) ^ ((k + 1 : ℕ) : Ordinal) := by
    apply exists_bounded_cofinal_power_decomposition n (rowSection data A i) (data.cut i)
    · intro x hx
      exact hx.2 ▸ data.lt_cut_row x
    · exact (cofinal_row_type_lt data A hA i).trans_eq htype
  choose D hD hDcover hDpieces using hdecomp
  have hDsub (i : W1) (B : D i) : B.val ⊆ rowSection data A i := by
    intro x hx
    rw [← hDcover i]
    exact ⟨B.val, B.property, hx⟩
  have hpc (i : W1) (B : D i) : Nonempty (PieceCover data L i B.val) :=
    exists_pieceCover data L i B.val (fun x hx => (hDsub i B hx).2)
      (fun x hx => (hDsub i B hx).2 ▸ data.lt_cut_row x) (hDpieces i B.val B.property)
  let pc (i : W1) (B : D i) : PieceCover data L i B.val := Classical.choice (hpc i B)
  let endpoint (i : W1) (B : D i) : V := (pc i B).endpoint
  obtain ⟨f0, hf0⟩ := covers_of_countable_prefixes data (endpointSupport D endpoint)
    (endpointSupport_prefix_countable data D hD endpoint (fun i B => (pc i B).row_witness))
  have hfunctions (i : W1) : ∃ f : W1 → W1, ∀ B : D i, (pc i B).function ≤ f := by
    let : Countable (D i) := hD i
    obtain ⟨f, hf⟩ := exists_pointwise_bound (Set.univ : Set (D i))
      (Set.to_countable _) (fun B => (pc i B).function)
    exact ⟨f, fun B => hf B (Set.mem_univ B)⟩
  choose F hF using hfunctions
  refine ⟨profile f0 F, ?_⟩
  intro x hx
  let i : W1 := data.row x
  have hxrow : x ∈ rowSection data A i := ⟨hx, rfl⟩
  rw [← hDcover i] at hxrow
  obtain ⟨B, hB, hxB⟩ := hxrow
  let piece : D i := ⟨B, hB⟩
  have he : (pc i piece).endpoint ∈ data.cover f0 := by
    apply hf0
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self piece⟩
  rcases (pc i piece).covered x hxB with hxe | ⟨k, hxk⟩
  · exact Or.inr (Or.inl (hxe ▸ he))
  · refine Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩))
    refine Set.mem_iUnion.mpr ⟨(pc i piece).endpoint, Set.mem_iUnion.mpr
      ⟨⟨he, (pc i piece).endpoint_le⟩, Set.mem_iUnion.mpr ⟨k, rfl, ?_⟩⟩⟩
    exact L.mono (pc i piece).endpoint k (hF i piece) hxk

end Erdos1172Part3CofinalPowerCoverCoverage
