/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3BHTRedCoreSectionBarrier
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

open Cardinal Ordinal Set Function

/-!
# Unary indivisibility of powers of omega

This file supplies the ordinal-arithmetic fact needed to pass from the
short red-compatible section of a BHT core to a full-type complementary
blue column.  The point of doing this here, rather than bounding an
interleaved union by ordinary ordinal addition, is that the latter bound
is false.

We first realize the Hessenberg natural sum by adding finite Cantor
normal-form coefficient functions.  Colexicographic order on those
finitely supported functions is the order of their evaluations, so the
result is strictly monotone in both variables.  This gives the standard
mixed-sum bound and hence unary indivisibility of every nonzero power of
`omega`.
-/

namespace Erdos1172OrdinalUnaryIndivisibility

universe u

/-! ## Finite Cantor coefficients -/

/-- The natural number represented by an ordinal below `omega`; values
outside that initial segment are sent to zero. -/
noncomputable def finiteOrdinalToNat (o : Ordinal.{u}) : ℕ :=
  if h : o < ω then Classical.choose (Ordinal.lt_omega0.mp h) else 0

theorem finiteOrdinalToNat_cast {o : Ordinal.{u}} (ho : o < ω) :
    (finiteOrdinalToNat o : Ordinal.{u}) = o := by
  rw [finiteOrdinalToNat, dif_pos ho]
  exact (Classical.choose_spec (Ordinal.lt_omega0.mp ho)).symm

@[simp] theorem finiteOrdinalToNat_zero :
    finiteOrdinalToNat (0 : Ordinal.{u}) = 0 := by
  apply Nat.cast_injective (R := Ordinal.{u})
  simpa using
    (finiteOrdinalToNat_cast
      (o := (0 : Ordinal.{u})) (Ordinal.natCast_lt_omega0 0))

/-- Every coefficient in base-`omega` Cantor normal form is finite. -/
theorem coeff_omega_lt (o e : Ordinal.{u}) :
    Ordinal.CNF.coeff ω o e < ω := by
  by_cases he : e ∈ (Ordinal.CNF.coeff ω o).support
  · rw [Ordinal.CNF.support_coeff, List.mem_toFinset,
      List.mem_map] at he
    obtain ⟨⟨e', c⟩, he'c, rfl⟩ := he
    rw [Ordinal.CNF.coeff_of_mem_CNF he'c]
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 he'c
  · rw [Finsupp.notMem_support_iff.mp he]
    exact Ordinal.natCast_lt_omega0 0

/-- Cantor coefficients, represented in `Nat` so that coefficientwise
addition is commutative and strictly monotone on both sides. -/
noncomputable def natCoeff (o : Ordinal.{u}) : Ordinal.{u} →₀ ℕ :=
  (Ordinal.CNF.coeff ω o).mapRange finiteOrdinalToNat
    finiteOrdinalToNat_zero

/-- Cast a finitely supported family of natural coefficients back to
ordinal coefficients. -/
noncomputable def castCoeff
    (f : Ordinal.{u} →₀ ℕ) : Ordinal.{u} →₀ Ordinal.{u} :=
  f.mapRange (fun n : ℕ ↦ (n : Ordinal.{u})) (Nat.cast_zero)

@[simp] theorem castCoeff_apply
    (f : Ordinal.{u} →₀ ℕ) (e : Ordinal.{u}) :
    castCoeff f e = (f e : Ordinal.{u}) := by
  simp [castCoeff]

theorem castCoeff_add (f g : Ordinal.{u} →₀ ℕ) :
    castCoeff (f + g) = castCoeff f + castCoeff g := by
  ext e
  simp [castCoeff, Nat.cast_add]

theorem castCoeff_single (e : Ordinal.{u}) (n : ℕ) :
    castCoeff (Finsupp.single e n) =
      Finsupp.single e (n : Ordinal.{u}) := by
  ext d
  by_cases hed : e = d
  · subst d
    simp
  · simp [hed]

theorem castCoeff_support (f : Ordinal.{u} →₀ ℕ) :
    (castCoeff f).support = f.support := by
  simpa [castCoeff] using
    (Finsupp.support_mapRange_of_injective
      (e := fun n : ℕ ↦ (n : Ordinal.{u})) (Nat.cast_zero) f
        Nat.cast_injective)

theorem castCoeff_natCoeff (o : Ordinal.{u}) :
    castCoeff (natCoeff o) = Ordinal.CNF.coeff ω o := by
  ext e
  simp only [castCoeff_apply, natCoeff, Finsupp.mapRange_apply]
  exact finiteOrdinalToNat_cast (coeff_omega_lt o e)

/-- Evaluate a finite natural Cantor coefficient family. -/
noncomputable def evalNatCoeff
    (f : Ordinal.{u} →₀ ℕ) : Ordinal.{u} :=
  Ordinal.CNF.eval ω (castCoeff f)

theorem evalNatCoeff_natCoeff (o : Ordinal.{u}) :
    evalNatCoeff (natCoeff o) = o := by
  rw [evalNatCoeff, castCoeff_natCoeff, Ordinal.CNF.eval_coeff]

/-! ## Colexicographic evaluation -/

private noncomputable def highPart
    (e : Ordinal.{u}) (f : Ordinal.{u} →₀ ℕ) : Ordinal.{u} →₀ ℕ :=
  f.filter (e < ·)

private noncomputable def lowPart
    (e : Ordinal.{u}) (f : Ordinal.{u} →₀ ℕ) : Ordinal.{u} →₀ ℕ :=
  f.filter (· < e)

private theorem coeff_decomposition
    (e : Ordinal.{u}) (f : Ordinal.{u} →₀ ℕ) :
    highPart e f + Finsupp.single e (f e) + lowPart e f = f := by
  ext d
  rcases lt_trichotomy d e with hde | rfl | hed
  · have hnot : ¬ e < d := not_lt_of_ge hde.le
    simp [highPart, lowPart, hde, hnot, hde.ne]
  · simp [highPart, lowPart]
  · have hnot : ¬ d < e := not_lt_of_ge hed.le
    simp [highPart, lowPart, hed, hnot, hed.ne]

private theorem highPart_eq_of_colex_witness
    {f g : Ordinal.{u} →₀ ℕ} {e : Ordinal.{u}}
    (h : ∀ d, e < d → f d = g d) : highPart e f = highPart e g := by
  ext d
  by_cases hed : e < d
  · simp [highPart, hed, h d hed]
  · simp [highPart, hed]

private theorem castCoeff_low_support
    (e : Ordinal.{u}) (f : Ordinal.{u} →₀ ℕ) :
    ∀ d ∈ (castCoeff (lowPart e f)).support, d < e := by
  intro d hd
  rw [castCoeff_support, lowPart, Finsupp.support_filter,
    Finset.mem_filter] at hd
  exact hd.2

private theorem evalNatCoeff_low_lt
    (e : Ordinal.{u}) (f : Ordinal.{u} →₀ ℕ) :
    evalNatCoeff (lowPart e f) < ω ^ e := by
  apply Ordinal.CNF.eval_lt
  · intro d
    rw [castCoeff_apply]
    exact Ordinal.natCast_lt_omega0 _
  · exact castCoeff_low_support e f

private theorem castCoeff_high_rest_eval
    (e : Ordinal.{u}) (f : Ordinal.{u} →₀ ℕ) :
    Ordinal.CNF.eval ω
        (castCoeff (highPart e f) +
          (castCoeff (Finsupp.single e (f e)) +
            castCoeff (lowPart e f))) =
      Ordinal.CNF.eval ω (castCoeff (highPart e f)) +
        Ordinal.CNF.eval ω
          (castCoeff (Finsupp.single e (f e)) +
            castCoeff (lowPart e f)) := by
  apply Ordinal.CNF.eval_add
  intro eHigh heHigh eRest heRest
  rw [castCoeff_support, highPart, Finsupp.support_filter,
    Finset.mem_filter] at heHigh
  have heRest' := Finsupp.support_add heRest
  rcases Finset.mem_union.mp heRest' with heAt | heLow
  · have heAt' : eRest = e := by
      rw [castCoeff_support] at heAt
      by_contra hne
      have hzero : Finsupp.single e (f e) eRest = 0 := by
        simp [hne]
      exact (Finsupp.mem_support_iff.mp heAt) hzero
    subst eRest
    exact heHigh.2.le
  · rw [castCoeff_support, lowPart, Finsupp.support_filter,
      Finset.mem_filter] at heLow
    exact heLow.2.le.trans heHigh.2.le

private theorem evalNatCoeff_decomposition
    (e : Ordinal.{u}) (f : Ordinal.{u} →₀ ℕ) :
    evalNatCoeff f =
      evalNatCoeff (highPart e f) +
        (ω ^ e * (f e : Ordinal.{u}) + evalNatCoeff (lowPart e f)) := by
  have hlow : ∀ d ∈ (castCoeff (lowPart e f)).support, d ≤ e :=
    fun d hd ↦ (castCoeff_low_support e f d hd).le
  calc
    evalNatCoeff f =
        evalNatCoeff
          (highPart e f + Finsupp.single e (f e) + lowPart e f) :=
      congrArg evalNatCoeff (coeff_decomposition e f).symm
    _ = Ordinal.CNF.eval ω
          (castCoeff (highPart e f) +
            (castCoeff (Finsupp.single e (f e)) +
              castCoeff (lowPart e f))) := by
      simp only [evalNatCoeff, castCoeff_add, add_assoc]
    _ = evalNatCoeff (highPart e f) +
          Ordinal.CNF.eval ω
            (castCoeff (Finsupp.single e (f e)) +
              castCoeff (lowPart e f)) :=
      castCoeff_high_rest_eval e f
    _ = evalNatCoeff (highPart e f) +
          (ω ^ e * (f e : Ordinal.{u}) +
            evalNatCoeff (lowPart e f)) := by
      rw [castCoeff_single,
        Ordinal.CNF.eval_single_add ω hlow]
      rfl

/-- Evaluation of natural Cantor coefficients is strictly increasing in
colexicographic order. -/
theorem evalNatCoeff_strictMono :
    StrictMono (fun f : Colex (Ordinal.{u} →₀ ℕ) ↦
      evalNatCoeff (ofColex f)) := by
  intro f g hfg
  obtain ⟨e, hhigh, he⟩ := Finsupp.Colex.lt_iff.mp hfg
  have hhighEq : highPart e (ofColex f) = highPart e (ofColex g) :=
    highPart_eq_of_colex_witness hhigh
  change evalNatCoeff (ofColex f) < evalNatCoeff (ofColex g)
  rw [evalNatCoeff_decomposition e (ofColex f),
    evalNatCoeff_decomposition e (ofColex g), hhighEq]
  apply add_lt_add_right
  have hlowF := evalNatCoeff_low_lt e (ofColex f)
  have hcoeffStep :
      ω ^ e * ((ofColex f) e : Ordinal.{u}) +
          evalNatCoeff (lowPart e (ofColex f)) <
        ω ^ e * (((ofColex f) e + 1 : ℕ) : Ordinal.{u}) := by
    simpa [Nat.cast_add, add_assoc, mul_add] using
      (add_lt_add_right hlowF
        (ω ^ e * ((ofColex f) e : Ordinal.{u})))
  have hsuccLe : (ofColex f) e + 1 ≤ (ofColex g) e :=
    Nat.succ_le_iff.mpr he
  exact hcoeffStep.trans_le <| by
    simpa [Nat.cast_add] using
      (mul_le_mul_right (Nat.cast_le.mpr hsuccLe) (ω ^ e)).trans
        (le_add_right le_rfl)

/-! ## Hessenberg natural sum -/

/-- Cantor coefficients reflect ordinal order into colexicographic
order.  This is obtained from the strict evaluation theorem and the
fact that `natCoeff` is a right inverse of evaluation. -/
theorem natCoeff_colex_strictMono :
    StrictMono (fun o : Ordinal.{u} ↦ toColex (natCoeff o)) := by
  intro a b hab
  rcases lt_trichotomy (toColex (natCoeff a))
      (toColex (natCoeff b)) with hlt | heq | hgt
  · exact hlt
  · have habEq : a = b := by
      calc
        a = evalNatCoeff (natCoeff a) := (evalNatCoeff_natCoeff a).symm
        _ = evalNatCoeff (natCoeff b) := by
          exact congrArg (fun f : Colex (Ordinal.{u} →₀ ℕ) ↦
            evalNatCoeff (ofColex f)) heq
        _ = b := evalNatCoeff_natCoeff b
    exact (hab.ne habEq).elim
  · have hba : b < a := by
      have hbaEval := evalNatCoeff_strictMono hgt
      change evalNatCoeff (natCoeff b) < evalNatCoeff (natCoeff a) at hbaEval
      simpa only [evalNatCoeff_natCoeff] using hbaEval
    exact (hab.asymm hba).elim

/-- Hessenberg natural sum, defined by coefficientwise addition of the
finite base-`omega` Cantor coefficients. -/
noncomputable def naturalSum
    (a b : Ordinal.{u}) : Ordinal.{u} :=
  evalNatCoeff (natCoeff a + natCoeff b)

theorem naturalSum_comm (a b : Ordinal.{u}) :
    naturalSum a b = naturalSum b a := by
  simp [naturalSum, add_comm]

@[simp] theorem naturalSum_zero_right (a : Ordinal.{u}) :
    naturalSum a 0 = a := by
  have hzero : natCoeff 0 = 0 := by
    ext e
    apply Nat.cast_injective (R := Ordinal.{u})
    rw [← castCoeff_apply, castCoeff_natCoeff,
      Ordinal.CNF.coeff_zero_apply]
    simp
  rw [naturalSum, hzero, add_zero, evalNatCoeff_natCoeff]

@[simp] theorem naturalSum_zero_left (a : Ordinal.{u}) :
    naturalSum 0 a = a := by
  rw [naturalSum_comm, naturalSum_zero_right]

theorem naturalSum_strictMono_left (b : Ordinal.{u}) :
    StrictMono (fun a ↦ naturalSum a b) := by
  intro a a' haa'
  apply evalNatCoeff_strictMono
  change toColex (natCoeff a) + toColex (natCoeff b) <
    toColex (natCoeff a') + toColex (natCoeff b)
  simpa [add_comm] using
    (add_lt_add_right (natCoeff_colex_strictMono haa')
      (toColex (natCoeff b)))

theorem naturalSum_strictMono_right (a : Ordinal.{u}) :
    StrictMono (naturalSum a) := by
  intro b b' hbb'
  rw [naturalSum_comm a b, naturalSum_comm a b']
  exact naturalSum_strictMono_left a hbb'

theorem natCoeff_support_lt_of_lt_opow
    {a e : Ordinal.{u}} (ha : a < ω ^ e) :
    ∀ d ∈ (natCoeff a).support, d < e := by
  intro d hd
  by_contra hde
  have hed : e ≤ d := le_of_not_gt hde
  have had : a < ω ^ d :=
    ha.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos hed)
  have hcoeffZero : Ordinal.CNF.coeff ω a d = 0 :=
    Ordinal.CNF.coeff_eq_zero_of_lt had
  have hnatZero : natCoeff a d = 0 := by
    apply Nat.cast_injective (R := Ordinal.{u})
    rw [← castCoeff_apply, castCoeff_natCoeff, hcoeffZero]
    simp
  exact (Finsupp.mem_support_iff.mp hd) hnatZero

/-- Natural sum preserves every initial segment of the form
`omega ^ e`. -/
theorem naturalSum_lt_opow
    {a b e : Ordinal.{u}} (ha : a < ω ^ e) (hb : b < ω ^ e) :
    naturalSum a b < ω ^ e := by
  apply Ordinal.CNF.eval_lt
  · intro d
    rw [castCoeff_apply]
    exact Ordinal.natCast_lt_omega0 _
  · intro d hd
    rw [castCoeff_support] at hd
    rcases Finset.mem_union.mp (Finsupp.support_add hd) with hda | hdb
    · exact natCoeff_support_lt_of_lt_opow ha d hda
    · exact natCoeff_support_lt_of_lt_opow hb d hdb

/-! ## Mixed sums and unary partitions -/

variable {X : Type*} [LinearOrder X] [WellFoundedLT X]

/-- The part of `s` strictly before `x`, still ordered as a subtype of
`s`. -/
def prefixIn (s : Set X) (x : X) : Set s :=
  {y | (y : X) < x}

def prefixType (s : Set X) (x : X) : Ordinal :=
  typeLT (prefixIn s x)

theorem prefixType_mono (s : Set X) {x y : X} (hxy : x ≤ y) :
    prefixType s x ≤ prefixType s y := by
  apply Ordinal.type_mono
  intro z hz
  exact hz.trans_le hxy

theorem prefixType_lt (s : Set X) (x : X) (hx : x ∈ s) :
    prefixType s x < typeLT s := by
  let xs : s := ⟨x, hx⟩
  change typeLT (Set.Iio xs) < typeLT s
  rw [Ordinal.type_Iio_lt]
  exact Ordinal.typein_lt_type (r := (· < ·)) xs

theorem prefixType_strict_of_mem (s : Set X) {x y : X}
    (hx : x ∈ s) (hxy : x < y) :
    prefixType s x < prefixType s y := by
  let xs : s := ⟨x, hx⟩
  let withX : Set s := Set.insert xs (prefixIn s x)
  have hbefore : ∀ z ∈ prefixIn s x, z < xs := by
    intro z hz
    exact hz
  have hwithType : typeLT withX = prefixType s x + 1 := by
    exact Ordinal.typeLT_insert_of_forall_lt hbefore
  have hwithSub : withX ⊆ prefixIn s y := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hxy
    · exact hz.trans hxy
  have hmono := Ordinal.type_mono hwithSub
  rw [hwithType] at hmono
  exact (lt_add_one (prefixType s x)).trans_le hmono

/-- Any strictly increasing ordinal-valued rank which stays below `o`
bounds the order type of its domain by `o`. -/
theorem typeLT_le_of_strictMono_bounded
    {o : Ordinal} (rank : X → Ordinal) (hrank : StrictMono rank)
    (hbound : ∀ x, rank x < o) : typeLT X ≤ o := by
  let _ : IsWellOrder X (· < ·) :=
    { wf := wellFounded_lt
      trichotomous := fun a b hab hba ↦
        le_antisymm (le_of_not_gt hba) (le_of_not_gt hab) }
  have htypeinLe : ∀ x : X, Ordinal.typein (r := (· < ·)) x ≤ rank x := by
    intro x
    refine WellFoundedLT.induction
      (motive := fun z : X ↦
        Ordinal.typein (r := (· < ·)) z ≤ rank z) x ?_
    intro x ih
    apply le_of_not_gt
    intro hlt
    obtain ⟨y, hy⟩ := Ordinal.typein_surj (· < ·) (hlt.trans (Ordinal.typein_lt_type (· < ·) x))
    have hyx : y < x := (Ordinal.typein_lt_typein (· < ·)).mp (hy.symm ▸ hlt)
    exact (hrank hyx).not_ge (hy ▸ ih y hyx)
  apply le_of_not_gt
  intro hotype
  obtain ⟨x, hx⟩ := Ordinal.typein_surj (r := (· < ·)) hotype
  have := (htypeinLe x).trans_lt (hbound x)
  rw [hx] at this
  exact (lt_irrefl o) this

/-- The order type of an arbitrary interleaving of two well-orders is
bounded by the Hessenberg natural sum of the two component types. -/
theorem typeLT_le_naturalSum_partition (s : Set X) :
    typeLT X ≤ naturalSum (typeLT s) (typeLT (sᶜ : Set X)) := by
  let rank : X → Ordinal := fun x ↦
    naturalSum (prefixType s x) (prefixType (sᶜ : Set X) x)
  have hrank : StrictMono rank := by
    intro x y hxy
    by_cases hx : x ∈ s
    · have hleft : prefixType s x < prefixType s y :=
        prefixType_strict_of_mem s hx hxy
      have hright : prefixType (sᶜ : Set X) x ≤
          prefixType (sᶜ : Set X) y :=
        prefixType_mono (sᶜ : Set X) hxy.le
      exact (naturalSum_strictMono_left _ hleft).trans_le
        ((naturalSum_strictMono_right _).monotone hright)
    · have hxCompl : x ∈ (sᶜ : Set X) := by simpa
      have hleft : prefixType s x ≤ prefixType s y :=
        prefixType_mono s hxy.le
      have hright : prefixType (sᶜ : Set X) x <
          prefixType (sᶜ : Set X) y :=
        prefixType_strict_of_mem (sᶜ : Set X) hxCompl hxy
      exact ((naturalSum_strictMono_left _).monotone hleft).trans_lt
        (naturalSum_strictMono_right _ hright)
  apply typeLT_le_of_strictMono_bounded rank hrank
  intro x
  by_cases hx : x ∈ s
  · have hright : prefixType (sᶜ : Set X) x ≤
        typeLT (sᶜ : Set X) :=
      Ordinal.type_set_le (prefixIn (sᶜ : Set X) x)
    exact ((naturalSum_strictMono_right (prefixType s x)).monotone
      hright).trans_lt
        (naturalSum_strictMono_left (typeLT (sᶜ : Set X))
          (prefixType_lt s x hx))
  · have hxCompl : x ∈ (sᶜ : Set X) := by simpa
    have hleft : prefixType s x ≤ typeLT s :=
      Ordinal.type_set_le (prefixIn s x)
    exact ((naturalSum_strictMono_left
      (prefixType (sᶜ : Set X) x)).monotone hleft).trans_lt
        (naturalSum_strictMono_right (typeLT s)
          (prefixType_lt (sᶜ : Set X) x hxCompl))

/-- Every power of `omega` is unary-indivisible: one side of
any two-piece partition retains the whole order type. -/
theorem typeLT_eq_opow_or_compl_eq_opow
    {e : Ordinal} {s : Set X}
    (htype : typeLT X = ω ^ e) :
    typeLT s = ω ^ e ∨ typeLT (sᶜ : Set X) = ω ^ e := by
  have hsLe : typeLT s ≤ ω ^ e := by
    rw [← htype]
    exact Ordinal.type_set_le s
  have hcLe : typeLT (sᶜ : Set X) ≤ ω ^ e := by
    rw [← htype]
    exact Ordinal.type_set_le (sᶜ : Set X)
  rcases hsLe.eq_or_lt with hsEq | hsLt
  · exact Or.inl hsEq
  rcases hcLe.eq_or_lt with hcEq | hcLt
  · exact Or.inr hcEq
  exfalso
  have hmixed := typeLT_le_naturalSum_partition s
  rw [htype] at hmixed
  exact (not_le_of_gt (naturalSum_lt_opow hsLt hcLt)) hmixed

end Erdos1172OrdinalUnaryIndivisibility
