/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Chart

/-!
# The residue field of a place

A place is a local ring, and the field it leaves behind when its maximal ideal is divided out is
its residue field — the field of values that functions regular at the place take there.  Computing
it is what makes the degree of a place computable.

Seen from a chart containing the place, the residue field is the quotient of the chart by the
prime under the place.  The map from the chart to the residue field kills exactly that prime, and
it is onto: a function regular at the place is a fraction whose denominator avoids the prime, and
the quotient of the chart by a prime of a Dedekind domain is already a field, so the denominator is
invertible there.

## Main definitions

* `Rigidity.RET.toPlaceSubring` — the chart, viewed inside the place of one of its primes.
* `Rigidity.RET.chartResidue` — the value at the place of a function of the chart.
* `Rigidity.RET.residueFieldEquiv` — the residue field of the place of a prime is the quotient of
  the chart by that prime.
-/

open IsDedekindDomain

noncomputable section


namespace Rigidity.RET

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
variable (F : Type*) [Field F] [Algebra B F] [IsFractionRing B F]

/-! ## The chart inside a place -/

/-- **The chart, viewed inside the place of one of its primes.** -/
def toPlaceSubring (v : HeightOneSpectrum B) : B →+* placeSubring F v :=
  (algebraMap B F).codRestrict _ (algebraMap_mem_placeSubring F v)

@[simp]
theorem coe_toPlaceSubring (v : HeightOneSpectrum B) (b : B) :
    ((toPlaceSubring F v b : placeSubring F v) : F) = algebraMap B F b := rfl

/-- **The value at a place of a function of the chart.** -/
def chartResidue (v : HeightOneSpectrum B) : B →+* IsLocalRing.ResidueField (placeSubring F v) :=
  (IsLocalRing.residue _).comp (toPlaceSubring F v)

/-- **A function of the chart vanishes at the place exactly when it lies in the prime.** -/
theorem chartResidue_eq_zero_iff (v : HeightOneSpectrum B) (b : B) :
    chartResidue F v b = 0 ↔ b ∈ v.asIdeal := by
  have hunder : underPrime (placeSubring F v) (algebraMap_mem_placeSubring F v) = v.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal (underPlace_placeSubring (F := F) v)
  rw [chartResidue, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff, ← hunder, mem_underPrime, coe_toPlaceSubring]

theorem chartResidue_ker (v : HeightOneSpectrum B) :
    RingHom.ker (chartResidue F v) = v.asIdeal :=
  Ideal.ext fun b => chartResidue_eq_zero_iff F v b

/-- **Every value at a place is the value of a function of the chart.**

A function regular at the place is a fraction whose denominator avoids the prime; the quotient of
the chart by the prime is a field, so the denominator has an inverse there already. -/
theorem chartResidue_surjective (v : HeightOneSpectrum B) :
    Function.Surjective (chartResidue F v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  rcases eq_or_ne (x : F) 0 with hx0 | hx0
  · refine ⟨0, ?_⟩
    have hx : x = 0 := Subtype.ext hx0
    rw [hx, map_zero, map_zero]
  obtain ⟨a, s, hs, hsa⟩ := exists_den_notMem_of_ord_nonneg F v ((mem_placeSubring F v hx0).mp x.2)
  obtain ⟨t, i, hi, hti⟩ := (HeightOneSpectrum.isMaximal v).exists_inv hs
  refine ⟨a * t, ?_⟩
  have hmul : toPlaceSubring F v s * x = toPlaceSubring F v a := Subtype.ext (by simpa using hsa)
  have hres : chartResidue F v s * IsLocalRing.residue _ x = chartResidue F v a := by
    rw [chartResidue, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hmul]
  have hi0 : chartResidue F v i = 0 := (chartResidue_eq_zero_iff F v i).mpr hi
  have hts : chartResidue F v t * chartResidue F v s = 1 := by
    have h := congrArg (chartResidue F v) hti
    rwa [map_add, map_mul, hi0, add_zero, map_one] at h
  calc chartResidue F v (a * t)
      = chartResidue F v a * chartResidue F v t := map_mul _ _ _
    _ = chartResidue F v s * IsLocalRing.residue _ x * chartResidue F v t := by rw [hres]
    _ = chartResidue F v t * chartResidue F v s * IsLocalRing.residue _ x := by ring
    _ = IsLocalRing.residue _ x := by rw [hts, one_mul]

/-! ## The residue field from a chart -/

/-- **The residue field of the place of a prime is the quotient of the chart by that prime.** -/
def residueFieldEquiv (v : HeightOneSpectrum B) :
    (B ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (placeSubring F v) :=
  (Ideal.quotEquivOfEq (chartResidue_ker F v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (chartResidue_surjective F v))

@[simp]
theorem residueFieldEquiv_mk (v : HeightOneSpectrum B) (b : B) :
    residueFieldEquiv F v (Ideal.Quotient.mk v.asIdeal b) = chartResidue F v b := rfl

end Rigidity.RET
