/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.BaseFundamentalCyclic
import InverseGalois.CFT.Units.DecompositionPlaceInjective

/-!
# Localising the fundamental class at a finite place

The second cohomology of the units of a completion at a finite place is the second cohomology of
the idele class group read on the decomposition group there.  Inverting that isomorphism sends a
class of the idele class group, restricted to a decomposition group, to a class of the units of the
completion: this is the localisation of a global class at a place.

Applied to the fundamental class of the extension it produces, at every finite place, a class of
the decomposition group with values in the units of the completion whose ideles are the restriction
of the fundamental class.  That class is a fundamental class in its own right.  Only the multiples
of the order of the decomposition group annihilate it, because only the multiples of that order
annihilate the restriction of the global class; it therefore generates, its order is the degree of
the extension of the completions, and its invariant under local class field theory is a rational
with exactly that denominator.  In particular it is the local fundamental class up to a multiple
prime to the local degree, and each of the two classes is a multiple of the other.

The point of localising rather than choosing is that the classical hypotheses of Tate's theorem
hold for the localised class on every subgroup of the decomposition group, exactly as they do for
the local fundamental class, while its relation to the global class is an equation rather than a
comparison of invariants.

## Main definitions

* `InverseGalois.CFT.decompositionLocalization`: **the localisation isomorphism at a finite
  place**, from the second cohomology of the idele class group on the decomposition group to the
  second cohomology of the units of the completion.
* `InverseGalois.CFT.localizedFundamentalClass`: **the fundamental class of the extension,
  localised at a finite place.**

## Main results

* `InverseGalois.CFT.map_localizedFundamentalClass`: **the ideles of the localised fundamental
  class are the restriction of the fundamental class to the decomposition group.**
* `InverseGalois.CFT.zsmul_localizedFundamentalClass_eq_zero_imp_dvd`,
  `InverseGalois.CFT.addOrderOf_localizedFundamentalClass`,
  `InverseGalois.CFT.zmultiples_localizedFundamentalClass_eq_top`: **only the multiples of the
  order of the decomposition group annihilate the localised fundamental class, and it generates.**
* `InverseGalois.CFT.isTateClassTwo_localizedFundamentalClass`: **the classical hypotheses of
  Tate's theorem hold for the localised fundamental class on every subgroup of the decomposition
  group.**
* `InverseGalois.CFT.orderOf_decompositionInvariant_localizedFundamentalClass`: **the invariant of
  the localised fundamental class has order the degree of the extension of the completions.**

## Tags

number field, idele class group, decomposition group, fundamental class, localisation, invariant,
Tate cohomology
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain Module MulAction NumberField Tate groupCohomology

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The localisation isomorphism at a finite place**: the second cohomology of the idele class
group, read on the decomposition group at the place, is the second cohomology of the units of the
completion there. -/
def decompositionLocalization :
    ↥(tateModule (resObj (stabilizer Gal(K/k) w) (ideleClassRep k K)) 2) ≃ₗ[ℤ]
      ↥(tateModule (decompositionUnitsRep k w) 2) :=
  (LinearEquiv.ofBijective
    ((groupCohomology.functor ℤ ↥(stabilizer Gal(K/k) w) 2).map
      (decompositionPlaceIdeleClass k w)).hom
    (bijective_map_H2_decompositionPlaceIdeleClass k w)).symm

variable (k) in
/-- **The fundamental class of the extension, localised at a finite place.** -/
def localizedFundamentalClass : ↥(tateModule (decompositionUnitsRep k w) 2) :=
  decompositionLocalization k w
    (tateRes (stabilizer Gal(K/k) w) (ideleClassRep k K) 2 (baseFundamentalClass k K))

variable (k) in
/-- **The ideles of the localised fundamental class are the restriction of the fundamental class to
the decomposition group.** -/
theorem map_localizedFundamentalClass :
    ((groupCohomology.functor ℤ ↥(stabilizer Gal(K/k) w) 2).map
        (decompositionPlaceIdeleClass k w)).hom (localizedFundamentalClass k w)
      = tateRes (stabilizer Gal(K/k) w) (ideleClassRep k K) 2 (baseFundamentalClass k K) :=
  (LinearEquiv.ofBijective _ (bijective_map_H2_decompositionPlaceIdeleClass k w)).apply_symm_apply _

variable (k) in
/-- **Only the multiples of the order of a decomposition group annihilate the localised fundamental
class.**  Its ideles are the restriction of the fundamental class, which is annihilated by exactly
those multiples, and the localisation is injective. -/
theorem zsmul_localizedFundamentalClass_eq_zero_imp_dvd (m : ℤ)
    (hm : m • localizedFundamentalClass k w = 0) :
    (Nat.card ↥(stabilizer Gal(K/k) w) : ℤ) ∣ m := by
  refine (isTateClassTwo_baseFundamentalClass k K
    (stabilizer Gal(K/k) w)).dvd_of_zsmul_eq_zero m ?_
  refine (decompositionLocalization k w).injective ?_
  rw [map_zsmul, map_zero]
  exact hm

variable (k) in
/-- **The localised fundamental class has order the order of the decomposition group.** -/
theorem addOrderOf_localizedFundamentalClass :
    addOrderOf (localizedFundamentalClass k w) = Nat.card ↥(stabilizer Gal(K/k) w) := by
  refine Nat.dvd_antisymm (addOrderOf_dvd_iff_nsmul_eq_zero.2
    (card_nsmul_eq_zero_tateModule (decompositionUnitsRep k w) 2 _)) ?_
  have h : ((addOrderOf (localizedFundamentalClass k w) : ℤ)) •
      localizedFundamentalClass k w = 0 := by
    rw [natCast_zsmul]
    exact addOrderOf_nsmul_eq_zero _
  exact_mod_cast zsmul_localizedFundamentalClass_eq_zero_imp_dvd k w _ h

variable (k) in
/-- **The localised fundamental class generates the second cohomology of the units of the
completion.** -/
theorem exists_zsmul_localizedFundamentalClass (y : ↥(tateModule (decompositionUnitsRep k w) 2)) :
    ∃ m : ℤ, y = m • localizedFundamentalClass k w := by
  haveI : Finite ↥(tateModule (decompositionUnitsRep k w) 2) :=
    finite_tateModule_decompositionUnits k w
  have hcard : Nat.card ↥(tateModule (decompositionUnitsRep k w) 2)
      ≤ Nat.card ↥(stabilizer Gal(K/k) w) := (natCard_H2_decompositionUnits k w).le
  exact exists_zsmul_of_card_le hcard (zsmul_localizedFundamentalClass_eq_zero_imp_dvd k w) y

variable (k) in
/-- **The multiples of the localised fundamental class exhaust the second cohomology of the units
of the completion.** -/
theorem zmultiples_localizedFundamentalClass_eq_top :
    AddSubgroup.zmultiples (localizedFundamentalClass k w) = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).2 fun y => ?_
  obtain ⟨m, hm⟩ := exists_zsmul_localizedFundamentalClass k w y
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨m, hm.symm⟩

variable (k) in
/-- **The classical hypotheses of Tate's theorem hold for the localised fundamental class, on every
subgroup of the decomposition group.**  The cohomology of the units of the completion vanishes in
degree one by Hilbert's theorem 90, it has exactly as many elements as the subgroup in degree two
by local reciprocity, and the localised class is annihilated by exactly the multiples of the order
of the decomposition group. -/
theorem isTateClassTwo_localizedFundamentalClass (S : Subgroup ↥(stabilizer Gal(K/k) w)) :
    IsTateClassTwo S (decompositionUnitsRep k w) (localizedFundamentalClass k w) :=
  isTateClassTwo_of_card_le S (isZero_tateModule_resObj_decompositionUnits_one k w S)
    (finite_tateModule_resObj_decompositionUnits_two k w S)
    (natCard_tateModule_resObj_decompositionUnits_two k w S).le
    (zsmul_localizedFundamentalClass_eq_zero_imp_dvd k w)

variable (k) in
/-- **The invariant of the localised fundamental class has order the degree of the extension of the
completions**, so it is a rational with exactly that denominator. -/
theorem orderOf_decompositionInvariant_localizedFundamentalClass :
    orderOf (decompositionInvariant k w
        (Multiplicative.ofAdd (localizedFundamentalClass k w)))
      = finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  rw [orderOf_injective _ (decompositionInvariant_injective k w),
    ← natCard_stabilizer_eq_finrank k w, ← addOrderOf_localizedFundamentalClass k w]
  rfl

variable (k) in
/-- **The localised fundamental class is a multiple of the local fundamental class.** -/
theorem exists_zsmul_localFundamentalClass_eq :
    ∃ m : ℤ, localizedFundamentalClass k w
      = m • Multiplicative.toAdd (localFundamentalClass k w) := by
  haveI : Finite ↥(tateModule (decompositionUnitsRep k w) 2) :=
    finite_tateModule_decompositionUnits k w
  have hcard : Nat.card ↥(tateModule (decompositionUnitsRep k w) 2)
      ≤ Nat.card ↥(stabilizer Gal(K/k) w) := (natCard_H2_decompositionUnits k w).le
  exact exists_zsmul_of_card_le hcard (dvd_of_zsmul_localFundamentalClass_eq_zero k w) _

variable (k) in
/-- **The local fundamental class is a multiple of the localised fundamental class.** -/
theorem exists_zsmul_localizedFundamentalClass_eq :
    ∃ m : ℤ, Multiplicative.toAdd (localFundamentalClass k w)
      = m • localizedFundamentalClass k w :=
  exists_zsmul_localizedFundamentalClass k w _

end

end InverseGalois.CFT
