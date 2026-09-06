/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormPlaceValue

/-!
# Prescribing the values of an element at finitely many places

Finitely many places of a number field can be given whatever values one likes by a single element
of the field.  The Chinese remainder theorem supplies an algebraic integer congruent, modulo one
more than the prescribed power of each of the chosen primes, to that power of a uniformiser there;
such an element differs from the power of the uniformiser by something of strictly smaller
valuation, so its valuation is exactly the prescribed one.  A quotient of two such integers realises
an arbitrary family of integer values.

The construction has a useful consequence for units.  An element which is a unit at each of
finitely many places is the quotient of two algebraic integers which are units at those places:
prescribe an integer whose values cancel the poles of the element and are trivial at the chosen
places, and the element times that integer is again an algebraic integer, again a unit at the
chosen places.

## Main results

* `InverseGalois.CFT.exists_forall_intValuation_eq`: **an element of a Dedekind domain with
  prescribed valuations at finitely many places.**
* `InverseGalois.CFT.exists_units_placeValue_eq`: **a unit of a number field with prescribed values
  at finitely many places.**
* `InverseGalois.CFT.exists_integral_div_of_forall_placeValue_eq_zero`: **a unit trivial at
  finitely many places is a quotient of algebraic integers trivial there.**

## Tags

Dedekind domain, number field, place, valuation, Chinese remainder theorem, uniformiser
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Prescribed valuations in a Dedekind domain -/

section Prescribe

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- **An element of a Dedekind domain with prescribed valuations at finitely many places.**  The
Chinese remainder theorem produces an element congruent to a power of a uniformiser at each of the
chosen places to one degree more accuracy than the exponent of that power, and the correction has
too small a valuation to disturb the leading term. -/
theorem exists_forall_intValuation_eq (s : Finset (HeightOneSpectrum R))
    (m : HeightOneSpectrum R → ℕ) :
    ∃ t : R, t ≠ 0 ∧ ∀ u ∈ s, u.intValuation t = WithZero.exp (-(m u : ℤ)) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
  · exact ⟨1, one_ne_zero, by simp⟩
  choose π hπ using fun u : HeightOneSpectrum R => u.intValuation_exists_uniformizer
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun u : HeightOneSpectrum R => u.asIdeal) (fun u => m u + 1)
    (fun u _ => Ideal.prime_of_isPrime u.ne_bot u.isPrime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun u : s => π (u : HeightOneSpectrum R) ^ m (u : HeightOneSpectrum R))
  have key : ∀ u ∈ s, u.intValuation t = WithZero.exp (-(m u : ℤ)) := by
    intro u hu
    have hpow : u.intValuation (π u ^ m u) = WithZero.exp (-(m u : ℤ)) := by
      rw [map_pow, hπ u, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hlt : u.intValuation (t - π u ^ m u) < u.intValuation (π u ^ m u) := by
      refine lt_of_le_of_lt ((u.intValuation_le_pow_iff_mem _ _).2 (ht u hu)) ?_
      rw [hpow, WithZero.exp_lt_exp]
      push_cast
      omega
    have h := Valuation.map_add_eq_of_lt_right (v := u.intValuation) hlt
    rw [sub_add_cancel, hpow] at h
    exact h
  refine ⟨t, ?_, key⟩
  intro hzero
  have hv := key u₀ hu₀
  rw [hzero, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

end Prescribe

/-! ### Prescribed values in a number field -/

section NumberFieldPrescribe

variable {K : Type} [Field K] [NumberField K]

/-- The value of an algebraic integer of prescribed valuation at a place. -/
theorem placeOrd_algebraMap_of_intValuation {v : HeightOneSpectrum (𝓞 K)} {t : 𝓞 K} {m : ℕ}
    (h : v.intValuation t = WithZero.exp (-(m : ℤ))) :
    placeOrd v (algebraMap (𝓞 K) K t) = -(m : ℤ) := by
  rw [placeOrd_apply, HeightOneSpectrum.valuation_of_algebraMap, h, WithZero.log_exp]

/-- **An algebraic integer has nonpositive value at every place.** -/
theorem placeOrd_le_zero_algebraMap (v : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) :
    placeOrd v (algebraMap (𝓞 K) K t) ≤ 0 := by
  rw [placeOrd_apply, HeightOneSpectrum.valuation_of_algebraMap]
  rcases eq_or_ne (v.intValuation t) 0 with h | h
  · rw [h, WithZero.log_zero]
  · rw [← WithZero.exp_le_exp, WithZero.exp_log h, WithZero.exp_zero]
    exact v.intValuation_le_one t

/-- **An element with nonpositive value at every place is an algebraic integer.** -/
theorem exists_algebraMap_eq_of_placeOrd_le_zero {x : K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), placeOrd v x ≤ 0) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one K x fun v => ?_
  rcases eq_or_ne (v.valuation K x) 0 with hv | hv
  · rw [hv]
    exact zero_le_one
  · rw [← WithZero.exp_log hv, ← WithZero.exp_zero (M := ℤ), WithZero.exp_le_exp]
    exact h v

/-- **A unit of a number field with prescribed values at finitely many places**, the quotient of
two algebraic integers whose prescribed valuations are the positive and the negative part of the
prescription. -/
theorem exists_units_placeValue_eq (T : Finset (HeightOneSpectrum (𝓞 K)))
    (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ θ : Kˣ, ∀ W ∈ T, placeValue W θ = n W := by
  obtain ⟨tp, htp0, htp⟩ := exists_forall_intValuation_eq T (fun W => (n W).toNat)
  obtain ⟨tm, htm0, htm⟩ := exists_forall_intValuation_eq T (fun W => (-n W).toNat)
  have hp : algebraMap (𝓞 K) K tp ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr htp0
  have hm : algebraMap (𝓞 K) K tm ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr htm0
  refine ⟨Units.mk0 (algebraMap (𝓞 K) K tm / algebraMap (𝓞 K) K tp) (div_ne_zero hm hp),
    fun W hW => ?_⟩
  rw [placeValue_eq_placeOrd, Units.val_mk0, placeOrd_div W hm hp,
    placeOrd_algebraMap_of_intValuation (htm W hW),
    placeOrd_algebraMap_of_intValuation (htp W hW)]
  omega

end NumberFieldPrescribe

/-! ### Units trivial at finitely many places -/

section QuotientOfIntegers

variable {k : Type} [Field k] [NumberField k]

/-- **A unit of a number field with trivial value at each of finitely many places is the quotient
of two algebraic integers with trivial value at those places.**  An integer whose values are the
poles of the unit and which is trivial at the chosen places clears the denominator without
disturbing them. -/
theorem exists_integral_div_of_forall_placeValue_eq_zero
    {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite) (a : kˣ)
    (ha : ∀ v ∈ S, placeValue v a = 0) :
    ∃ b c : kˣ, a = b / c ∧
      (∃ b' : 𝓞 k, (b : k) = algebraMap (𝓞 k) k b') ∧
      (∃ c' : 𝓞 k, (c : k) = algebraMap (𝓞 k) k c') ∧
      (∀ v ∈ S, placeValue v b = 0) ∧ (∀ v ∈ S, placeValue v c = 0) := by
  classical
  have hP : {v : HeightOneSpectrum (𝓞 k) | placeValue v a ≠ 0}.Finite := by
    simpa only [placeValue_eq_placeOrd] using finite_placeOrd_ne_zero (Units.ne_zero a)
  obtain ⟨t, ht0, ht⟩ := exists_forall_intValuation_eq (hS.union hP).toFinset
    (fun v => (placeValue v a).toNat)
  have htK : algebraMap (𝓞 k) k t ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 k) k)).mpr ht0
  set c : kˣ := Units.mk0 (algebraMap (𝓞 k) k t) htK with hcdef
  have hcord : ∀ v : HeightOneSpectrum (𝓞 k), placeValue v c ≤ 0 := fun v => by
    rw [placeValue_eq_placeOrd, hcdef, Units.val_mk0]
    exact placeOrd_le_zero_algebraMap v t
  have hcmem : ∀ v ∈ (hS.union hP).toFinset,
      placeValue v c = -((placeValue v a).toNat : ℤ) := fun v hv => by
    rw [placeValue_eq_placeOrd, hcdef, Units.val_mk0, placeOrd_algebraMap_of_intValuation (ht v hv)]
  have hmul : ∀ v : HeightOneSpectrum (𝓞 k),
      placeValue v (a * c) = placeValue v a + placeValue v c := fun v => by
    simp only [placeValue_eq_placeOrd, Units.val_mul]
    exact placeOrd_mul v (Units.ne_zero a) (Units.ne_zero c)
  have hbord : ∀ v : HeightOneSpectrum (𝓞 k), placeValue v (a * c) ≤ 0 := fun v => by
    by_cases hv : v ∈ (hS.union hP).toFinset
    · rw [hmul v, hcmem v hv]
      omega
    · have hva : placeValue v a = 0 := by
        by_contra hc
        exact hv ((hS.union hP).mem_toFinset.mpr (Or.inr hc))
      rw [hmul v, hva, zero_add]
      exact hcord v
  refine ⟨a * c, c, by simp, ?_, ⟨t, by rw [hcdef]; rfl⟩, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨y, hy⟩ := exists_algebraMap_eq_of_placeOrd_le_zero (x := ((a * c : kˣ) : k))
      fun v => by simpa only [placeValue_eq_placeOrd] using hbord v
    exact ⟨y, hy.symm⟩
  · have hvT : v ∈ (hS.union hP).toFinset := (hS.union hP).mem_toFinset.mpr (Or.inl hv)
    rw [hmul v, hcmem v hvT, ha v hv]
    simp
  · have hvT : v ∈ (hS.union hP).toFinset := (hS.union hP).mem_toFinset.mpr (Or.inl hv)
    rw [hcmem v hvT, ha v hv]
    simp

end QuotientOfIntegers

end InverseGalois.CFT
