/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Ord

/-!
# The order at a prime and the adic valuation

The order `Rigidity.RET.ord` counts the exponent of a height-one prime in the factorization of a
principal fractional ideal; Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation` measures the
same thing multiplicatively, in the value group `ℤᵐ⁰`.  The two are the same measurement in
different clothes: the valuation of `x` is `exp (-ord x)`.

Making that identification explicit imports Mathlib's valuation-theoretic results into the additive
language of divisors.  The one that matters is that a Dedekind domain is the intersection of its
localizations: an element of the fraction field with non-negative order at *every* prime already
lies in the domain.  From it follows the local description of the elements of non-negative order at
a *single* prime — they are exactly the fractions `a / s` with denominator away from that prime —
which is what identifies the abstract local ring at a prime with the localization.

## Main results

* `Rigidity.RET.valuation_eq_exp_neg_ord` — the adic valuation is `exp (-ord)`.
* `Rigidity.RET.valuation_le_one_iff_ord_nonneg` — a function is integral at a prime exactly when
  its order there is non-negative.
* `Rigidity.RET.exists_algebraMap_eq_of_ord_nonneg` — non-negative order everywhere means being in
  the domain.
* `Rigidity.RET.exists_den_notMem_of_ord_nonneg` — non-negative order at one prime means being a
  fraction whose denominator avoids that prime.
-/

open IsDedekindDomain FractionalIdeal WithZero
open scoped nonZeroDivisors

noncomputable section


namespace Rigidity.RET

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## The comparison -/

/-- **The adic valuation of an element of the domain is `exp (-ord)`.**  Both sides are read off
the same exponent in the factorization of the ideal it generates. -/
theorem intValuation_eq_exp_neg_ord (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    v.intValuation r = exp (-(ord K v (algebraMap R K r))) := by
  classical
  have hspan : (Ideal.span {r} : Ideal R) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [v.intValuation_if_neg hr, ord_algebraMap, FractionalIdeal.count_coe K v hspan]

/-- **The adic valuation of a rational function is `exp (-ord)`.** -/
theorem valuation_eq_exp_neg_ord (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = exp (-(ord K v x)) := by
  obtain ⟨⟨n, d, hd⟩, hxd⟩ := IsLocalization.surj R⁰ x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : algebraMap R K d ≠ 0 := fun h => hd0 (IsFractionRing.to_map_eq_zero_iff.mp h)
  have hnK : algebraMap R K n ≠ 0 := by
    rw [← hxd]; exact mul_ne_zero hx hdK
  have hn0 : n ≠ 0 := fun h => hnK (by rw [h, map_zero])
  have hxeq : x = algebraMap R K n / algebraMap R K d := by
    field_simp
    exact hxd
  have hmk : x = IsLocalization.mk' K n ⟨d, hd⟩ := by
    rw [IsFractionRing.mk'_eq_div]
    exact hxeq
  rw [hmk, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    intValuation_eq_exp_neg_ord K v hn0, intValuation_eq_exp_neg_ord K v hd0, ← exp_sub, ← hmk]
  congr 1
  rw [hxeq, ord_div v hnK hdK]
  ring

/-- **A function is integral at a prime exactly when its order there is non-negative.** -/
theorem valuation_le_one_iff_ord_nonneg (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x ≤ 1 ↔ 0 ≤ ord K v x := by
  rw [valuation_eq_exp_neg_ord K v hx, ← WithZero.exp_zero (M := ℤ), WithZero.exp_le_exp,
    neg_nonpos]

/-- **A Dedekind domain is the intersection of its local rings**: an element of the fraction field
with non-negative order at every prime lies in the domain. -/
theorem exists_algebraMap_eq_of_ord_nonneg {x : K} (h : ∀ v : HeightOneSpectrum R, 0 ≤ ord K v x) :
    ∃ r : R, algebraMap R K r = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, map_zero _⟩
  · exact IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x
      fun v => (valuation_le_one_iff_ord_nonneg K v hx).mpr (h v)

/-! ## The local description at a single prime -/

/-- **A function of non-negative order at a prime is a fraction whose denominator avoids that
prime.**

Split off from the denominator `d` the part supported at `v`, writing `(d) = vᵐ · J` with `J` not
divisible by `v`; any `s ∈ J` outside `v` is then a denominator that works, because multiplying by
`s` supplies at every prime other than `v` the order that `d` takes away, while at `v` itself the
hypothesis already does. -/
theorem exists_den_notMem_of_ord_nonneg (v : HeightOneSpectrum R) {x : K}
    (h : 0 ≤ ord K v x) :
    ∃ a s : R, s ∉ v.asIdeal ∧ algebraMap R K s * x = algebraMap R K a := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, 1, (Ideal.ne_top_iff_one _).mp v.isPrime.ne_top, by simp⟩
  obtain ⟨⟨n, d, hd⟩, hxd⟩ := IsLocalization.surj R⁰ x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : algebraMap R K d ≠ 0 := fun h => hd0 (IsFractionRing.to_map_eq_zero_iff.mp h)
  have hnK : algebraMap R K n ≠ 0 := by rw [← hxd]; exact mul_ne_zero hx hdK
  have hn0 : n ≠ 0 := fun h => hnK (by rw [h, map_zero])
  have hxeq : x = algebraMap R K n / algebraMap R K d := by field_simp; exact hxd
  -- the order of `x` at any prime is the difference of the orders of numerator and denominator
  have hordx : ∀ w : HeightOneSpectrum R, ord K w x
      = ord K w (algebraMap R K n) - ord K w (algebraMap R K d) := by
    intro w
    rw [hxeq, ord_div w hnK hdK]
  -- split the denominator at `v`
  obtain ⟨m, hmeq⟩ : ∃ m : ℕ, ord K v (algebraMap R K d) = (m : ℤ) :=
    ⟨(ord K v (algebraMap R K d)).toNat, (Int.toNat_of_nonneg (ord_nonneg v d)).symm⟩
  have hdvd : v.asIdeal ^ m ∣ Ideal.span {d} := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    rw [intValuation_eq_exp_neg_ord K v hd0, hmeq]
  obtain ⟨J, hJ⟩ := hdvd
  have hspand : (Ideal.span {d} : Ideal R) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hd0
  have hJ0 : J ≠ 0 := by
    rintro rfl
    exact hspand (by rw [hJ, mul_zero])
  -- the counts of the denominator, prime by prime
  have hcount : ∀ w : HeightOneSpectrum R,
      ord K w (algebraMap R K d)
        = count K w ((v.asIdeal : FractionalIdeal R⁰ K) ^ m) + count K w (J : Ideal R) := by
    intro w
    have hfrac : ((Ideal.span {d} : Ideal R) : FractionalIdeal R⁰ K)
        = (v.asIdeal : FractionalIdeal R⁰ K) ^ m * (J : Ideal R) := by
      rw [hJ, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
    have hpne : ((v.asIdeal : FractionalIdeal R⁰ K)) ^ m ≠ 0 :=
      pow_ne_zero _ (by simpa [FractionalIdeal.coeIdeal_eq_zero] using v.ne_bot)
    have hJne : ((J : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
      simpa [FractionalIdeal.coeIdeal_eq_zero] using hJ0
    rw [ord_algebraMap, hfrac, FractionalIdeal.count_mul K w hpne hJne]
  -- `v` does not divide `J`, so `J` is not contained in `v`
  have hcountJv : count K v (J : Ideal R) = 0 := by
    have := hcount v
    rw [FractionalIdeal.count_pow_self, hmeq] at this
    omega
  have hnotdvd : ¬ v.asIdeal ∣ J := by
    intro hdvdJ
    have hne : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd hJ0 v.irreducible).mpr hdvdJ
    rw [FractionalIdeal.count_coe K v hJ0] at hcountJv
    exact hne (by exact_mod_cast hcountJv)
  have hnotle : ¬ (J ≤ v.asIdeal) := fun hle => hnotdvd (Ideal.dvd_iff_le.mpr hle)
  obtain ⟨s, hsJ, hsv⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hs0 : s ≠ 0 := fun h => hsv (h ▸ Submodule.zero_mem _)
  have hsK : algebraMap R K s ≠ 0 := fun h => hs0 (IsFractionRing.to_map_eq_zero_iff.mp h)
  -- the product `s · x` is integral at every prime
  have hnonneg : ∀ w : HeightOneSpectrum R, 0 ≤ ord K w (algebraMap R K s * x) := by
    intro w
    rw [ord_mul w hsK hx, hordx w]
    rcases eq_or_ne w v with hwv | hwv
    · have h1 : 0 ≤ ord K w (algebraMap R K s) := ord_nonneg w s
      have h2 : 0 ≤ ord K w x := by rw [hwv]; exact h
      rw [hordx w] at h2
      omega
    · -- away from `v` the element `s` supplies the order that the denominator takes away
      have hle : count K w (J : Ideal R) ≤ ord K w (algebraMap R K s) := by
        rw [ord_algebraMap]
        refine FractionalIdeal.count_mono K w
          (I := ((Ideal.span {s} : Ideal R) : FractionalIdeal R⁰ K)) ?_ ?_
        · rw [FractionalIdeal.coeIdeal_ne_zero]
          simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hs0
        · exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr
            ((Submodule.span_singleton_le_iff_mem s J).mpr hsJ)
      have hzero : count K w ((v.asIdeal : FractionalIdeal R⁰ K) ^ m) = 0 := by
        rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime K w (Ne.symm hwv)]
        ring
      have hd' := hcount w
      rw [hzero, zero_add] at hd'
      have h2 : 0 ≤ ord K w (algebraMap R K n) := ord_nonneg w n
      omega
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_ord_nonneg (K := K) hnonneg
  exact ⟨a, s, hsv, ha.symm⟩

end Rigidity.RET
