/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Places

/-!
# Adic valuations along an extension of Dedekind domains

A height one prime of an extension of Dedekind domains lies over a height one prime of the base,
and the two adic valuations are related by a single exponent: the ramification index.  The prime
below appears in the factorisation of an ideal of the base to some exponent, and the prime above
appears in the factorisation of the extended ideal to exactly the ramification index times that
exponent.  Passing to the fields of fractions, the valuation of the base at an element is raised to
the ramification index by the extension.

Because the ramification index is at least one, the comparison makes the inclusion of the base
field into the extension uniformly continuous for the two adic topologies, so it extends to the
completions: the completion of the base at a prime maps to the completion of the extension at any
prime above it.

## Main definitions

* `InverseGalois.CFT.ramIdx`: **the ramification index of a height one prime of the extension**
  over the prime below it.
* `InverseGalois.CFT.adicCompletionComap`: **the induced map on completions**, from the completion
  of the base field at the prime below to the completion of the extension at the prime above.

## Main results

* `InverseGalois.CFT.intValuation_algebraMap`: **the adic valuation of an element of the base at a
  prime above** is the valuation at the prime below, raised to the ramification index.
* `InverseGalois.CFT.valuation_algebraMap`: **the same for an element of the base field.**
* `InverseGalois.CFT.adicCompletionComap_coe`: the induced map on completions extends the inclusion
  of the base field.

## Tags

Dedekind domain, height one prime, adic valuation, ramification index, completion
-/

namespace InverseGalois.CFT

open IsDedekindDomain UniqueFactorizationMonoid WithZero

/-! ### The ramification index of a prime of the extension -/

section RamificationIdx

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]

variable (A) in
/-- **The ramification index of a height one prime of the extension** over the prime of the base
below it. -/
noncomputable def ramIdx (w : HeightOneSpectrum B) : ℕ :=
  Ideal.ramificationIdx (algebraMap A B) (primeUnder A w).asIdeal w.asIdeal

/-- Extending the prime below to the extension does not produce the zero ideal. -/
theorem map_primeUnder_ne_bot (w : HeightOneSpectrum B) :
    Ideal.map (algebraMap A B) (primeUnder A w).asIdeal ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot (primeUnder A w).ne_bot

omit [Module.IsTorsionFree A B] in
/-- The prime below extends into the prime above. -/
theorem map_primeUnder_le (w : HeightOneSpectrum B) :
    Ideal.map (algebraMap A B) (primeUnder A w).asIdeal ≤ w.asIdeal := by
  rw [primeUnder_asIdeal, Ideal.under_def]
  exact Ideal.map_comap_le

theorem ramIdx_ne_zero (w : HeightOneSpectrum B) : ramIdx A w ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx_ne_zero (map_primeUnder_ne_bot w) w.isPrime
    (map_primeUnder_le w)

omit [Module.IsTorsionFree A B] in
/-- The prime above divides the extended prime below to the power of the ramification index. -/
theorem pow_ramIdx_dvd_map (w : HeightOneSpectrum B) :
    w.asIdeal ^ ramIdx A w ∣ Ideal.map (algebraMap A B) (primeUnder A w).asIdeal :=
  Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx

/-- The ramification index is the exact exponent: one more power of the prime above no longer
divides the extended prime below. -/
theorem not_pow_succ_ramIdx_dvd_map (w : HeightOneSpectrum B) :
    ¬ w.asIdeal ^ (ramIdx A w + 1) ∣ Ideal.map (algebraMap A B) (primeUnder A w).asIdeal := by
  classical
  have hP0 : w.asIdeal ≠ ⊥ := w.ne_bot
  have hPirr := (Ideal.prime_of_isPrime hP0 w.isPrime).irreducible
  rw [ramIdx, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (map_primeUnder_ne_bot w) w.isPrime hP0,
    dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0)
      (map_primeUnder_ne_bot w),
    normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
    Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]
  exact (Nat.lt_succ_self _).not_ge

/-- **The factorisation of the extended prime below**: the prime above to the ramification index,
times an ideal that the prime above no longer divides. -/
theorem exists_map_primeUnder_eq (w : HeightOneSpectrum B) :
    ∃ J : Ideal B, Ideal.map (algebraMap A B) (primeUnder A w).asIdeal
      = w.asIdeal ^ ramIdx A w * J ∧ ¬ w.asIdeal ∣ J := by
  obtain ⟨J, hJ⟩ := pow_ramIdx_dvd_map (A := A) w
  refine ⟨J, hJ, fun hdvd => not_pow_succ_ramIdx_dvd_map (A := A) w ?_⟩
  rw [hJ, pow_succ]
  exact mul_dvd_mul_left _ hdvd

end RamificationIdx

/-! ### Reading the adic valuation off the factorisation -/

section IntValuation

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R)

/-- The adic valuation of a nonzero element is an integral power of the uniformiser. -/
theorem exists_intValuation_eq_exp {r : R} (hr : r ≠ 0) :
    ∃ n : ℕ, v.intValuation r = exp (-(n : ℤ)) := by
  classical
  exact ⟨_, v.intValuation_if_neg hr⟩

/-- **The adic valuation of a nonzero element is pinned by the exact power of the prime dividing
it.** -/
theorem intValuation_eq_exp_iff {r : R} (hr : r ≠ 0) (n : ℕ) :
    v.intValuation r = exp (-(n : ℤ)) ↔
      v.asIdeal ^ n ∣ Ideal.span {r} ∧ ¬ v.asIdeal ^ (n + 1) ∣ Ideal.span {r} := by
  constructor
  · intro h
    refine ⟨(v.intValuation_le_pow_iff_dvd r n).mp h.le, fun hdvd => ?_⟩
    have hx := (v.intValuation_le_pow_iff_dvd r (n + 1)).mpr hdvd
    rw [h, exp_le_exp] at hx
    push_cast at hx
    omega
  · rintro ⟨h1, h2⟩
    obtain ⟨m, hm⟩ := exists_intValuation_eq_exp v hr
    have hle : v.intValuation r ≤ exp (-(n : ℤ)) := (v.intValuation_le_pow_iff_dvd r n).mpr h1
    have hnle : ¬ v.intValuation r ≤ exp (-((n + 1 : ℕ) : ℤ)) := fun hx =>
      h2 ((v.intValuation_le_pow_iff_dvd r (n + 1)).mp hx)
    rw [hm, exp_le_exp] at hle hnle
    push_cast at hle hnle
    rw [hm]
    congr 1
    omega

end IntValuation

/-! ### The comparison of the two adic valuations -/

section Comparison

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]

/-- **The adic valuation of an element of the base at a prime of the extension** is its valuation
at the prime below, raised to the ramification index. -/
theorem intValuation_algebraMap (w : HeightOneSpectrum B) (a : A) :
    w.intValuation (algebraMap A B a) = (primeUnder A w).intValuation a ^ ramIdx A w := by
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, Valuation.map_zero, Valuation.map_zero, zero_pow (ramIdx_ne_zero (A := A) w)]
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hfa : algebraMap A B a ≠ 0 := fun h => ha (hinj (by rwa [map_zero]))
  obtain ⟨n, hn⟩ := exists_intValuation_eq_exp (primeUnder A w) ha
  obtain ⟨h1, h2⟩ := (intValuation_eq_exp_iff (primeUnder A w) ha n).mp hn
  obtain ⟨I, hI⟩ := h1
  have hIv : ¬ (primeUnder A w).asIdeal ∣ I := fun hd =>
    h2 (by rw [hI, pow_succ]; exact mul_dvd_mul_left _ hd)
  obtain ⟨J, hJ, hJw⟩ := exists_map_primeUnder_eq (A := A) w
  have hmapspan : Ideal.map (algebraMap A B) (Ideal.span {a}) = Ideal.span {algebraMap A B a} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hspan : Ideal.span {algebraMap A B a}
      = w.asIdeal ^ (ramIdx A w * n) * (J ^ n * Ideal.map (algebraMap A B) I) := by
    rw [← hmapspan, hI, Ideal.map_mul, Ideal.map_pow, hJ, mul_pow, ← pow_mul]
    ring
  have hprime : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hwJ : ¬ w.asIdeal ∣ J ^ n * Ideal.map (algebraMap A B) I := by
    intro hd
    rcases hprime.dvd_mul.mp hd with h | h
    · exact hJw (hprime.dvd_of_dvd_pow h)
    · refine hIv (Ideal.dvd_iff_le.mpr ?_)
      rw [primeUnder_asIdeal, Ideal.under_def]
      exact le_trans Ideal.le_comap_map (Ideal.comap_mono (Ideal.le_of_dvd h))
  have key : w.intValuation (algebraMap A B a) = exp (-((ramIdx A w * n : ℕ) : ℤ)) := by
    rw [intValuation_eq_exp_iff w hfa]
    refine ⟨⟨_, hspan⟩, fun hd => hwJ ?_⟩
    rw [hspan, pow_succ] at hd
    exact (mul_dvd_mul_iff_left
      (pow_ne_zero (ramIdx A w * n) (by simpa [Ideal.zero_eq_bot] using w.ne_bot))).mp hd
  rw [key, hn, ← exp_nsmul]
  congr 1
  push_cast [nsmul_eq_mul]
  ring

end Comparison

/-! ### The comparison on the fields of fractions -/

section Fraction

variable {A B k K : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
  [Field k] [Field K] [Algebra A k] [IsFractionRing A k] [Algebra B K] [IsFractionRing B K]
  [Algebra k K] [Algebra A K] [IsScalarTower A B K] [IsScalarTower A k K]

omit [IsDedekindDomain A] [IsDedekindDomain B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
  [IsFractionRing A k] [IsFractionRing B K] in
/-- The two ways of getting from the base domain into the extension field agree. -/
theorem algebraMap_comm (a : A) :
    algebraMap k K (algebraMap A k a) = algebraMap B K (algebraMap A B a) := by
  rw [← IsScalarTower.algebraMap_apply A k K, IsScalarTower.algebraMap_apply A B K]

/-- **The adic valuation of an element of the base field at a prime of the extension** is its
valuation at the prime below, raised to the ramification index. -/
theorem valuation_algebraMap (w : HeightOneSpectrum B) (x : k) :
    w.valuation K (algebraMap k K x) = (primeUnder A w).valuation k x ^ ramIdx A w := by
  obtain ⟨a, s, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  rw [map_div₀, algebraMap_comm (B := B) (K := K) a, algebraMap_comm (B := B) (K := K) s,
    map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_algebraMap, intValuation_algebraMap,
    div_pow]

end Fraction

/-! ### The induced map on the completions -/

section Completion

variable {A B k K : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
  [Field k] [Field K] [Algebra A k] [IsFractionRing A k] [Algebra B K] [IsFractionRing B K]
  [Algebra k K] [Algebra A K] [IsScalarTower A B K] [IsScalarTower A k K]

/-- A power of an element at most one is at most that element. -/
theorem pow_le_self_of_le_one {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] {t : Γ} (ht : t ≤ 1)
    {e : ℕ} (he : e ≠ 0) : t ^ e ≤ t := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  rw [pow_succ, mul_comm]
  exact mul_le_of_le_one_right' (pow_le_one' ht d)

/-- Small elements of the base field stay small in the extension. -/
theorem valuation_algebraMap_lt (w : HeightOneSpectrum B) {γ : ℤᵐ⁰} (hγ : γ ≤ 1) {x : k}
    (hx : (primeUnder A w).valuation k x < γ) :
    w.valuation K (algebraMap k K x) < γ := by
  rw [valuation_algebraMap (A := A)]
  exact lt_of_le_of_lt
    (pow_le_self_of_le_one (le_trans hx.le hγ) (ramIdx_ne_zero (A := A) w)) hx

variable (A) in
/-- The inclusion of the base field into the extension, as a map of valued fields. -/
def withValComap (w : HeightOneSpectrum B) :
    WithVal ((primeUnder A w).valuation k) →+* WithVal (w.valuation K) :=
  algebraMap k K

omit [Module.IsTorsionFree A B] [Algebra A K] [IsScalarTower A B K] [IsScalarTower A k K] in
@[simp]
theorem withValComap_apply (w : HeightOneSpectrum B) (x : k) :
    withValComap A w (K := K) x = algebraMap k K x := rfl

variable (A) in
/-- **The inclusion of the base field into the extension is continuous** for the two adic
topologies: the ramification index is at least one, so small elements stay small. -/
theorem continuous_withValComap (w : HeightOneSpectrum B) :
    Continuous (withValComap A w : WithVal ((primeUnder A w).valuation k) → WithVal
      (w.valuation K)) := by
  refine continuous_of_continuousAt_zero (withValComap A w (K := K)) ?_
  rw [ContinuousAt, map_zero]
  refine (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff.mpr fun γ _ => ?_
  rcases le_or_gt ((γ : ℤᵐ⁰)) 1 with hγ | hγ
  · filter_upwards [(Valued.hasBasis_nhds_zero
      (WithVal ((primeUnder A w).valuation k)) ℤᵐ⁰).mem_of_mem (i := γ) trivial] with x hx
    exact valuation_algebraMap_lt (A := A) w hγ hx
  · filter_upwards [(Valued.hasBasis_nhds_zero
      (WithVal ((primeUnder A w).valuation k)) ℤᵐ⁰).mem_of_mem (i := 1) trivial] with x hx
    exact lt_trans (valuation_algebraMap_lt (A := A) w le_rfl hx) hγ

variable (A) in
/-- **The map induced on the completions** by the inclusion of the base field into the extension:
the completion of the base at the prime below maps to the completion of the extension at the prime
above. -/
noncomputable def adicCompletionComap (w : HeightOneSpectrum B) :
    (primeUnder A w).adicCompletion k →+* w.adicCompletion K :=
  UniformSpace.Completion.mapRingHom (withValComap A w) (continuous_withValComap A w)

variable (A) in
/-- The map induced on the completions extends the inclusion of the base field. -/
theorem adicCompletionComap_coe (w : HeightOneSpectrum B) (x : k) :
    adicCompletionComap A w ((x : (primeUnder A w).adicCompletion k))
      = ((algebraMap k K x : WithVal (w.valuation K)) : w.adicCompletion K) :=
  UniformSpace.Completion.mapRingHom_coe (continuous_withValComap A w) x

variable (A) in
/-- **The map induced on the completions is continuous**, being the extension by continuity of a
continuous map. -/
theorem continuous_adicCompletionComap (w : HeightOneSpectrum B) :
    Continuous (adicCompletionComap A w (k := k) (K := K)) :=
  UniformSpace.Completion.continuous_map

variable (A) in
/-- The map induced on the completions is injective, the completion of the base being a field. -/
theorem adicCompletionComap_injective (w : HeightOneSpectrum B) :
    Function.Injective (adicCompletionComap A w (k := k) (K := K)) :=
  (adicCompletionComap A w (k := k) (K := K)).injective

end Completion

end InverseGalois.CFT
