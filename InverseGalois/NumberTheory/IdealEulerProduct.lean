/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.IdealNormCount

/-!
# The Euler product of the Dedekind zeta function over the prime ideals

Let `K` be a number field with ring of integers `𝓞 K`. In the half-plane `1 < s.re` the Dedekind
zeta function `ζ_K` is the absolutely convergent series `∑_I (N I) ^ (-s)`, the sum being taken
over all nonzero integral ideals of `𝓞 K`. Unique factorisation of ideals into prime ideals turns
this series into a product of geometric series, one for each prime ideal, and each such geometric
series sums to the local factor `(1 - (N 𝔭) ^ (-s))⁻¹`.

## Main results

* `IdealEulerProduct.summable_norm_cpow_absNorm`: the family `I ↦ (N I) ^ (-s)`, indexed by the
  integral ideals of `𝓞 K`, is absolutely summable for `1 < s.re`.
* `IdealEulerProduct.tsum_cpow_absNorm`: its sum is `ζ_K (s)`.
* `IdealEulerProduct.tsum_local_geometric`: the local series `∑_e (N 𝔭 ^ e) ^ (-s)` sums to
  `(1 - (N 𝔭) ^ (-s))⁻¹`.
* `IdealEulerProduct.hasProd_dedekindZeta`: the product of the local factors over all prime
  ideals converges to `ζ_K (s)`.
* `dedekindZeta_eulerProduct_primeIdeal`: the resulting identity
  `∏_𝔭 (1 - (N 𝔭) ^ (-s))⁻¹ = ζ_K (s)`.
-/

open NumberField Ideal IsDedekindDomain

namespace IdealEulerProduct

variable {K : Type*} [Field K] [NumberField K]

/-! ### The summand attached to an integral ideal -/

/-- **The summand attached to the zero ideal vanishes.** -/
theorem cpow_absNorm_bot {s : ℂ} (hs : s ≠ 0) :
    ((absNorm (⊥ : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 0 := by
  rw [absNorm_bot, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.2 hs)]

/-- **The summand is multiplicative.** -/
theorem cpow_absNorm_mul (s : ℂ) (I J : Ideal (𝓞 K)) :
    ((absNorm (I * J) : ℕ) : ℂ) ^ (-s)
      = ((absNorm I : ℕ) : ℂ) ^ (-s) * ((absNorm J : ℕ) : ℂ) ^ (-s) := by
  rw [map_mul, Nat.cast_mul]
  simpa only [Complex.ofReal_natCast] using
    Complex.mul_cpow_ofReal_nonneg (absNorm I).cast_nonneg (absNorm J).cast_nonneg (-s)

/-- **The counted summand is the term of the Dedekind zeta series.** -/
theorem card_mul_norm_cpow {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) * ‖((n : ℕ) : ℂ) ^ (-s)‖
      = ‖LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.2 hs)]
    simp
  · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast, Complex.cpow_neg, norm_inv,
      div_eq_mul_inv]

/-- **There are only finitely many integral ideals of a given norm.** -/
theorem finite_absNorm_eq (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} :=
  Set.Finite.to_subtype (Ideal.finite_setOf_absNorm_eq n)

/-- **The family of summands attached to the ideals of a fixed norm is summable.** -/
theorem summable_fiber (s : ℂ) (n : ℕ) :
    Summable fun I : {I : Ideal (𝓞 K) // absNorm I = n} ↦
      ‖((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)‖ :=
  have := finite_absNorm_eq (K := K) n
  Summable.of_finite

/-- **Summing the summands over the ideals of a fixed norm multiplies by their number.** -/
theorem tsum_fiber (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, ‖((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)‖)
      = (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) * ‖((n : ℕ) : ℂ) ^ (-s)‖ := by
  rw [tsum_congr (fun I ↦ by rw [I.2]), tsum_const, nsmul_eq_mul]

/-- **Summing the summands over the ideals of a fixed norm, as complex numbers.** -/
theorem tsum_fiber_complex (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, ((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      = (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ) * ((n : ℕ) : ℂ) ^ (-s) := by
  rw [tsum_congr (fun I ↦ by rw [I.2]), tsum_const, nsmul_eq_mul]

/-- **The term of the Dedekind zeta series, written with a negative exponent.** -/
theorem term_eq_card_mul_cpow {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s n
      = (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ) * ((n : ℕ) : ℂ) ^ (-s) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.2 hs), mul_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-- **The Dedekind zeta series converges absolutely as a series indexed by integral ideals.** -/
theorem summable_norm_cpow_absNorm {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) ↦ ‖((absNorm I : ℕ) : ℂ) ^ (-s)‖ := by
  have hs0 : s ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  rw [← (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 K))).summable_iff,
    show (fun I : Ideal (𝓞 K) ↦ ‖((absNorm I : ℕ) : ℂ) ^ (-s)‖) ∘
        (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 K)))
      = fun p : Σ n : ℕ, {I : Ideal (𝓞 K) // absNorm I = n} ↦
          ‖((absNorm (p.2 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)‖ from rfl,
    summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)]
  refine ⟨fun n ↦ summable_fiber s n, ?_⟩
  refine ((IdealNormCount.summable_norm_term_card_absNorm (K := K) hs).congr
    fun n ↦ ?_).congr fun n ↦ rfl
  rw [← card_mul_norm_cpow hs0 n, ← tsum_fiber s n]

/-- **The Dedekind zeta series, as a series indexed by integral ideals.** -/
theorem summable_cpow_absNorm {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) ↦ ((absNorm I : ℕ) : ℂ) ^ (-s) :=
  (summable_norm_cpow_absNorm hs).of_norm

/-- **The Dedekind zeta function is the sum of `(N I) ^ (-s)` over the integral ideals.** -/
theorem tsum_cpow_absNorm {s : ℂ} (hs : 1 < s.re) :
    ∑' I : Ideal (𝓞 K), ((absNorm I : ℕ) : ℂ) ^ (-s) = dedekindZeta K s := by
  have hs0 : s ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hsig : Summable fun p : Σ n : ℕ, {I : Ideal (𝓞 K) // absNorm I = n} ↦
      ((absNorm (p.2 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) :=
    (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 K))).summable_iff.2 (summable_cpow_absNorm hs)
  rw [← (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 K))).tsum_eq
      (fun I ↦ ((absNorm I : ℕ) : ℂ) ^ (-s)),
    show (fun p : Σ n : ℕ, {I : Ideal (𝓞 K) // absNorm I = n} ↦
        ((absNorm ((Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 K))) p) : ℕ) : ℂ) ^ (-s))
      = fun p : Σ n : ℕ, {I : Ideal (𝓞 K) // absNorm I = n} ↦
          ((absNorm (p.2 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) from rfl,
    hsig.tsum_sigma, dedekindZeta, LSeries]
  exact tsum_congr fun n ↦ by rw [tsum_fiber_complex s n, term_eq_card_mul_cpow hs0 n]

/-! ### A finite product of local factors -/

/-- **Splitting a finite tuple of exponents into its first entry and the remaining ones.** -/
def consEquivNat (n : ℕ) : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) where
  toFun q := Fin.cons q.1 q.2
  invFun a := (a 0, fun i ↦ a i.succ)
  left_inv q := by simp
  right_inv a := Fin.cons_self_tail a

/-- **A finite product of geometric local factors is a sum over the ideals generated by the
corresponding finite family.** -/
theorem summable_and_hasSum_prod_pow (s : ℂ) :
    ∀ (n : ℕ) (P : Fin n → Ideal (𝓞 K)),
      (∀ i, Summable fun e : ℕ ↦ ‖((absNorm (P i ^ e) : ℕ) : ℂ) ^ (-s)‖) →
      (Summable fun a : Fin n → ℕ ↦ ‖((absNorm (∏ i, P i ^ a i) : ℕ) : ℂ) ^ (-s)‖) ∧
        HasSum (fun a : Fin n → ℕ ↦ ((absNorm (∏ i, P i ^ a i) : ℕ) : ℂ) ^ (-s))
          (∏ i, ∑' e : ℕ, ((absNorm (P i ^ e) : ℕ) : ℂ) ^ (-s)) := by
  intro n
  induction n with
  | zero =>
    intro P _
    have hval : ∀ a : Fin 0 → ℕ, ((absNorm (∏ i, P i ^ a i) : ℕ) : ℂ) ^ (-s) = 1 := by
      intro a
      rw [Finset.univ_eq_empty, Finset.prod_empty, Ideal.one_eq_top, absNorm_top, Nat.cast_one,
        Complex.one_cpow]
    have h1 : HasSum (fun a : Fin 0 → ℕ ↦ ((absNorm (∏ i, P i ^ a i) : ℕ) : ℂ) ^ (-s)) 1 := by
      refine (hval default) ▸ hasSum_single (default : Fin 0 → ℕ) fun b hb ↦ ?_
      exact absurd (Subsingleton.elim b default) hb
    refine ⟨?_, ?_⟩
    · refine Summable.congr (f := fun _ : Fin 0 → ℕ ↦ (1 : ℝ)) ?_ fun a ↦ by rw [hval a, norm_one]
      exact (hasSum_single (default : Fin 0 → ℕ)
        fun b hb ↦ absurd (Subsingleton.elim b default) hb).summable
    · rw [Finset.univ_eq_empty, Finset.prod_empty]
      exact h1
  | succ n ih =>
    intro P hP
    obtain ⟨hsum₀, hhas₀⟩ := ih (fun i ↦ P i.succ) (fun i ↦ hP i.succ)
    have hsum : Summable fun a : Fin n → ℕ ↦
        ‖((absNorm (∏ i, P i.succ ^ a i) : ℕ) : ℂ) ^ (-s)‖ := hsum₀
    have hhas : HasSum (fun a : Fin n → ℕ ↦ ((absNorm (∏ i, P i.succ ^ a i) : ℕ) : ℂ) ^ (-s))
        (∏ i : Fin n, ∑' e : ℕ, ((absNorm (P i.succ ^ e) : ℕ) : ℂ) ^ (-s)) := hhas₀
    have key : ∀ q : ℕ × (Fin n → ℕ),
        ((absNorm (P 0 ^ q.1) : ℕ) : ℂ) ^ (-s)
            * ((absNorm (∏ i : Fin n, P i.succ ^ q.2 i) : ℕ) : ℂ) ^ (-s)
          = ((absNorm (∏ i, P i ^ consEquivNat n q i) : ℕ) : ℂ) ^ (-s) := by
      intro q
      show _ = ((absNorm (∏ i, P i ^ (Fin.cons q.1 q.2 : Fin (n + 1) → ℕ) i) : ℕ) : ℂ) ^ (-s)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact (cpow_absNorm_mul s _ _).symm
    have hcomp : ((fun a : Fin (n + 1) → ℕ ↦ ((absNorm (∏ i, P i ^ a i) : ℕ) : ℂ) ^ (-s)) ∘
          consEquivNat n)
        = fun q : ℕ × (Fin n → ℕ) ↦ ((absNorm (P 0 ^ q.1) : ℕ) : ℂ) ^ (-s)
            * ((absNorm (∏ i : Fin n, P i.succ ^ q.2 i) : ℕ) : ℂ) ^ (-s) :=
      funext fun q ↦ (key q).symm
    have hcompn : ((fun a : Fin (n + 1) → ℕ ↦ ‖((absNorm (∏ i, P i ^ a i) : ℕ) : ℂ) ^ (-s)‖) ∘
          consEquivNat n)
        = fun q : ℕ × (Fin n → ℕ) ↦ ‖((absNorm (P 0 ^ q.1) : ℕ) : ℂ) ^ (-s)‖
            * ‖((absNorm (∏ i : Fin n, P i.succ ^ q.2 i) : ℕ) : ℂ) ^ (-s)‖ :=
      funext fun q ↦ by rw [← norm_mul, key q]; rfl
    have hmulsum : Summable fun q : ℕ × (Fin n → ℕ) ↦
        ‖((absNorm (P 0 ^ q.1) : ℕ) : ℂ) ^ (-s)‖
          * ‖((absNorm (∏ i : Fin n, P i.succ ^ q.2 i) : ℕ) : ℂ) ^ (-s)‖ := by
      apply Summable.mul_of_nonneg (hP 0) hsum <;> exact fun _ ↦ norm_nonneg _
    have hmulhas : HasSum (fun q : ℕ × (Fin n → ℕ) ↦ ((absNorm (P 0 ^ q.1) : ℕ) : ℂ) ^ (-s)
          * ((absNorm (∏ i : Fin n, P i.succ ^ q.2 i) : ℕ) : ℂ) ^ (-s))
        ((∑' e : ℕ, ((absNorm (P 0 ^ e) : ℕ) : ℂ) ^ (-s))
          * ∏ i : Fin n, ∑' e : ℕ, ((absNorm (P i.succ ^ e) : ℕ) : ℂ) ^ (-s)) := by
      apply ((hP 0).of_norm.hasSum).mul hhas
      apply summable_mul_of_summable_norm (hP 0) hsum
    refine ⟨(consEquivNat n).summable_iff.mp ?_, (consEquivNat n).hasSum_iff.mp ?_⟩
    · rw [hcompn]
      exact hmulsum
    · rw [Fin.prod_univ_succ, hcomp]
      exact hmulhas

/-! ### The local factor at a prime ideal -/

/-- **The summand is compatible with powers.** -/
theorem cpow_absNorm_pow (s : ℂ) (I : Ideal (𝓞 K)) (e : ℕ) :
    ((absNorm (I ^ e) : ℕ) : ℂ) ^ (-s) = (((absNorm I : ℕ) : ℂ) ^ (-s)) ^ e := by
  induction e with
  | zero => rw [pow_zero, Ideal.one_eq_top, absNorm_top, Nat.cast_one, Complex.one_cpow, pow_zero]
  | succ e ih => rw [pow_succ, cpow_absNorm_mul, ih, pow_succ]

/-- **The summand at a prime ideal has norm less than one in the half-plane of convergence.** -/
theorem norm_cpow_absNorm_lt_one {s : ℂ} (hs : 1 < s.re) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ‖((absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have h1 : 1 < absNorm 𝔭.asIdeal := RingOfIntegers.HeightOneSpectrum.one_lt_absNorm 𝔭
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  refine Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h1) (by linarith)

/-- **The local series at a prime ideal converges absolutely.** -/
theorem summable_norm_local {s : ℂ} (hs : 1 < s.re) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Summable fun e : ℕ ↦ ‖((absNorm (𝔭.asIdeal ^ e) : ℕ) : ℂ) ^ (-s)‖ := by
  simp_rw [cpow_absNorm_pow, norm_pow]
  exact summable_geometric_of_lt_one (norm_nonneg _) (norm_cpow_absNorm_lt_one hs 𝔭)

/-- **The local factor at a prime ideal is the geometric series in `(N 𝔭) ^ (-s)`.** -/
theorem tsum_local_geometric {s : ℂ} (hs : 1 < s.re) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ∑' e : ℕ, ((absNorm (𝔭.asIdeal ^ e) : ℕ) : ℂ) ^ (-s)
      = (1 - ((absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  simp_rw [cpow_absNorm_pow]
  exact tsum_geometric_of_norm_lt_one (norm_cpow_absNorm_lt_one hs 𝔭)

/-! ### Ideals supported on a finite family of primes -/

omit [NumberField K] in
/-- **A product of powers of prime ideals is a nonzero ideal.** -/
theorem prod_pow_ne_zero {ι : Type*} (T : Finset ι) (P : ι → HeightOneSpectrum (𝓞 K))
    (a : ι → ℕ) : (∏ i ∈ T, (P i).asIdeal ^ a i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ ↦
    pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact (P i).ne_bot)

open scoped Classical in
/-- **The multiplicity of a prime ideal in a product of powers of prime ideals.** -/
theorem count_prod_pow {ι : Type*} (T : Finset ι) (P : ι → HeightOneSpectrum (𝓞 K)) (a : ι → ℕ)
    (𝔮 : HeightOneSpectrum (𝓞 K)) :
    (Associates.mk 𝔮.asIdeal).count (Associates.mk (∏ i ∈ T, (P i).asIdeal ^ a i)).factors
      = ∑ i ∈ T, if P i = 𝔮 then a i else 0 := by
  have hq : Irreducible (Associates.mk 𝔮.asIdeal) := 𝔮.associates_irreducible
  induction T using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, Associates.mk_one, Associates.factors_one,
      Associates.count_zero hq]
  | insert i T hi ih =>
    have hne : Associates.mk (P i).asIdeal ≠ 0 :=
      Associates.mk_ne_zero.mpr (by rw [Ideal.zero_eq_bot]; exact (P i).ne_bot)
    have h1 : Associates.mk ((P i).asIdeal ^ a i) ≠ 0 := by
      rw [Associates.mk_pow]; exact pow_ne_zero _ hne
    have h2 : Associates.mk (∏ j ∈ T, (P j).asIdeal ^ a j) ≠ 0 :=
      Associates.mk_ne_zero.mpr (prod_pow_ne_zero T P a)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ← Associates.mk_mul_mk,
      Associates.count_mul h1 h2 hq, ih, Associates.mk_pow, Associates.count_pow hne hq]
    rcases eq_or_ne (P i) 𝔮 with h | h
    · rw [if_pos h, h, Associates.count_self hq, mul_one]
    · rw [if_neg h, Associates.count_eq_zero_of_ne hq (P i).associates_irreducible
        (fun hh ↦ h (HeightOneSpectrum.ext (Associates.mk_injective hh.symm))), mul_zero]

/-- **The ideal with prescribed multiplicities along a finite family of prime ideals.** -/
def prodPow {n : ℕ} (P : Fin n → HeightOneSpectrum (𝓞 K)) (a : Fin n → ℕ) : Ideal (𝓞 K) :=
  ∏ j, (P j).asIdeal ^ a j

/-- **Distinct primes give distinct products of prime powers.** -/
theorem prodPow_injective {n : ℕ} {P : Fin n → HeightOneSpectrum (𝓞 K)}
    (hP : Function.Injective P) : Function.Injective (prodPow P) := by
  classical
  intro a b hab
  funext k
  have ha := count_prod_pow Finset.univ P a (P k)
  have hb := count_prod_pow Finset.univ P b (P k)
  simp only [hP.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true] at ha hb
  have hab' : (∏ j, (P j).asIdeal ^ a j) = ∏ j, (P j).asIdeal ^ b j := hab
  rw [hab'] at ha
  rw [← ha]
  exact hb

/-- **The summands attached to the ideals generated by a family of distinct primes are absolutely
summable.** -/
theorem summable_range_prodPow {s : ℂ} (hs : 1 < s.re) {n : ℕ}
    {P : Fin n → HeightOneSpectrum (𝓞 K)} (hP : Function.Injective P) :
    Summable fun I : Set.range (prodPow P) ↦ ‖((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)‖ := by
  have h1 := (summable_and_hasSum_prod_pow s n (fun j ↦ (P j).asIdeal)
    (fun j ↦ summable_norm_local hs (P j))).1
  rw [← (Equiv.ofInjective _ (prodPow_injective hP)).summable_iff]
  exact h1

/-- **The finite product of the local factors of a family of distinct primes is the sum of the
summands over the ideals generated by that family.** -/
theorem hasSum_range_prodPow {s : ℂ} (hs : 1 < s.re) {n : ℕ}
    {P : Fin n → HeightOneSpectrum (𝓞 K)} (hP : Function.Injective P) :
    HasSum (fun I : Set.range (prodPow P) ↦ ((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (∏ j, ∑' e : ℕ, ((absNorm ((P j).asIdeal ^ e) : ℕ) : ℂ) ^ (-s)) := by
  have h2 := (summable_and_hasSum_prod_pow s n (fun j ↦ (P j).asIdeal)
    (fun j ↦ summable_norm_local hs (P j))).2
  rw [← (Equiv.ofInjective _ (prodPow_injective hP)).hasSum_iff]
  exact h2

/-! ### Approximating the sum over all integral ideals -/

/-- **A nonzero ideal all of whose prime divisors occur in a finite family of distinct primes is
generated by that family.** -/
theorem mem_range_prodPow {n : ℕ} {P : Fin n → HeightOneSpectrum (𝓞 K)}
    (hP : Function.Injective P) {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (hdvd : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.asIdeal ∣ I → ∃ j, P j = 𝔭) :
    I ∈ Set.range (prodPow P) := by
  classical
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ v.maxPowDividing I)
      ⊆ ↑(Finset.image P Finset.univ) := by
    intro v hv
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine hdvd v ?_
    by_contra hd
    have hcount : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 :=
      not_not.1 fun h ↦ hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).1 h)
    have hone : v.maxPowDividing I = 1 := by
      rw [HeightOneSpectrum.maxPowDividing, hcount, pow_zero]
    exact hv hone
  have hI' : I = ∏ j : Fin n, (P j).maxPowDividing I := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub,
      Finset.prod_image fun x _ y _ h ↦ hP h]
  exact ⟨fun j ↦ (Associates.mk (P j).asIdeal).count (Associates.mk I).factors, hI'.symm⟩

/-- **Summing over the ideals generated by a large enough finite family of primes approximates the
sum over all integral ideals.** -/
theorem exists_finset_norm_tsum_sub_lt {s : ℂ} (hs : 1 < s.re) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ (n : ℕ) (P : Fin n → HeightOneSpectrum (𝓞 K)),
      Function.Injective P → (∀ 𝔭 ∈ S₀, ∃ j, P j = 𝔭) →
        ‖(∑' I : Ideal (𝓞 K), ((absNorm I : ℕ) : ℂ) ^ (-s))
          - ∑' I : Set.range (prodPow P), ((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)‖ < ε := by
  classical
  have hs0 : s ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hbot : ((absNorm (0 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 0 := by
    rw [Ideal.zero_eq_bot]; exact cpow_absNorm_bot hs0
  obtain ⟨T, hT⟩ :=
    (summable_cpow_absNorm (K := K) hs).tsum_vanishing (Metric.ball_mem_nhds 0 hε)
  simp_rw [mem_ball_zero_iff] at hT
  have hbig : (⋃ I ∈ (T : Set (Ideal (𝓞 K))),
      {v : HeightOneSpectrum (𝓞 K) | I ≠ 0 ∧ v.asIdeal ∣ I}).Finite := by
    refine Set.Finite.biUnion T.finite_toSet fun I _ ↦ ?_
    rcases eq_or_ne I 0 with rfl | hI0
    · simp
    · exact (Ideal.finite_factors hI0).subset fun v hv ↦ hv.2
  have hDfin : {v : HeightOneSpectrum (𝓞 K) | ∃ I ∈ T, I ≠ 0 ∧ v.asIdeal ∣ I}.Finite := by
    refine hbig.subset fun v hv ↦ ?_
    obtain ⟨I, hIT, hI0, hdvd⟩ := hv
    exact Set.mem_biUnion hIT ⟨hI0, hdvd⟩
  refine ⟨hDfin.toFinset, fun n P hP hsub ↦ ?_⟩
  have hdisj : Disjoint ((Set.range (prodPow P))ᶜ \ {0}) (T : Set (Ideal (𝓞 K))) := by
    refine Set.disjoint_left.mpr fun I hI hIT ↦ hI.1 ?_
    refine mem_range_prodPow hP hI.2 fun 𝔭 hdvd ↦ hsub 𝔭 ?_
    exact hDfin.mem_toFinset.mpr ⟨I, hIT, hI.2, hdvd⟩
  have hkey := hT _ hdisj
  rwa [← (summable_cpow_absNorm hs).tsum_subtype_add_tsum_subtype_compl (Set.range (prodPow P)),
    add_sub_cancel_left, tsum_eq_tsum_diff_singleton
      (f := fun I : Ideal (𝓞 K) ↦ ((absNorm I : ℕ) : ℂ) ^ (-s)) (Set.range (prodPow P))ᶜ hbot]

/-! ### The Euler product -/

omit [NumberField K] in
/-- **A product over a finite set of primes, read along an enumeration of that set.** -/
theorem prod_eq_prod_fin {M : Type*} [CommMonoid M] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (F : HeightOneSpectrum (𝓞 K) → M) :
    ∏ j : Fin S.card, F (S.equivFin.symm j) = ∏ 𝔭 ∈ S, F 𝔭 := by
  rw [← Finset.prod_coe_sort S F]
  exact (Fintype.prod_equiv S.equivFin _ _ fun i ↦ by simp).symm

/-- **The product of the local series over all prime ideals converges to the sum of the summands
over all integral ideals.** -/
theorem hasProd_tsum_local {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
        ∑' e : ℕ, ((absNorm (𝔭.asIdeal ^ e) : ℕ) : ℂ) ^ (-s))
      (∑' I : Ideal (𝓞 K), ((absNorm I : ℕ) : ℂ) ^ (-s)) := by
  classical
  rw [HasProd, SummationFilter.unconditional_filter]
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨S₀, hS₀⟩ := exists_finset_norm_tsum_sub_lt (K := K) hs hε
  refine ⟨S₀, fun S hS ↦ ?_⟩
  obtain ⟨P, hPinj, hPmem, hPprod⟩ : ∃ P : Fin S.card → HeightOneSpectrum (𝓞 K),
      Function.Injective P ∧ (∀ 𝔭 ∈ S₀, ∃ j, P j = 𝔭) ∧
        ∏ 𝔭 ∈ S, (∑' e : ℕ, ((absNorm (𝔭.asIdeal ^ e) : ℕ) : ℂ) ^ (-s))
          = ∏ j, ∑' e : ℕ, ((absNorm ((P j).asIdeal ^ e) : ℕ) : ℂ) ^ (-s) :=
    ⟨fun j ↦ (S.equivFin.symm j : HeightOneSpectrum (𝓞 K)),
      fun i j h ↦ S.equivFin.symm.injective (Subtype.coe_injective h),
      fun 𝔭 h𝔭 ↦ ⟨S.equivFin ⟨𝔭, Finset.mem_of_subset hS h𝔭⟩, by simp⟩,
      (prod_eq_prod_fin S _).symm⟩
  rw [dist_eq_norm, hPprod, ← (hasSum_range_prodPow hs hPinj).tsum_eq, norm_sub_rev]
  exact hS₀ S.card P hPinj hPmem

/-- **The Euler product of the Dedekind zeta function over the prime ideals.** -/
theorem hasProd_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (1 - ((absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (dedekindZeta K s) := by
  have h := hasProd_tsum_local (K := K) hs
  rw [tsum_cpow_absNorm hs] at h
  simpa only [tsum_local_geometric hs] using h

end IdealEulerProduct

/-- **The Dedekind zeta function of a number field is the product of the local factors
`(1 - (N 𝔭) ^ (-s))⁻¹` over the prime ideals of its ring of integers.** -/
theorem dedekindZeta_eulerProduct_primeIdeal (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    ∏' 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ = NumberField.dedekindZeta K s :=
  (IdealEulerProduct.hasProd_dedekindZeta hs).tprod_eq
